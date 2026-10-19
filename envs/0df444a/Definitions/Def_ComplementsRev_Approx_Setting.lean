-- Prove2me | Definitions.Def_ComplementsRev_Approx_Setting
-- name    : ComplementsRev_Approx_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:15:17.211066+00:00
-- url     : https://prove2.me/theorems/df4eff3f-acbe-45de-a0e3-e113339ee77c
-- title:
--   §2 and §3 — finite-support buyer population and revenue benchmarks
-- statement:
--   A seller has a finite set $M$ of items. A **hyperedge** is a subset $T\subseteq M$ with a nonnegative random weight $w(T)$. The weights have independent, finite-support laws $D'_T$ with mass functions $f_T$, and $C\subseteq 2^M$ is a fixed downward-closed family of feasible bundles containing the empty set. We impose $w(T)=0$ outside $C$ and $w(\varnothing)=0$. The buyer's value for a bundle $S$ is
--
--   $$v_w(S)=\max_{T\subseteq S,\ T\in C}\sum_{U\subseteq T}w(U).$$
--
--   The setting defines the product law of $w$, its expectation and probability, the induced finite type space $V=\{v_w\}$, and **complementarity degree** at most $d$ when each item belongs to at most $d$ hyperedges with $\Pr[w(T)>0]>0$. A mechanism offers a lottery over bundles and a payment to each type in $V$. Truthfulness includes incentive compatibility and individual rationality; its revenue is expected payment.
--
--   **BREV** optimizes $p\Pr[v_w(M)\ge p]$ over real bundle prices $p$. **SREV*** optimizes item-pricing revenue over real price vectors, counting item $i$ only when some bundle containing it has strictly positive utility and every bundle omitting it has nonpositive utility. A fixed injective rank breaks ties among nonempty hyperedges in the favorite region $R_T$. The definition also supplies the paper's SINGLE, NON-FAVORITE, CORE and TAIL benchmarks, the discrete ironed virtual value from the concave revenue curve, and the Partition-Edges procedure of Figure 1.
--
--   These objects are shared by the goal and its intermediate claims. The concave curve is evaluated only at support quantiles; all other revenue and probability expressions are finite weighted sums or suprema over actual price choices.
--
--   **Formalization Note** Individual rationality is explicit because incentive compatibility alone permits arbitrary constant charges. Regions use an arbitrary injective tie rank, covering the paper's lexicographic choice. The ironed virtual value is the slope of the least concave majorant of the finite revenue curve.
-- source:
--   Eden, Feldman, Friedler, Talgam-Cohen & Weinberg, A Simple and Approximately Optimal Mechanism for a Buyer with Complements, arXiv:1612.04746v2, §§2–3, pp. 4–6; Figure 1, p. 9

import Mathlib

namespace ComplementsRev.Approx

open Classical

/-- The fixed feasible sets and independent, finitely supported hyperedge weights of §2. -/
structure Population (ι : Type*) [Fintype ι] [DecidableEq ι] where
  C : Finset (Finset ι)
  C_down : ∀ S ∈ C, ∀ T ⊆ S, T ∈ C
  empty_mem : (∅ : Finset ι) ∈ C
  supp : Finset ι → Finset ℝ
  f : Finset ι → ℝ → ℝ
  supp_nonneg : ∀ T, ∀ y ∈ supp T, 0 ≤ y
  f_pos : ∀ T, ∀ y ∈ supp T, 0 < f T y
  f_zero : ∀ T y, y ∉ supp T → f T y = 0
  f_sum : ∀ T, ∑ y ∈ supp T, f T y = 1
  zero_off_C : ∀ T, T ∉ C → supp T = {0}
  zero_empty : supp ∅ = {0}

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The independent product support, with one coordinate for each potential hyperedge. -/
def Population.profiles (P : Population ι) : Finset (Finset ι → ℝ) :=
  Fintype.piFinset P.supp

/-- Product probability of a hypergraph. -/
def Population.prob (P : Population ι) (w : Finset ι → ℝ) : ℝ :=
  ∏ T : Finset ι, P.f T (w T)

/-- Expectation under the product law. -/
def Population.E (P : Population ι) (g : (Finset ι → ℝ) → ℝ) : ℝ :=
  ∑ w ∈ P.profiles, P.prob w * g w

/-- Probability of an event on hypergraphs. -/
noncomputable def Population.Pr (P : Population ι) (A : (Finset ι → ℝ) → Prop) : ℝ :=
  P.E (fun w => if A w then 1 else 0)

/-- Feasible subsets of a bundle. -/
def feasible (P : Population ι) (S : Finset ι) : Finset (Finset ι) :=
  P.C.filter (fun T => T ⊆ S)

/-- Value of a bundle under the realized hypergraph, §2. -/
def val (P : Population ι) (w : Finset ι → ℝ) (S : Finset ι) : ℝ :=
  (feasible P S).sup' (by
    exact ⟨∅, Finset.mem_filter.mpr ⟨P.empty_mem, Finset.empty_subset S⟩⟩)
    (fun T => ∑ U ∈ T.powerset, w U)

/-- The finite image of the product support in valuation space. -/
noncomputable def Population.V (P : Population ι) : Finset (Finset ι → ℝ) :=
  P.profiles.image (val P)

/-- Population complementarity degree from §2. -/
def HasComplementarity (P : Population ι) (d : ℕ) : Prop :=
  ∀ i : ι, (Finset.univ.filter (fun T : Finset ι => i ∈ T ∧ P.f T 0 < 1)).card ≤ d

/-- Lottery mechanism on the valuation type space. -/
structure Mech (ι : Type*) where
  X : (Finset ι → ℝ) → Finset ι → ℝ
  p : (Finset ι → ℝ) → ℝ

/-- Utility of true type `v` when reporting `r`. -/
def util (v : Finset ι → ℝ) (m : Mech ι) (r : Finset ι → ℝ) : ℝ :=
  (∑ S : Finset ι, m.X r S * v S) - m.p r

/-- Lottery validity, incentive compatibility, and individual rationality on V. -/
def IsTruthful (P : Population ι) (m : Mech ι) : Prop :=
  (∀ v ∈ P.V, (∀ S : Finset ι, 0 ≤ m.X v S) ∧
    (∑ S : Finset ι, m.X v S) = 1) ∧
  (∀ v ∈ P.V, ∀ r ∈ P.V, util v m r ≤ util v m v) ∧
  (∀ v ∈ P.V, 0 ≤ util v m v)

/-- Expected payment under the original population. -/
def revenue (P : Population ι) (m : Mech ι) : ℝ :=
  P.E (fun w => m.p (val P w))

/-- Revenue from selling the whole item set at one real price. -/
noncomputable def BREV (P : Population ι) : ℝ :=
  sSup (Set.range (fun p : ℝ => p * P.Pr (fun w => p ≤ val P w Finset.univ)))

/-- The paper's conservative indicator that item i is sold at posted prices p. -/
noncomputable def Psold (v : Finset ι → ℝ) (p : ι → ℝ) (i : ι) : ℝ :=
  if (∃ S : Finset ι, i ∈ S ∧ 0 < v S - ∑ j ∈ S, p j) ∧
      (∀ S : Finset ι, i ∉ S → v S - ∑ j ∈ S, p j ≤ 0) then 1 else 0

/-- Conservative separate-sale revenue, optimized over all real item prices. -/
noncomputable def SREVstar (P : Population ι) : ℝ :=
  sSup (Set.range (fun p : ι → ℝ => P.E (fun w =>
    ∑ i : ι, Psold (val P w) p i * p i)))

/-- Membership in the most valuable nonempty hyperedge region, with rank breaking ties. -/
def InRegion (rk : Finset ι → ℕ) (w : Finset ι → ℝ) (A : Finset ι) : Prop :=
  A.Nonempty ∧ ∀ T : Finset ι, T.Nonempty → T ≠ A →
    (w T < w A ∨ (w T = w A ∧ rk A < rk T))

/-- Upper-tail probability of a hyperedge's finite law. -/
noncomputable def Population.qtl (P : Population ι) (T : Finset ι) (y : ℝ) : ℝ :=
  ∑ z ∈ (P.supp T).filter (fun z => y ≤ z), P.f T z

/-- The discrete revenue curve's points are (0,0) and (qtl y, y*qtl y).
The least concave majorant at q is the best convex combination of these points. -/
noncomputable def Population.concaveRevenue (P : Population ι) (T : Finset ι) (q : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ a : Option ℝ → ℝ,
    (∀ y : Option ℝ, 0 ≤ a y) ∧
    a none + (∑ y ∈ P.supp T, a (some y)) = 1 ∧
    (∑ y ∈ P.supp T, a (some y) * P.qtl T y) = q ∧
    r = ∑ y ∈ P.supp T, a (some y) * (y * P.qtl T y)}

/-- Myerson's ironed virtual value: the slope of the concave revenue curve
on the mass interval belonging to y. Used only for y in the support. -/
noncomputable def Population.phibar (P : Population ι) (T : Finset ι) (y : ℝ) : ℝ :=
  (P.concaveRevenue T (P.qtl T y) -
    P.concaveRevenue T (P.qtl T y - P.f T y)) / P.f T y

/-- The SINGLE benchmark in Corollary 3.1. -/
noncomputable def SINGLE (P : Population ι) (rk : Finset ι → ℕ) : ℝ :=
  P.E (fun w => ∑ T : Finset ι,
    (if InRegion rk w T then max 0 (P.phibar T (w T)) else 0))

/-- The NON-FAVORITE benchmark in Corollary 3.1. -/
noncomputable def NONFAV (P : Population ι) (rk : Finset ι → ℕ) : ℝ :=
  P.E (fun w => P.C.sup' ⟨∅, P.empty_mem⟩ (fun S =>
    ∑ T ∈ S.powerset, if InRegion rk w T then 0 else w T))

/-- The CORE benchmark in Lemma 5.1. -/
noncomputable def CORE (P : Population ι) (t : ℝ) : ℝ :=
  P.E (fun w => P.C.sup' ⟨∅, P.empty_mem⟩ (fun S =>
    ∑ T ∈ S.powerset, if w T ≤ t then w T else 0))

/-- The TAIL benchmark in Lemma 5.1. -/
noncomputable def TAIL (P : Population ι) (rk : Finset ι → ℕ) (t : ℝ) : ℝ :=
  P.E (fun w => ∑ T : Finset ι,
    if t < w T ∧ ¬ InRegion rk w T then w T else 0)

/-- Sweep one stage of Figure 1 in the supplied processing order. -/
def sweep (order : List (Finset ι)) (E : Finset (Finset ι)) : Finset (Finset ι) :=
  order.foldl (fun F T =>
    if T ∈ F ∧ T ⊆ (F.erase T).biUnion id then F.erase T else F) E

/-- Figure 1 with explicit loop fuel and a separate order for each round. -/
def partitionEdges (σ : ℕ → Finset (Finset ι) → List (Finset ι)) :
    ℕ → ℕ → Finset (Finset ι) → List (Finset (Finset ι))
  | _, 0, _ => []
  | round, fuel + 1, E =>
      if E = ∅ then [] else
        let H := sweep (σ round E) E
        H :: partitionEdges σ (round + 1) fuel (E \ H)

end ComplementsRev.Approx


