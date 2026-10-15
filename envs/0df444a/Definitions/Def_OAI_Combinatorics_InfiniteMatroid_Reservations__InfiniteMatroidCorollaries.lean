-- Prove2me | Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Reservations__InfiniteMatroidCorollaries
-- name    : OAI_Combinatorics_InfiniteMatroid_Reservations__InfiniteMatroidCorollaries
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T05:42:24.673979+00:00
-- url     : https://prove2.me/theorems/746e2390-eef2-4dff-bcf7-118e1f75c1fe
-- title:
--   Reservation cells: one fresh index meeting fewer than continuum many non-small sets
-- statement:
--   Notation follows the column and density-ideal definitions. $D$ is the set of pairs $(m,g)$ with $m\in\mathbb N$ and $g:\{0,1\}^m\to\{0,1\}$, with blocks $D_m=\{(m,g)\}$; $E_0=D\times\{0,1\}$ has blocks $W_m=D_m\times\{0,1\}$; for $X\subseteq E_0$, $\delta_m(X)=|X\cap W_m|/|W_m|$, and $X$ is *small* if $\delta_m(X)\to0$. The index set $\mathfrak c$ has cardinality $2^{\aleph_0}$. For $t\in\mathfrak c$, $\sigma_{a_t}$ and $\sigma_{b_t}$ are the binary codes of the tags $a_t=(t,0)$ and $b_t=(t,1)$, $\sigma|_m$ denotes the length-$m$ prefix of a binary sequence $\sigma$, and $A_t=\{(m,g)\in D:\ g(\sigma_{a_t}|_m)=1\}$ is the $A$-column of $t$.
--
--   1. **Lift.** For $X\subseteq D$, $\widehat X=X\times\{0,1\}\subseteq E_0$. Its block densities are those of $X$: $\delta_m(\widehat X)=|X\cap D_m|/|D_m|$.
--   2. **Reservation cells.** For $t\in\mathfrak c$ and $k\in\{0,1\}$,
--   $$C_{t,k}=\bigl\{(m,g)\in D:\ g(\sigma_{a_t}|_m)=0\ \text{and}\ g(\sigma_{b_t}|_m)=k\bigr\},\qquad H_{t,k}=\widehat{C_{t,k}}\subseteq E_0 .$$
--   Thus $C_{t,k}\subseteq D\setminus A_t$, and the two cells $H_{t,0}$ and $H_{t,1}$ are disjoint.
--   3. **Avoidance sets.** For a finite set $F\subseteq\mathfrak c$ and a choice $k:F\to\{0,1\}$,
--   $$\mathrm{Av}(F,k)=\{x\in D:\ x\notin C_{t,k(t)}\ \text{for all}\ t\in F\}.$$
--
--   The file proves the following facts.
--
--   - *Counting.* For a finite type $A$ and $k:A\to\{0,1\}$, exactly $3^{|A|}$ maps $v:A\times\{0,1\}\to\{0,1\}$ satisfy $(v(t,0),v(t,1))\ne(0,k(t))$ for all $t\in A$.
--   - *Avoidance density.* For all sufficiently large $m$, $|\mathrm{Av}(F,k)\cap D_m|/|D_m|=(3/4)^{|F|}$, and likewise $\delta_m\bigl(\{x\in E_0:\ x\notin H_{t,k(t)}\ \text{for all}\ t\in F\}\bigr)=(3/4)^{|F|}$.
--   - *Finite unions.* A finite union of small subsets of $E_0$ is small.
--   - *Few bad indices.* If $S\subseteq E_0$ is not small, then only finitely many $t\in\mathfrak c$ admit some $k\in\{0,1\}$ for which $S\cap H_{t,k}$ is small.
--   - *Simultaneous reservations.* Let $(S_i)_{i\in\iota}$ be a family of non-small subsets of $E_0$ whose index set has cardinality $|\iota|<2^{\aleph_0}$. Then there is $t\in\mathfrak c$ such that
--
--   $$
--   S_i\cap H_{t,k}\ \text{is not small for every}\ i\in\iota\ \text{and every}\ k\in\{0,1\}.
--   $$
--
--   Simultaneous reservations are used when a new admissible set has to be inserted between two sets $A\subseteq Z$ so that it differs non-negligibly, in both directions, from each of fewer than continuum many earlier sets. A single fresh index $t$ provides two disjoint cells $H_{t,0},H_{t,1}$ that meet every relevant non-small set in a non-small set; enlarging $A$ inside one cell and shrinking $Z$ inside the other forces the required differences. Because the cells lie outside the column $A_t$, they are negligible for the column ideal $\mathcal K$, so these modifications do not change the rank-model status of $A$ and $Z$.
--
--   **Formalization Note** The definitions are `liftD X = Prod.fst ⁻¹' X`, `DCell t k`, `HCell t k = liftD (DCell t k)` and `avoidCells F k` for `F : Finset CIndex` and `k : F → Bool`; the binary codes are `columnString (tagA t)` and `columnString (tagB t)`, and prefixes are taken with `prefixString`. The lemmas are `density_liftD`, `dCell_subset_Acompl`, `hCell_disjoint`, `card_avoid_cells` (a `Nat.card` identity), `eventually_avoidCells`, `eventually_avoidHCells`, `small_biUnion`, `bad_cells_finite` and `simultaneous_reservations`, whose cardinality hypothesis is `Cardinal.mk ι < Cardinal.continuum` for `ι : Type`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/InfiniteMatroid/Reservations.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/InfiniteMatroid/Reservations.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the InfiniteMatroidCorollaries mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Matroid__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_DoubleRay__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Waves
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Cardinality__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Ideals__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_OrdinalRank__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_FiniteCounting__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_BlockDensity__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Columns__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Cesaro__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_ProbeLimits__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_SparsePerturbation__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Interpolation__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_LocalBases__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_DensityIdeal__InfiniteMatroidCorollaries

namespace OAI

section
open Set Filter Finset
open scoped Topology symmDiff
namespace InfiniteMatroidCounterexample

def liftD (X : Set D) : Set E0 := Prod.fst ⁻¹' X

lemma density_liftD (X : Set D) (m : ℕ) : density (liftD X) m = dDensity X m := by
  classical
  have he : traceFinset (wBlock m) (liftD X) = (traceFinset (dBlock m) X).product univ := by
    ext x
    simp [wBlock, liftD]
  rw [density, finiteDensity, he]
  simp [dDensity, finiteDensity, wBlock]
  ring

def DCell (t : CIndex) (k : Bool) : Set D :=
  {x | x.2 (prefixString (columnString (tagA t)) x.1) = false ∧
    x.2 (prefixString (columnString (tagB t)) x.1) = k}
def HCell (t : CIndex) (k : Bool) : Set E0 := liftD (DCell t k)

lemma dCell_subset_Acompl (t : CIndex) (k : Bool) : DCell t k ⊆ (AColumn t)ᶜ := by
  intro x hx ha
  exact Bool.false_ne_true (hx.1.symm.trans ha)

lemma hCell_disjoint (t : CIndex) : Disjoint (HCell t false) (HCell t true) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact Bool.false_ne_true (hx.2.symm.trans hy.2)

lemma card_avoid_cells {A : Type} [Fintype A] (k : A → Bool) :
    Nat.card {v : A × Bool → Bool // ∀ t, ¬ (v (t,false) = false ∧ v (t,true) = k t)} =
      3 ^ Fintype.card A := by
  classical
  let e := ((Equiv.curry A Bool Bool).subtypeEquiv
    (p := fun v ↦ ∀ t, ¬(v (t,false) = false ∧ v (t,true) = k t))
    (q := fun v ↦ ∀ t, ¬(v t false = false ∧ v t true = k t)) (fun _ ↦ Iff.rfl)).trans
      (Equiv.subtypePiEquivPi (α := A) (β := fun _ ↦ Bool → Bool)
        (p := fun t v ↦ ¬(v false = false ∧ v true = k t)))
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_pi]
  have hc (b : Bool) : Fintype.card {v : Bool → Bool // ¬(v false = false ∧ v true = b)} = 3 := by
    cases b <;> decide
  simp only [hc, Finset.prod_const, Finset.card_univ]

def avoidCells (F : Finset CIndex) (k : F → Bool) : Set D :=
  {x | ∀ t : F, x ∉ DCell t (k t)}

lemma eventually_avoidCells (F : Finset CIndex) (k : F → Bool) :
    ∀ᶠ m in atTop, dDensity (avoidCells F k) m = (3/4 : ℝ)^F.card := by
  classical
  let e : F × Bool ↪ ColumnTag := ⟨fun p ↦ if p.2 then tagB p.1 else tagA p.1, by
    rintro ⟨t,b⟩ ⟨s,c⟩ he
    have ht : t = s := by
      apply Subtype.ext
      cases b <;> cases c <;> exact congrArg Prod.fst he
    subst s
    congr 1
    cases b <;> cases c <;> simp_all [tagA,tagB]⟩
  have h := columns_uniform e (fun v ↦ ∀ t : F, ¬(v (t,false) = false ∧ v (t,true) = k t))
  rw [card_avoid_cells] at h
  filter_upwards [h] with m hm
  have he : {x : D | ∀ t : F, ¬(x.2 (prefixString (columnString (e (t,false))) x.1) = false ∧
      x.2 (prefixString (columnString (e (t,true))) x.1) = k t)} = avoidCells F k := rfl
  rw [he] at hm
  rw [hm]
  simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_bool,
    Fintype.card_coe, Nat.cast_pow, Nat.cast_ofNat]
  rw [mul_comm F.card 2, pow_mul, div_pow]
  norm_num

lemma eventually_avoidHCells (F : Finset CIndex) (k : F → Bool) :
    ∀ᶠ m in atTop, density {x | ∀ t : F, x ∉ HCell t (k t)} m = (3/4 : ℝ)^F.card := by
  have h := eventually_avoidCells F k
  filter_upwards [h] with m hm
  change density (liftD (avoidCells F k)) m = _
  rwa [density_liftD]

lemma small_biUnion {ι : Type} (F : Finset ι) (X : ι → Set E0) (hX : ∀ t ∈ F, Small (X t)) :
    Small (⋃ t ∈ F, X t) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using small_empty
  | @insert t F ht ih =>
    simpa only [Finset.mem_insert, iUnion_iUnion_eq_or_left] using
      small_union (hX t (Finset.mem_insert_self _ _))
        (ih (fun s hs ↦ hX s (Finset.mem_insert_of_mem hs)))

lemma bad_cells_finite {S : Set E0} (hS : ¬ Small S) :
    {t | ∃ k : Bool, Small (S ∩ HCell t k)}.Finite := by
  classical
  by_contra hinf
  apply hS
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun m ↦ ha.trans_le (finiteDensity_nonneg _ _)
  · intro ε hε
    have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 3/4)
      (by norm_num : (3/4:ℝ) < 1)).eventually (gt_mem_nhds (half_pos hε))
    obtain ⟨q,hq⟩ := hp.exists
    obtain ⟨F,hF,hFfin,hFcard⟩ := Set.Infinite.exists_subset_ncard_eq hinf q
    let Q := hFfin.toFinset
    have hchoose : ∀ t : Q, ∃ k : Bool, Small (S ∩ HCell t k) := by
      intro t
      exact hF (hFfin.mem_toFinset.mp t.property)
    choose k hk using hchoose
    let N := ⋃ t : Q, S ∩ HCell t (k t)
    have hN : Small N := by
      have := small_biUnion (Finset.univ : Finset Q) (fun t ↦ S ∩ HCell t (k t)) (fun t _ ↦ hk t)
      simpa only [Finset.mem_univ, iUnion_true] using this
    have hsub : S ⊆ N ∪ {x | ∀ t : Q, x ∉ HCell t (k t)} := by
      intro x hx
      by_cases hn : x ∈ N
      · exact Or.inl hn
      · right
        intro t ht
        exact hn (mem_iUnion.mpr ⟨t,hx,ht⟩)
    have hQ : Q.card = q := (Set.ncard_eq_toFinset_card F hFfin).symm.trans hFcard
    filter_upwards [eventually_avoidHCells Q k, hN.eventually (gt_mem_nhds (half_pos hε))] with m hm hn
    have hle := (finiteDensity_mono (wBlock m) hsub).trans
      (finiteDensity_union_le (wBlock m) N {x | ∀ t : Q, x ∉ HCell t (k t)})
    change density S m ≤ density N m + density _ m at hle
    rw [hm, hQ] at hle
    linarith

lemma simultaneous_reservations {ι : Type} (hι : Cardinal.mk ι < Cardinal.continuum)
    (S : ι → Set E0) (hS : ∀ i, ¬ Small (S i)) :
    ∃ t : CIndex, ∀ i k, ¬ Small (S i ∩ HCell t k) := by
  obtain ⟨t,ht⟩ := exists_avoid_finite_family hι
    (fun i ↦ {t | ∃ k : Bool, Small (S i ∩ HCell t k)}) (fun i ↦ bad_cells_finite (hS i))
  exact ⟨t,fun i k h ↦ ht i ⟨k,h⟩⟩

end InfiniteMatroidCounterexample
end

end OAI


