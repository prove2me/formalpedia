-- Prove2me | Definitions.Def_ProphetMatchingEFGT_BatchedModel
-- name    : ProphetMatchingEFGT_BatchedModel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:49:58.406775+00:00
-- url     : https://prove2.me/theorems/5b51872a-c0f9-4e86-8dad-5191ff866111
-- title:
--   §2 — batched arrivals, the optimum $\mathrm{OPT}$, the sampling scheme $R(w,F)$, batched OCRSs and batched prophet algorithms
-- statement:
--   This module sets up the batched framework of §2 (pp. 7–8).
--
--   1. **Ground set and feasibility.** $E$ is a finite set of elements and $\mathcal M$ a family of feasible subsets of $E$; $\mathcal M$ is **downward closed** if $S\in\mathcal M$ and $S'\subseteq S$ imply $S'\in\mathcal M$. For weights $w\in\mathbb R^E$, $w(S)=\sum_{e\in S}w_e$.
--   2. **Ordered partitions.** An ordered partition $(B_1,\dots,B_T)$ of $E$ consists of nonempty, pairwise disjoint batches covering $E$; the batches arrive in this order. A family $\mathcal B$ of such partitions is the structure the adversary chooses from.
--   3. **Weights.** The weight vector $w$ has a law $\mu$ on $\mathbb R^E$. For a partition $(B_t)$, the blocks $w_t=(w_e)_{e\in B_t}$ are **independent across batches** under $\mu$ (the paper's $w\sim F=\prod_t F_t$).
--   4. **The optimum.** $\mathrm{OPT}$ is a deterministic map with $\mathrm{OPT}(w)\in\arg\max_{S\in\mathcal M}w(S)$ whose level sets $\{w:\mathrm{OPT}(w)=S\}$ are measurable. The hybrid vector $(w_t,\tilde w^{(t)})$ equals $w$ on $B_t$ and $\tilde w$ off $B_t$.
--   5. **The sampling scheme $R(w,F)$ (§2.3).** $R_t=B_t\cap\mathrm{OPT}(w_t,\tilde w^{(t)})$ with an independent resample $\tilde w^{(t)}$. Its law on a partition $(B_t)$ is that of independent sets $R_t$, each distributed as $\mathrm{OPT}(w)\cap B_t$: $\Pr[R=r]=\prod_t\mu\{w:\mathrm{OPT}(w)\cap B_t=r\cap B_t\}$.
--   6. **Online rules.** A batched rule has internal randomness $\omega\sim\rho$ (a probability space). At time $t$ it sees the earlier batches with their observations, the batch $B_t$, its observation, and $\omega$, and returns a set. A **batched prophet algorithm** observes the weights $w_t$ and selects $I_t\subseteq B_t$; a **batched OCRS** observes $R_t$ and selects $I_t\subseteq R_t$; in both cases $I=\bigsqcup_tI_t\in\mathcal M$ (Definitions 2.1 and 2.2).
--   7. **Value and selectability.** The value of a prophet algorithm on a partition is $\mathbb E_{w,I}[w(I)]$ with $\omega$ independent of $w$; the benchmark is $\mathbb E_w[w(\mathrm{OPT}(w))]$. An OCRS is **$c$-selectable** for $R(w,F)$ on $\mathcal B$ if for every partition in $\mathcal B$, every $t$, every $S\subseteq B_t$ and every $e\in S$,
--   $$\Pr[e\in I_t,\ R_t=S]\ \ge\ c\cdot\Pr[R_t=S].$$
--
--   These are the objects of Theorem 2.3 and eq. (2).
--
--   **Formalization Note** A rule may return any set; the run keeps the returned set exactly when it lies inside the allowed set ($B_t$ or $R_t$) and keeps the selection in $\mathcal M$, and selects nothing at that step otherwise, so every run is feasible and a rule that always proposes feasible sets runs unchanged. The prophet algorithm sees the batch weights as a vector equal to $w$ on $B_t$ and $0$ off it. Selectability is stated in product form because $\Pr[R_t=S]$ may be $0$. Measurability of a rule (`MeasurableProphet`, `MeasurableOCRS`) is a separate predicate.
-- source:
--   Ezra–Feldman–Gravin–Tang, Online Stochastic Max-Weight Matching: prophet inequality for vertex and edge arrival models, arXiv:2002.09807v2, §2 pp. 7–8 (§2.1, Definition 2.1 eq. (1), §2.2, Definition 2.2, footnotes 3 and 5, §2.3)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace ProphetMatchingEFGT

/-! # The batched model of §2 (Ezra–Feldman–Gravin–Tang, arXiv:2002.09807v2, pp. 7–8)

Ground set `E` (a finite type), a feasible family `M` of subsets, ordered partitions of `E`
into batches, random weights, the deterministic optimum `OPT`, the sampling scheme `R(w, F)` of
§2.3, batched OCRSs (Definition 2.1) and batched prophet algorithms (Definition 2.2).

**Formalization Note.** Weight vectors are functions `E → ℝ` with one joint law `μ`; the paper's
`F = ∏_t F_t` (independence across batches, dependence inside a batch allowed) is the hypothesis
`BlocksIndep μ Bs` for each feasible ordered partition `Bs`. Probabilities of finitely many
outcomes are finite sums of real masses `μ.real`. An online rule may return any set; the run keeps
the returned set exactly when it is inside the allowed set and keeps the selection feasible, and
selects nothing at that step otherwise, so feasibility is built into every run. -/

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- `M` is downward closed: `S ∈ M` and `S' ⊆ S` imply `S' ∈ M` (§2, p. 7). -/
def IsDownwardClosed (M : Set (Finset E)) : Prop :=
  ∀ S ∈ M, ∀ S' ⊆ S, S' ∈ M

/-- An ordered partition `(B₁, …, B_T)` of `E` into nonempty, pairwise disjoint batches whose
union is `E` (§2, p. 7). -/
def IsOrderedPartition (Bs : List (Finset E)) : Prop :=
  (∀ B ∈ Bs, B.Nonempty) ∧ Bs.Pairwise Disjoint ∧ ∀ e : E, ∃ B ∈ Bs, e ∈ B

/-- `w(S) = Σ_{e ∈ S} w_e` (p. 7). -/
def setWeight (w : E → ℝ) (S : Finset E) : ℝ :=
  ∑ e ∈ S, w e

/-- `opt` is a deterministic optimum `OPT(w) ∈ argmax_{S ∈ M} w(S)` (p. 8 and footnote 5), with
measurable level sets so that `Pr[OPT(w) = S]` is defined. -/
structure IsOPT (M : Set (Finset E)) (opt : (E → ℝ) → Finset E) : Prop where
  measurableSet_eq : ∀ S : Finset E, MeasurableSet {w | opt w = S}
  mem : ∀ w, opt w ∈ M
  le : ∀ w, ∀ S ∈ M, setWeight w S ≤ setWeight w (opt w)

/-- The weight vector equal to `w` on the batch `B` and to `w'` off it: the vector
`(w_t, w̃^{(t)})` of §2.3, p. 8, with `B = B_t`. -/
def hybrid (B : Finset E) (w w' : E → ℝ) : E → ℝ :=
  fun e => if e ∈ B then w e else w' e

/-- The weights of the different batches of `Bs` are mutually independent under `μ`
("`w ∼ F = ∏_t F_t`; we allow dependency within batches, but not across batches", p. 7). -/
def BlocksIndep (μ : Measure (E → ℝ)) (Bs : List (Finset E)) : Prop :=
  iIndepFun (fun (t : Fin Bs.length) (w : E → ℝ) (e : {e // e ∈ Bs.get t}) => w e) μ

/-- A randomized online rule for batched arrivals. Its internal randomness is `ω ∈ Ω`, drawn
from the probability measure `ρ`. At each step it receives the history (earlier batches with
their observations, in arrival order), the current batch and its observation, and `ω`, and returns
the set it wants to select. The observation type `Obs` is `E → ℝ` for a prophet algorithm
(the batch's weights) and `Finset E` for an OCRS (the realized set `R_t`). -/
structure BatchedRule (E : Type*) (Obs : Type*) where
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  ρ : Measure Ω
  [isProb : IsProbabilityMeasure ρ]
  choose : List (Finset E × Obs) → Finset E → Obs → Ω → Finset E

attribute [instance] BatchedRule.mΩ BatchedRule.isProb

open Classical in
/-- The run of a batched rule on the batches `Bs` (in this order) with observation `obs B` for
batch `B`: at each step the rule's choice is kept if it lies in `allowed B (obs B)` and keeps the
union in `M`; otherwise nothing is selected at that step. Returns the selected set `I = ⊔_t I_t`. -/
noncomputable def runBatched {Obs : Type*} (A : BatchedRule E Obs) (M : Set (Finset E))
    (allowed : Finset E → Obs → Finset E) (Bs : List (Finset E)) (obs : Finset E → Obs)
    (ω : A.Ω) : Finset E :=
  (Bs.foldl (fun (st : List (Finset E × Obs) × Finset E) B =>
      let J := A.choose st.1 B (obs B) ω
      (st.1 ++ [(B, obs B)], if J ⊆ allowed B (obs B) ∧ st.2 ∪ J ∈ M then st.2 ∪ J else st.2))
    ([], ∅)).2

/-- The weights `w_t = (w_e)_{e ∈ B}` of a batch, as the prophet algorithm observes them: `w`
on `B` and `0` off `B`. -/
def maskWeights (w : E → ℝ) (B : Finset E) : E → ℝ :=
  fun e => if e ∈ B then w e else 0

/-- Measurability of a batched prophet algorithm: for every fixed sequence of past batches and
current batch, the choice is a measurable function of the observed weights and of `ω`. -/
def BatchedRule.MeasurableProphet (A : BatchedRule E (E → ℝ)) : Prop :=
  ∀ (Bs : List (Finset E)) (B : Finset E) (S : Finset E),
    MeasurableSet {p : (Fin Bs.length → E → ℝ) × (E → ℝ) × A.Ω |
      A.choose (List.ofFn fun i => (Bs.get i, p.1 i)) B p.2.1 p.2.2 = S}

/-- Measurability of a batched OCRS: for every history, batch and realized set, the choice is a
measurable function of `ω`. -/
def BatchedRule.MeasurableOCRS (A : BatchedRule E (Finset E)) : Prop :=
  ∀ (h : List (Finset E × Finset E)) (B R S : Finset E), MeasurableSet {ω | A.choose h B R ω = S}

/-- The run of a batched prophet algorithm (Definition 2.2, p. 8): at time `t` it sees `B_t` and
`w_t` and selects `I_t ⊆ B_t` with `⊔_t I_t ∈ M`. -/
noncomputable def prophetRun (A : BatchedRule E (E → ℝ)) (M : Set (Finset E))
    (Bs : List (Finset E)) (w : E → ℝ) (ω : A.Ω) : Finset E :=
  runBatched A M (fun B _ => B) Bs (maskWeights w) ω

/-- `E_{w,I}[w(I)]` for a batched prophet algorithm on the ordered partition `Bs`, with `w ∼ μ`
and the internal randomness `ω ∼ ρ` independent of `w`. -/
noncomputable def prophetValue (A : BatchedRule E (E → ℝ)) (M : Set (Finset E))
    (μ : Measure (E → ℝ)) (Bs : List (Finset E)) : ℝ :=
  ∫ p : (E → ℝ) × A.Ω, setWeight p.1 (prophetRun A M Bs p.1 p.2) ∂(μ.prod A.ρ)

/-- `E_w[w(OPT(w))]`. -/
noncomputable def optBenchmark (μ : Measure (E → ℝ)) (opt : (E → ℝ) → Finset E) : ℝ :=
  ∫ w, setWeight w (opt w) ∂μ

/-- The law of the sampling scheme `R(w, F)` of §2.3 (p. 8) on the ordered partition `Bs`:
`R_t = B_t ∩ OPT(w_t, w̃^{(t)})` has the law of `OPT(w) ∩ B_t` (property 3) and the `R_t` are
independent (property 1). `realProb μ opt Bs r` is the probability that `R = r`, i.e. that
`R_t = r ∩ B_t` for every `t`. -/
noncomputable def realProb (μ : Measure (E → ℝ)) (opt : (E → ℝ) → Finset E)
    (Bs : List (Finset E)) (r : Finset E) : ℝ :=
  ∏ t : Fin Bs.length, μ.real {w | opt w ∩ Bs.get t = r ∩ Bs.get t}

/-- The run of a batched OCRS (Definition 2.1, p. 7): at time `t` it sees `B_t` and `R_t` and
selects `I_t ⊆ R_t` with `⊔_t I_t ∈ M`. -/
noncomputable def ocrsRunBatched (A : BatchedRule E (Finset E)) (M : Set (Finset E))
    (Bs : List (Finset E)) (r : Finset E) (ω : A.Ω) : Finset E :=
  runBatched A M (fun _ R => R) Bs (fun B => r ∩ B) ω

open Classical in
/-- `A` is a `c`-selectable batched OCRS for the sampling scheme `R(w, F)` (Definition 2.1, eq. (1),
p. 7), for every ordered partition in `𝓑`: for every `t`, every `S ⊆ B_t` and every `e ∈ S`,
`Pr[e ∈ I_t, R_t = S] ≥ c · Pr[R_t = S]` (the product form of `Pr[e ∈ I_t | R_t = S] ≥ c`). -/
def IsSelectableBatchedOCRS (A : BatchedRule E (Finset E)) (M : Set (Finset E))
    (μ : Measure (E → ℝ)) (opt : (E → ℝ) → Finset E) (𝓑 : Set (List (Finset E))) (c : ℝ) :
    Prop :=
  ∀ Bs ∈ 𝓑, ∀ t : Fin Bs.length, ∀ S ⊆ Bs.get t, ∀ e ∈ S,
    c * ∑ r ∈ Finset.univ.filter (fun r : Finset E => r ∩ Bs.get t = S), realProb μ opt Bs r ≤
      ∑ r ∈ Finset.univ.filter (fun r : Finset E => r ∩ Bs.get t = S),
        realProb μ opt Bs r * A.ρ.real {ω | e ∈ ocrsRunBatched A M Bs r ω}

end ProphetMatchingEFGT


