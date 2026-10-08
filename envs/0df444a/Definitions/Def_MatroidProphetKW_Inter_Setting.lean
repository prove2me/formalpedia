-- Prove2me | Definitions.Def_MatroidProphetKW_Inter_Setting
-- name    : MatroidProphetKW_Inter_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T13:22:34.8241+00:00
-- url     : https://prove2.me/theorems/9183544a-f10a-4d43-92d4-d39177135847
-- title:
--   §2, §4.1–4.2 — the intersection $\mathcal I = \bigcap_j \mathcal I_j$, $\mathrm{OPT}(w)$, $B$, $C_j(A)$, $R_j(A)$, $C(A)$, $R(A)$ and the thresholds $T(A,i,j)$
-- statement:
--   Let $\mathcal U$ be a finite ground set and let $\mathcal M_1,\dots,\mathcal M_p$ be matroids on $\mathcal U$ with independent sets $\mathcal I_1,\dots,\mathcal I_p$. The **feasible** ("truly independent") sets are
--   $$\mathcal I = \mathcal I_1 \cap \dots \cap \mathcal I_p .$$
--   A **weight assignment** is a function $w : \mathcal U \to \mathbb R$, extended additively to sets by $w(S) = \sum_{x \in S} w(x)$, and
--   $$\mathrm{OPT}(w) = \max\{ w(S) : S \in \mathcal I \}$$
--   is the weight of a maximum-weight feasible set. For each $x \in \mathcal U$ let $F_x$ be a probability distribution on $\mathbb R$; the random weights $w(x)$ are independent with $w(x) \sim F_x$, i.e. $w$ has the product law $\mu = \bigotimes_x F_x$.
--
--   Fix a second weight assignment $w'$ (the "ghost sample", an independent draw from $\mu$). Let $B = B(w')$ be a feasible set $B \in \mathcal I$ of maximum weight $w'(B)$. For a set $A$ and an index $j$, consider the sets $R \subseteq B \setminus A$ with
--   $$A \cup R \in \mathcal I_j \qquad\text{and}\qquad B \subseteq \mathrm{cl}_j(A \cup R),$$
--   where $\mathrm{cl}_j$ is the closure (span) in $\mathcal M_j$. Among them, $R_j(A)$ is one of maximum weight $w'(R)$, and $C_j(A) = B \setminus R_j(A)$, so that $B = C_j(A) \sqcup R_j(A)$. Further
--   $$R(A) = \bigcap_j R_j(A), \qquad C(A) = \bigcup_j C_j(A).$$
--   Finally, for a parameter $\alpha$, a set $A$ and an element $x_i$, the thresholds of §4.2 are
--   $$T(A,i,j) = \frac1\alpha\, \mathbb E_{w'}\big[w'(R_j(A)) - w'(R_j(A \cup \{x_i\}))\big], \qquad T(A,i) = \sum_j T(A,i,j).$$
--
--   These are the objects in which Definition 3 ($\alpha$-balanced thresholds), the algorithm of §4.2, and the proof of Proposition 3 are written.
--
--   **Formalization Note** The ground set is a `Fintype` $\alpha$, the matroids are Mathlib's `Matroid α` indexed by `Fin p`; theorems assume each has ground set `Set.univ`. Sets are `Finset α`. $\mathrm{OPT}(w)$ is a `Finset.sup'` over the nonempty finset of feasible sets. When weights tie, the maximisers $B(w')$ and $R_j(A)$ are chosen by a fixed tie-breaking rule (the first maximiser in a fixed enumeration of `Finset α`, independent of the weights), so that they are measurable functions of $w'$; the paper's statements do not depend on the choice. $R_j(A)$ is required to be disjoint from $A$ (it is what a prophet forced to start with $A$ adds to it; Proposition 3's proof applies (14) to $V = R(A)$, which must be disjoint from $A$). If $A \notin \mathcal I_j$ there is no admissible $R$ and $R_j(A) = \emptyset$; no statement uses this case. $R(A)$ is the set of elements lying in every $R_j(A)$. Expectations are Bochner integrals against $\mu$ (`law F`); the theorems assume the $F_x$ are supported on $[0,\infty)$ with finite means, which makes every integrand integrable.
-- source:
--   Kleinberg & Weinberg, Matroid Prophet Inequalities, arXiv:1201.4764v1, p. 3 (§2, w(A), OPT(w)), p. 9 (§4.1, ℐ = ∩_j ℐ_j, B, C_j(A), R_j(A), R(A), C(A)), p. 10 (§4.2, T(A, i, j), T(A, i))

import Mathlib
import Definitions.Def_MatroidProphetKW_Single_Setting

open MeasureTheory

namespace MatroidProphetKW.Inter

/-!
Kleinberg & Weinberg, *Matroid Prophet Inequalities*, arXiv:1201.4764v1,
§2 (p. 3) and §4.1–§4.2 (pp. 9–10).

The ground set 𝒰 is a finite type `α`; the feasibility constraint is the intersection
ℐ = ℐ_1 ∩ ⋯ ∩ ℐ_p of the independent sets of `p` matroids `M j` on `α`. Weights are
real functions `w : α → ℝ`; the weight law is the product `Measure.pi F` of the laws `F x`.
-/

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- `S ∈ ℐ = ⋂_j ℐ_j`: `S` is independent in every one of the `p` matroids (§4.1, p. 9). -/
def IsIndep {p : ℕ} (M : Fin p → Matroid α) (S : Finset α) : Prop :=
  ∀ j, (M j).Indep (↑S : Set α)

/-- `OPT(w) = max { w(S) : S ∈ ℐ }`, the weight of a maximum-weight feasible set (§2, p. 3).
The maximum is over a finite nonempty family (`∅ ∈ ℐ`). -/
noncomputable def OPT {p : ℕ} (M : Fin p → Matroid α) (w : α → ℝ) : ℝ := by
  classical
  exact ((Finset.univ : Finset (Finset α)).filter (fun S => IsIndep M S)).sup'
    ⟨∅, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun j => by simp⟩⟩ (MatroidProphetKW.Single.wt w)

/-- The first set of a family of finite sets in a fixed enumeration of `Finset α`
(`Fintype.equivFin`), or `∅` if the family is empty. This is the fixed tie-breaking rule used
to pick "the" maximiser below; it does not depend on the weights. -/
noncomputable def firstOf (S : Finset (Finset α)) : Finset α :=
  if h : S.Nonempty then
    (Fintype.equivFin (Finset α)).symm
      ((S.image (Fintype.equivFin (Finset α))).min' (h.image _))
  else ∅

/-- A maximiser of `f` over the finite sets satisfying `P`, ties broken by `firstOf`
(`∅` if no set satisfies `P`). -/
noncomputable def argmaxOn (P : Finset α → Prop) (f : Finset α → ℝ) : Finset α := by
  classical
  exact firstOf ((Finset.univ : Finset (Finset α)).filter
    (fun S => P S ∧ ∀ T, P T → f T ≤ f S))

/-- `B = B(w′)`: the feasible set `B ∈ ℐ` maximising `w′(B)` (§4.1, p. 9), ties broken by the
fixed rule `firstOf`. -/
noncomputable def B {p : ℕ} (M : Fin p → Matroid α) (w' : α → ℝ) : Finset α :=
  argmaxOn (fun S => IsIndep M S) (MatroidProphetKW.Single.wt w')

/-- `R_j(A)` (§4.1, p. 9): among the partitions of `B` into `C_j ⊔ R_j` with
`A ∪ R_j ∈ ℐ_j` and `B ⊆ cl_j(A ∪ R_j)`, the one maximising `w′(R_j)`; here `R_j` ranges over
subsets of `B ∖ A` (the elements a prophet forced to start with `A` adds to it), ties broken
by `firstOf`. It is `∅` when no such `R_j` exists (i.e. when `A ∉ ℐ_j`). -/
noncomputable def Rj {p : ℕ} (M : Fin p → Matroid α) (j : Fin p) (A : Finset α)
    (w' : α → ℝ) : Finset α :=
  argmaxOn (fun R => R ⊆ B M w' \ A ∧ (M j).Indep (↑(A ∪ R) : Set α) ∧
      (↑(B M w') : Set α) ⊆ (M j).closure (↑(A ∪ R) : Set α)) (MatroidProphetKW.Single.wt w')

/-- `C_j(A) = B ∖ R_j(A)`, the other part of the partition (§4.1, p. 9). -/
noncomputable def Cj {p : ℕ} (M : Fin p → Matroid α) (j : Fin p) (A : Finset α)
    (w' : α → ℝ) : Finset α :=
  B M w' \ Rj M j A w'

/-- `R(A) = ⋂_j R_j(A)` (§4.1, p. 9). -/
noncomputable def Rint {p : ℕ} (M : Fin p → Matroid α) (A : Finset α) (w' : α → ℝ) :
    Finset α :=
  Finset.univ.filter (fun x => ∀ j, x ∈ Rj M j A w')

/-- `C(A) = ⋃_j C_j(A)` (§4.1, p. 9). -/
noncomputable def Cint {p : ℕ} (M : Fin p → Matroid α) (A : Finset α) (w' : α → ℝ) :
    Finset α :=
  Finset.univ.biUnion (fun j => Cj M j A w')

/-- The weight law: `w(x) ~ F x`, independent over `x` (§2, p. 3). -/
noncomputable def law (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)] :
    Measure (α → ℝ) :=
  Measure.pi F

/-- `T(A, i, j) = (1/α) E[w′(R_j(A)) − w′(R_j(A ∪ {x_i}))]` (§4.2, p. 10), the expectation
being over the ghost sample `w′ ~ law F`; `a` is the paper's parameter `α`, `x` is `x_i`. -/
noncomputable def Tij {p : ℕ} (M : Fin p → Matroid α) (F : α → Measure ℝ)
    [∀ x, IsProbabilityMeasure (F x)] (a : ℝ) (j : Fin p) (A : Finset α) (x : α) : ℝ :=
  (1 / a) * ∫ w', (MatroidProphetKW.Single.wt w' (Rj M j A w') - MatroidProphetKW.Single.wt w' (Rj M j (insert x A) w')) ∂(law F)

/-- `T(A, i) = ∑_j T(A, i, j)` (§4.2, p. 10). -/
noncomputable def Tsum {p : ℕ} (M : Fin p → Matroid α) (F : α → Measure ℝ)
    [∀ x, IsProbabilityMeasure (F x)] (a : ℝ) (A : Finset α) (x : α) : ℝ :=
  ∑ j, Tij M F a j A x

end MatroidProphetKW.Inter


