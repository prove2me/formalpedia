-- Prove2me | Definitions.Def_MatroidProphetKW_Single_Setting
-- name    : MatroidProphetKW_Single_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:06.4635+00:00
-- url     : https://prove2.me/theorems/fb02bd03-8c55-4535-a330-e2a95082a7c0
-- title:
--   §2, §3.2 — weights $w(A)$, $\mathrm{OPT}$, the maximum-weight basis $B$, and the partition $B = C(A) \sqcup R(A)$
-- statement:
--   Let $\mathcal U$ be a finite ground set and $\mathcal M = (\mathcal U, \mathcal I)$ a matroid on $\mathcal U$. A **weight assignment** is a function $w : \mathcal U \to \mathbb R$, extended additively to sets by
--   $$w(A) = \sum_{x \in A} w(x), \qquad A \subseteq \mathcal U.$$
--   For a weight assignment $w$, $\mathrm{OPT}(w)$ is the weight of the maximum-weight feasible (independent) set,
--   $$\mathrm{OPT}(w) = \max\{ w(S) : S \in \mathcal I \}.$$
--   For each $x \in \mathcal U$ let $F_x$ be a probability distribution on $\mathbb R$ (in the paper, supported on $\mathbb R_+$). The random weights $w(x)$, $x \in \mathcal U$, are independent with $w(x) \sim F_x$, so $w$ is distributed according to the product measure $\mu = \bigotimes_{x} F_x$, and
--   $$\mathrm{OPT} = \mathbb E_{w \sim \mu}[\mathrm{OPT}(w)].$$
--
--   Now fix a second weight assignment $w'$ (the "ghost sample" of §3.2, an independent draw from $\mu$). Let $B = B(w')$ be a basis of $\mathcal M$ of maximum weight $w'(B)$. For a set $A$, the **admissible remainders** of $A$ are the sets $R \subseteq B \setminus A$ such that $A \cup R$ is a basis of $\mathcal M$; when $A$ is independent there is at least one. Among them, $R(A)$ is one of maximum weight $w'(R)$, and
--   $$C(A) = B \setminus R(A),$$
--   so that $B$ is partitioned into $C(A)$ and $R(A)$ and $A \cup R(A)$ is a basis.
--
--   These are the objects in which both the definition of $\alpha$-balanced thresholds (Definition 1) and the algorithm (9) are written.
--
--   **Formalization Note** The ground set is a `Fintype` $\alpha$ and the matroid is Mathlib's `Matroid α`; theorems assume $\mathcal M.E = $ `Set.univ`. Sets are `Finset α`. $\mathrm{OPT}(w)$ is a `Finset.sup'` over the (nonempty) finset of independent sets, so it is never a junk value. When weights tie, the maximum-weight basis $B(w')$ and the maximizer $R(A)$ are fixed by choice; the paper's statements do not depend on this choice. The paper only says $B$ is partitioned into $C, R$ with $A \cup R$ a basis; $R$ is required here to be disjoint from $A$, because Lemma 2 places $R(A)$ in $\mathcal M/A$, whose ground set is $\mathcal U - A$ (without it, on a one-element rank-one matroid with $A = B = \{x\}$, the choice $R = \{x\}$ would be allowed). For a dependent $A$ there is no admissible remainder and $R(A)$ is set to $\emptyset$; no statement uses this case. $\mathrm{OPT}$ is a Bochner integral; the theorems that use it assume $F_x([0,\infty)) = 1$ and finite means, which makes $\mathrm{OPT}(w)$ integrable. The theorems integrate only the numbers $w'(R(A))$ and $w'(C(A)) = w'(B) - w'(R(A))$, whose values do not depend on how ties are broken (Lemma 2 identifies $w'(R(A))$ with the maximum weight of a basis of $\mathcal M/A$). The additive extension $w(A)$ is shared by both the single-matroid mission and the $p$-matroid-intersection mission of this paper; the rest of this module is used by the single-matroid mission.
-- source:
--   Kleinberg & Weinberg, Matroid Prophet Inequalities, arXiv:1201.4764v1, p. 3 (§2, BOSP, w(A), OPT(w)), p. 5 (§3.2, w′, B, C(A), R(A)), p. 6 ((4)–(5), OPT = E[OPT(w)])

import Mathlib

namespace MatroidProphetKW.Single

open MeasureTheory

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The additive extension of a weight assignment `w : 𝒰 → ℝ` to sets, `w(A) = ∑_{x ∈ A} w(x)`
(Kleinberg–Weinberg, *Matroid Prophet Inequalities*, arXiv:1201.4764v1, §2, p. 3). -/
def wt (w : α → ℝ) (A : Finset α) : ℝ := ∑ x ∈ A, w x

/-- The independent sets of `M`, as a finset of finsets. Nonempty, since `∅` is independent. -/
noncomputable def indepSets (M : Matroid α) : Finset (Finset α) := by
  classical
  exact Finset.univ.filter (fun S : Finset α => M.Indep (↑S : Set α))

omit [DecidableEq α] in
lemma indepSets_nonempty (M : Matroid α) : (indepSets M).Nonempty := by
  classical
  refine ⟨∅, ?_⟩
  simp [indepSets, M.empty_indep]

/-- `OPT(w)`: the weight of the maximum-weight feasible (independent) set (§2, p. 3). -/
noncomputable def optW (M : Matroid α) (w : α → ℝ) : ℝ :=
  (indepSets M).sup' (indepSets_nonempty M) (wt w)

/-- `OPT = E[OPT(w)]`, where the weights `w(x)`, `x ∈ 𝒰`, are independent and `w(x) ∼ F_x`, i.e.
`w ∼ Measure.pi F` (§2, p. 3; used in (4) and (5), p. 6). -/
noncomputable def OPT (M : Matroid α) (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)] : ℝ :=
  ∫ w, optW M w ∂(Measure.pi F)

/-- The bases of `M`, as a finset of finsets. -/
noncomputable def bases (M : Matroid α) : Finset (Finset α) := by
  classical
  exact Finset.univ.filter (fun S : Finset α => M.IsBase (↑S : Set α))

omit [DecidableEq α] in
lemma bases_nonempty (M : Matroid α) : (bases M).Nonempty := by
  classical
  obtain ⟨B, hB⟩ := M.exists_isBase
  refine ⟨(Set.toFinite B).toFinset, ?_⟩
  simpa [bases] using hB

/-- `B = B(w′)`: a basis of `M` maximizing `w′(B)` (§3.2, p. 5). When several bases tie, one of
them is fixed once and for all by choice. -/
noncomputable def maxBase (M : Matroid α) (w' : α → ℝ) : Finset α :=
  (Finset.exists_max_image (bases M) (wt w') (bases_nonempty M)).choose

/-- The admissible remainders of `A`: the sets `R ⊆ B(w′) ∖ A` such that `A ∪ R` is a basis of `M`
(§3.2, p. 5: the partitions `B = C ⊔ R` with `A ∪ R` a basis). -/
noncomputable def remCands (M : Matroid α) (A : Finset α) (w' : α → ℝ) : Finset (Finset α) := by
  classical
  exact (maxBase M w' \ A).powerset.filter (fun R => M.IsBase (↑(A ∪ R) : Set α))

/-- `R(A)` (§3.2, p. 5): among the admissible remainders of `A`, one maximizing `w′(R)`.
It is defined (nonempty candidate set) for every independent `A`; for a dependent `A` it is `∅`. -/
noncomputable def Rset (M : Matroid α) (A : Finset α) (w' : α → ℝ) : Finset α := by
  classical
  exact if h : (remCands M A w').Nonempty then
      (Finset.exists_max_image (remCands M A w') (wt w') h).choose
    else ∅

/-- `C(A) = B(w′) ∖ R(A)` (§3.2, p. 5), the other half of the partition of `B(w′)`. -/
noncomputable def Cset (M : Matroid α) (A : Finset α) (w' : α → ℝ) : Finset α :=
  maxBase M w' \ Rset M A w'

end MatroidProphetKW.Single


