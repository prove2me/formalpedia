-- Prove2me | Definitions.Def_ZOGlobalLB_OneStage
-- name    : ZOGlobalLB_OneStage
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:48:59.85181+00:00
-- url     : https://prove2.me/theorems/b3aaf0c0-0d1f-4be9-ad33-b6f25cdd3fb9
-- title:
--   The one-stage experiment with reusable labels
-- statement:
--   An adaptive query rule chooses, at round $i$, from its seed and the earlier replies, a label $j_i$, a point $r_i\in\mathbb R^m$ and an activation $g_i\in[0,1]$; the reply is
--   $$Y_i=\mu_v(r_i,g_i)+Q_{j_i}(r_i,g_i),$$
--   where label $j$ always uses the same sample field $Q_j$. The record $\mathcal F_i$ is the seed and the first $i$ replies. For the analysis of Lemma C.4: the earlier features $\phi_t$ of the label chosen at round $i$, their span and the orthogonal projection onto it, the residual feature $\psi_i=(I-P)\phi_i$, the public terms $b_t=4(\sqrt{S(x_t)}-1)$, and the conditional mean $m_i(v,h)=b_i+\sum_{t<i:\,j_t=j_i}c_{it}(Y_t-b_t)+\langle\theta(v),\psi_i\rangle$.
--
--   **Formalization Note.** Rounds are 0-based; labels form a countable set with the discrete σ-algebra.
-- source:
--   Xia, Yuan, On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization, arXiv:2610.19652, (28)–(30), pp.15–18; Lemma C.4, (94)–(96), p.49

import Mathlib
import Definitions.Def_ZOGlobalLB_Field

open MeasureTheory
open scoped RealInnerProductSpace

namespace ZOGlobalLB

/-! # The one-stage experiment with reusable labels

Xia, Yuan, arXiv:2610.19652, Section 3.2, (28)–(30), pp.15–18; Lemma C.4, p.49, (94)–(96);
Lemma C.5, p.52; Theorem 3.3, p.18.

At round `i` the seed and the earlier replies choose a label `j_i`, a point `r_i ∈ ℝᵐ` and an
activation `g_i ∈ [0, 1]`; the reply is `Y_i = μ_v(r_i, g_i) + Q_{j_i}(r_i, g_i)`, where `Q_j` is
the one-stage field (85) of label `j`, the same sample at every query of label `j`. The record
`F_i` is the seed and the first `i` replies (the queries are functions of these).

**Formalization Note.** Rounds are 0-based: the history before round `i` is a vector of `i`
replies. Labels form a countable type `J` with its discrete σ-algebra; all tensors of all labels
form one array `G : J × Idx m → ℝ`, label `j` using `G (j, ·)`. The seed space `S₀` is an arbitrary
measurable space. -/

/-- **An adaptive query rule for the one-stage experiment** (p.18, p.49): measurable in the seed
and the earlier replies; the activation coordinate lies in `[0, 1]`. -/
structure OneStageRule (m : ℕ) (J S₀ : Type*) [MeasurableSpace J] [MeasurableSpace S₀] where
  /-- The label, point and activation of round `i`. -/
  query : (i : ℕ) → S₀ → (Fin i → ℝ) → J × E m × ℝ
  /-- The rule is jointly measurable. -/
  measurable_query : ∀ i, Measurable (Function.uncurry (query i))
  /-- Queries lie on the strip `g ∈ [0, 1]`. -/
  g_mem : ∀ i s h, (query i s h).2.2 ∈ Set.Icc (0 : ℝ) 1

namespace OneStageRule

open Classical

variable {m : ℕ} {J S₀ : Type*} [MeasurableSpace J] [MeasurableSpace S₀]

/-- The array of label `j` inside the array of all labels. -/
def labelArr (G : J × Idx m → ℝ) (j : J) : Idx m → ℝ := fun k => G (j, k)

/-- The replies of the first `n` rounds, for parameter `v`, seed `s` and tensors `G`:
`Y_i = μ_v(r_i, g_i) + Q_{j_i}(r_i, g_i)` (28), (94). -/
noncomputable def replies (A : OneStageRule m J S₀) (σ : ℝ) (v : E m) (s : S₀)
    (G : J × Idx m → ℝ) : (n : ℕ) → Fin n → ℝ
  | 0 => Fin.elim0
  | n + 1 =>
      Fin.snoc (α := fun _ => ℝ) (A.replies σ v s G n)
        (muV v (A.query n s (A.replies σ v s G n)).2.1 (A.query n s (A.replies σ v s G n)).2.2 +
          Qfield σ (labelArr G (A.query n s (A.replies σ v s G n)).1)
            (A.query n s (A.replies σ v s G n)).2.1 (A.query n s (A.replies σ v s G n)).2.2)

/-- The record `F_n` (seed and first `n` replies). -/
noncomputable def record (A : OneStageRule m J S₀) (σ : ℝ) (v : E m) (s : S₀)
    (G : J × Idx m → ℝ) (n : ℕ) : S₀ × (Fin n → ℝ) :=
  (s, A.replies σ v s G n)

/-- The query of an earlier round `t < i`, read off a history `y` of `i` replies. -/
def queryAt (A : OneStageRule m J S₀) {i : ℕ} (s : S₀) (y : Fin i → ℝ) (t : Fin i) :
    J × E m × ℝ :=
  A.query t s (fun k : Fin t => y (Fin.castLE (le_of_lt t.2) k))

/-- The feature `ϕ_t = ϕ(r_t, g_t)` of an earlier round `t < i` (86). -/
noncomputable def featAt (A : OneStageRule m J S₀) (σ : ℝ) {i : ℕ} (s : S₀) (y : Fin i → ℝ)
    (t : Fin i) : Hsp m :=
  phiFeat σ (A.queryAt s y t).2.1 (A.queryAt s y t).2.2

/-- The public term `b_t = 4(√S(x_t) - 1)` of an earlier round `t < i` (94). -/
noncomputable def pubAt (A : OneStageRule m J S₀) {i : ℕ} (s : S₀) (y : Fin i → ℝ)
    (t : Fin i) : ℝ :=
  4 * (Real.sqrt (Sq (A.queryAt s y t).2.1 (A.queryAt s y t).2.2) - 1)

/-- The span of the earlier features of the label chosen at round `i` (Lemma C.4, p.49). -/
noncomputable def sameLabelSpan (A : OneStageRule m J S₀) (σ : ℝ) {i : ℕ} (s : S₀)
    (y : Fin i → ℝ) : Submodule ℝ (Hsp m) :=
  Submodule.span ℝ
    (A.featAt σ s y '' {t | (A.queryAt s y t).1 = (A.query i s y).1})

/-- The current feature `ϕ_i = ϕ(r_i, g_i)` of round `i`. -/
noncomputable def featNow (A : OneStageRule m J S₀) (σ : ℝ) {i : ℕ} (s : S₀) (y : Fin i → ℝ) :
    Hsp m :=
  phiFeat σ (A.query i s y).2.1 (A.query i s y).2.2

/-- The public term `b_i = 4(√S(x_i) - 1)` of round `i` (94). -/
noncomputable def pubNow (A : OneStageRule m J S₀) {i : ℕ} (s : S₀) (y : Fin i → ℝ) : ℝ :=
  4 * (Real.sqrt (Sq (A.query i s y).2.1 (A.query i s y).2.2) - 1)

/-- Coefficients `c_{it}` represent the projection of `ϕ_i` onto the span of the earlier features
of its label: `P_{j_i,i-1} ϕ_i = Σ_{t<i : j_t = j_i} c_{it} ϕ_t` (Lemma C.4, p.49). -/
def IsProjCoef (A : OneStageRule m J S₀) (σ : ℝ) {i : ℕ} (s : S₀) (y : Fin i → ℝ)
    (c : Fin i → ℝ) : Prop :=
  ∃ x ∈ A.sameLabelSpan σ s y, A.featNow σ s y - x ∈ (A.sameLabelSpan σ s y)ᗮ ∧
    x = ∑ t ∈ Finset.univ.filter (fun t => (A.queryAt s y t).1 = (A.query i s y).1),
      c t • A.featAt σ s y t

/-- The residual feature `ψ_i = (I - P_{j_i,i-1}) ϕ_i` (Lemma C.4, p.49). -/
noncomputable def resid (A : OneStageRule m J S₀) (σ : ℝ) {i : ℕ} (s : S₀) (y : Fin i → ℝ) :
    Hsp m :=
  haveI : FiniteDimensional ℝ (A.sameLabelSpan σ s y) :=
    FiniteDimensional.span_of_finite ℝ ((Set.toFinite _).image _)
  haveI : CompleteSpace (A.sameLabelSpan σ s y) := FiniteDimensional.complete ℝ _
  A.featNow σ s y - (A.sameLabelSpan σ s y).starProjection (A.featNow σ s y)

/-- The conditional mean `m_i(v, h) = b_i + Σ_{t<i : j_t = j_i} c_{it}(Y_t - b_t) + ⟨θ(v), ψ_i⟩`
(96), at the history `h = (s, y)` and with coefficients `c`. -/
noncomputable def condMean (A : OneStageRule m J S₀) (σ : ℝ) (v : E m) {i : ℕ} (s : S₀)
    (y : Fin i → ℝ) (c : Fin i → ℝ) : ℝ :=
  A.pubNow s y +
    ∑ t ∈ Finset.univ.filter (fun t => (A.queryAt s y t).1 = (A.query i s y).1),
      c t * (y t - A.pubAt s y t) +
    ⟪thetaFeat σ v, A.resid σ s y⟫

end OneStageRule

end ZOGlobalLB


