-- Prove2me | Definitions.Def_KMPMixing_Supplement_hitAndRun
-- name    : KMPMixing_Supplement_hitAndRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:54:46.636206+00:00
-- url     : https://prove2.me/theorems/ce6bf086-7d09-4300-808f-decfde2a36ee
-- title:
--   Coordinate hit-and-run on $S_n$ and the uniform law $\pi_n$
-- statement:
--   Let $n\ge2$ and
--   $$
--   S_n=\Big\{x\in\mathbb R^n_{\ge0}:\sum_{i=1}^nx_i\le1\Big\}.
--   $$
--   One step of **coordinate hit-and-run** chooses $i\in[n]$ uniformly and replaces $x_i$ by a uniform sample from $[0,\,1-\sum_{j\ne i}x_j]$, leaving the other coordinates unchanged. The target is $\pi_n$, the uniform distribution on $S_n$: Lebesgue measure restricted to $S_n$ and normalized by $\mathrm{vol}(S_n)=1/n!$.
--
--   Corollary 5.6 bounds the mixing time of this sampler through the continuous KMP chain on the star graph.
--
--   **Formalization Note** A uniform sample from $[0,a]$ is written $\xi a$ with $\xi\sim\mathrm{Unif}[0,1]$. The kernel lives on all of $\mathbb R^n$ ($S_n$ is invariant) and is the pushforward of $\delta_x\otimes\mathrm{Unif}[0,1]\otimes\mathrm{Unif}([n])$ along a measurable map. $\pi_n$ is `ProbabilityTheory.cond volume S_n`.
-- source:
--   Chen, Liu, Qin, Schulman, Song, Yao, Zhao, A Tale of Two Walks: From Kac to KMP and Back, arXiv:2609.38044 (sha256 6a9abdd4…), §5.3, p.38 (PDF p.40); Remark 5.7, p.39 (PDF p.41)

import Mathlib
import Definitions.Def_KMPMixing_Supplement_measureMixing

namespace KMPMixing.Supplement

open MeasureTheory ProbabilityTheory

/-- The standard simplex `S_n = {x ∈ ℝ^n_{≥0} : Σ_i x_i ≤ 1}` (arXiv:2609.38044, §5.3, p.38
(PDF p.40)). -/
def hitSimplex (n : ℕ) : Set (Fin n → ℝ) := {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

/-- The coordinate hit-and-run update in coordinate `i` (arXiv:2609.38044, §5.3, p.38
(PDF p.40)): `x_i` is replaced by `ξ · (1 − Σ_{j ≠ i} x_j)`, a uniform sample from
`[0, 1 − Σ_{j≠i} x_j]` when `ξ ∼ Unif[0, 1]`; the other coordinates are unchanged. -/
noncomputable def hitUpdate {n : ℕ} (i : Fin n) (q : (Fin n → ℝ) × ℝ) : Fin n → ℝ :=
  Function.update q.1 i (q.2 * (1 - ∑ j ∈ Finset.univ.erase i, q.1 j))

theorem measurable_hitUpdate {n : ℕ} (i : Fin n) : Measurable (hitUpdate i) := by
  unfold hitUpdate
  apply measurable_pi_lambda
  intro a
  simp only [Function.update_apply]
  split_ifs <;> fun_prop

/-- The transition kernel of **coordinate hit-and-run** on `S_n` (arXiv:2609.38044, §5.3, p.38
(PDF p.40)): choose `i ∈ [n]` uniformly and replace `x_i` by a uniform sample from
`[0, 1 − Σ_{j≠i} x_j]`, leaving the other coordinates unchanged.

**Formalization Note** Coordinates are `Fin n`. The kernel lives on all of `ℝ^n` (`S_n` is
invariant; every statement starts inside `S_n`). It is the pushforward of
`δ_x ⊗ Unif[0,1] ⊗ Unif([n])` along `(x, ξ, i) ↦ hitUpdate i (x, ξ)`. -/
noncomputable def hitAndRunKernel (n : ℕ) : Kernel (Fin n → ℝ) (Fin n → ℝ) :=
  Kernel.mapOfMeasurable
    ((Kernel.deterministic id measurable_id ×ₖ Kernel.const _ unif01) ×ₖ
      Kernel.const _ (uniformOn (Set.univ : Set (Fin n))))
    (fun q => hitUpdate q.2 q.1)
    (measurable_from_prod_countable_left fun i => measurable_hitUpdate i)

/-- `π_n`, the uniform distribution on `S_n` (arXiv:2609.38044, §5.3 and Remark 5.7, pp.38–39
(PDF pp.40–41)): Lebesgue measure restricted to `S_n` and normalized,
`π_n = vol(S_n)⁻¹ · vol|_{S_n}` (`vol(S_n) = 1/n!`). -/
noncomputable def hitUniform (n : ℕ) : Measure (Fin n → ℝ) :=
  ProbabilityTheory.cond volume (hitSimplex n)

end KMPMixing.Supplement


