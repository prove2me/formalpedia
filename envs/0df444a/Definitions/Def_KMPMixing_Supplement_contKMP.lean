-- Prove2me | Definitions.Def_KMPMixing_Supplement_contKMP
-- name    : KMPMixing_Supplement_contKMP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:54:15.703452+00:00
-- url     : https://prove2.me/theorems/db869606-8e10-4f4a-a526-7ab1966951e4
-- title:
--   The continuous KMP chain $K^{(G)}$ on $\Delta^{\mathrm{cont}}_G$
-- statement:
--   Let $G=([d],E)$ be a connected graph. The **continuous KMP chain** lives on the simplex
--   $$
--   \Delta^{\mathrm{cont}}_G=\Big\{v\in\mathbb R^d_{\ge0}:\sum_xv_x=1\Big\}.
--   $$
--   From $v$, it samples a uniformly random edge $\{i,j\}\in E$ and an independent $\xi\sim\mathrm{Unif}[0,1]$, and sets
--   $$
--   v_i\leftarrow(v_i+v_j)\,\xi,\qquad v_j\leftarrow(v_i+v_j)(1-\xi),
--   $$
--   both right-hand sides using the old values, all other coordinates unchanged. $K^{(G)}$ is its transition kernel; its stationary law is $\mu_G=\mathrm{Dirichlet}(1,\dots,1)$, the uniform law on the simplex.
--
--   This is the continuum limit of the KMP chain; Theorem 5.5 transfers the mission's particle-number-free bound to it.
--
--   **Formalization Note** The kernel is defined on all of $\mathbb R^d$; the simplex is invariant and every statement starts inside it. The uniform edge is the uniform law on the base mission's `edgePairs G` (each edge once, as $(i,j)$ with $i<j$); the law of $\xi$ is symmetric, so the orientation is immaterial. The kernel is built as the pushforward of $\delta_v\otimes\mathrm{Unif}[0,1]\otimes\mathrm{Unif}(E)$ along a measurable map, so it is never the junk zero kernel when $E\neq\emptyset$.
-- source:
--   Chen, Liu, Qin, Schulman, Song, Yao, Zhao, A Tale of Two Walks: From Kac to KMP and Back, arXiv:2609.38044 (sha256 6a9abdd4…), Definition 5.1, pp.32–33 (PDF pp.34–35); Eq. (27), p.33; µG, p.34 (PDF p.36)

import Mathlib
import Definitions.Def_KMPMixing_kmpChain
import Definitions.Def_KMPMixing_Supplement_measureMixing

namespace KMPMixing.Supplement

open MeasureTheory ProbabilityTheory KMPMixing

/-- The state space `Δ^cont_G = {v ∈ ℝ^d_{≥0} : Σ_x v_x = 1}` of the continuous KMP chain
(arXiv:2609.38044, Definition 5.1, p.32 (PDF p.34); Eq. (27), p.33). -/
def contSimplex (d : ℕ) : Set (Fin d → ℝ) := {v | (∀ i, 0 ≤ v i) ∧ ∑ i, v i = 1}

/-- The continuous KMP update on the edge `p = (i, j)` with split `ξ` (arXiv:2609.38044,
Definition 5.1, step 2, p.33 (PDF p.35)): `v_i ← (v_i + v_j) ξ`, `v_j ← (v_i + v_j)(1 − ξ)`, both
right-hand sides using the old values, all other coordinates unchanged. -/
noncomputable def contUpdate {d : ℕ} (p : Fin d × Fin d) (q : (Fin d → ℝ) × ℝ) : Fin d → ℝ :=
  Function.update (Function.update q.1 p.1 ((q.1 p.1 + q.1 p.2) * q.2)) p.2
    ((q.1 p.1 + q.1 p.2) * (1 - q.2))

theorem measurable_contUpdate {d : ℕ} (p : Fin d × Fin d) : Measurable (contUpdate p) := by
  unfold contUpdate
  apply measurable_pi_lambda
  intro a
  simp only [Function.update_apply]
  split_ifs <;> fun_prop

/-- The transition kernel `K^{(G)}` of the **continuous KMP chain** on a graph `G = ([d], E)`
(arXiv:2609.38044, Definition 5.1, pp.32–33 (PDF pp.34–35)): from `v`, sample a uniformly random
edge `e = {i, j} ∈ E` and an independent `ξ ∼ Unif[0, 1]`, and apply `contUpdate (i, j)`.

**Formalization Note** The kernel is defined on all of `ℝ^d` (the simplex `contSimplex d` is
invariant, and every statement starts the chain inside it). The uniform edge is the uniform law
on the base mission's `edgePairs G` (each edge once, as `(i, j)` with `i < j`); the law of `ξ` is
symmetric, so the orientation of the edge does not matter. The kernel is the pushforward, along
the measurable map `(v, ξ, e) ↦ contUpdate e (v, ξ)`, of `δ_v ⊗ Unif[0,1] ⊗ Unif(E)`. -/
noncomputable def contKMPKernel {d : ℕ} (G : SimpleGraph (Fin d)) [DecidableRel G.Adj] :
    Kernel (Fin d → ℝ) (Fin d → ℝ) :=
  Kernel.mapOfMeasurable
    ((Kernel.deterministic id measurable_id ×ₖ Kernel.const _ unif01) ×ₖ
      Kernel.const _ (uniformOn (↑(edgePairs G) : Set (Fin d × Fin d))))
    (fun q => contUpdate q.2 q.1)
    (measurable_from_prod_countable_left fun p => measurable_contUpdate p)

end KMPMixing.Supplement


