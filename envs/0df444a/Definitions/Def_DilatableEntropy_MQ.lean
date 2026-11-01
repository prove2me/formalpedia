-- Prove2me | Definitions.Def_DilatableEntropy_MQ
-- name    : DilatableEntropy_MQ
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:51:01.104769+00:00
-- url     : https://prove2.me/theorems/643ece20-3ed9-4e90-bccd-e4e2f6a2ad45
-- title:
--   $M_Q=\max_{x\in Q}\|x\|_1$
-- statement:
--   The largest $\ell_1$ norm of a point of the sequence-form polytope is
--   $$
--   M_Q:=\max_{x\in Q}\|x\|_1=\max_{x\in Q}\sum_{\sigma\in\Sigma}|x_\sigma| .
--   $$
--   Every coordinate counts, including $x_\varnothing=1$.
--
--   It is the strong-convexity modulus scale in the $\ell_1$ norm (Theorem 5) and enters the range bound (Theorem 6).
--
--   **Formalization Note** Written as the supremum of the explicit sums $\sum_\sigma|x_\sigma|$ over $Q$; since $Q$ is nonempty and compact this is the maximum. Mathlib's norm on a function space is the sup norm and is not used.
-- source:
--   Farina, Kroer, Sandholm, Better Regularization for Sequential Decision Spaces, arXiv:2105.12954v2, §3, p.4 (M_X := max_{x∈X} ‖x‖₁)

import Mathlib
import Definitions.Def_DilatableEntropy_seqFormPolytope

namespace DilatableEntropy

/-- `M_Q := max_{x ∈ Q} ‖x‖₁`, the largest `ℓ1` norm of a point of the sequence-form polytope
(Farina, Kroer, Sandholm, *Better Regularization for Sequential Decision Spaces*, arXiv:2105.12954v2, §3, p.4, "`M_X := max_{x∈X} ‖x‖₁`"). Every coordinate counts, including `x_∅ = 1`.

**Formalization Note** Written as `sSup` of the explicit sums `∑_σ |x_σ|` over `Q`; `Q` is
nonempty and compact, so the supremum is the paper's maximum (Mathlib's norm on a Pi type is the
sup norm and is not used). -/
noncomputable def MQ (P : SeqDecisionProblem) : ℝ :=
  sSup ((fun x : Seq P → ℝ => ∑ σ, |x σ|) '' seqFormPolytope P)

end DilatableEntropy


