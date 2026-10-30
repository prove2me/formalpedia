-- Prove2me | Definitions.Def_LindenReversibility_Protocol_avg
-- name    : LindenReversibility_Protocol_avg
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:17:33.090506+00:00
-- url     : https://prove2.me/theorems/1612fa7f-5114-42fd-b04e-acc66b3bde3c
-- title:
--   Branch average $\langle f\rangle_{\mathrm{final}}$ over the final branches of a protocol
-- statement:
--   Let $f$ assign a value in $[0,+\infty]$ to each pure state of the joint system $\mathbb C^A\otimes\mathbb C^B\otimes\mathbb C^C$. For a protocol $P$ and an initial vector $\psi$, the **final average** $\langle f\rangle_{\text{final}}$ is defined by following unnormalized branch vectors: a step in which a party applies $K_1,\dots,K_n$ sends the branch vector $\varphi$ to the vectors $\varphi_k = (K_k)_{\text{lifted}}\,\varphi$, and continues on each; at a leaf with vector $\varphi$ the contribution is
--
--   $$
--   \|\varphi\|^2\, f\!\left(\varphi/\|\varphi\|\right).
--   $$
--
--   The average is the sum of the contributions of all leaves. For a unit vector $\psi$ and a local protocol, $\|\varphi\|^2$ is the probability of the branch (the product of the paper's $p_k = \operatorname{Tr}(P_k\otimes I\otimes I\,\rho^{ABC})$ along it) and $\varphi/\|\varphi\|$ its pure state, so this is the probability-weighted average of $f$ over the final branches that appears on both sides of (22).
--
--   **Formalization Note** A branch of probability zero ($\varphi = 0$) contributes $0$, as zero-probability outcomes do in the paper's sums.
-- source:
--   Linden, Popescu, Schumacher, Westmoreland, Reversibility of local transformations of multiparticle entanglement, arXiv:quant-ph/9912039v1, eq. (22), p.4 (with eq. (7), p.2)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_LindenReversibility_liftA
import Definitions.Def_LindenReversibility_liftB
import Definitions.Def_LindenReversibility_liftC
import Definitions.Def_LindenReversibility_Protocol

open scoped ENNReal

namespace LindenReversibility

/-- Linden, Popescu, Schumacher, Westmoreland, arXiv:quant-ph/9912039v1, eq. (22), p.4: the
average `⟨f⟩_final` of a branch quantity `f` over the final branches of a protocol, each branch
weighted by its probability, starting from the joint pure state `ψ`.

The branches are tracked as **unnormalized** vectors: a step with operators `K_i` sends the branch
vector `φ` to the vectors `(K_i ⊗ 1 ⊗ 1) φ` (for Alice; similarly for Bob and Claire). A final
branch vector `φ` has probability `‖φ‖²` (the product of the paper's `p_k = Tr(P_k ⊗ I ⊗ I ρ)`,
eq. (7), along the branch, times `‖ψ‖²`) and normalized state `φ / ‖φ‖`, so
`avg f stop φ = ‖φ‖² · f(φ / ‖φ‖)` and a step sums over its outcomes.

**Formalization Note.** Values in `ℝ≥0∞`. A branch of probability zero (`φ = 0`) contributes
`0 · f 0 = 0`, i.e. zero-probability outcomes drop out, as in the paper's sums. For a unit vector
`ψ` and a protocol with `Protocol.IsLocal`, the leaf weights are the outcome probabilities. -/
noncomputable def Protocol.avg {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] [Fintype C] [DecidableEq C] (f : EuclideanSpace ℂ (A × (B × C)) → ℝ≥0∞) :
    Protocol A B C → EuclideanSpace ℂ (A × (B × C)) → ℝ≥0∞
  | .stop, φ => ENNReal.ofReal (‖φ‖ ^ 2) * f ((‖φ‖⁻¹ : ℝ) • φ)
  | .stepA _ K next, φ => ∑ i, (next i).avg f (QAlgorithms.act (liftA (K i)) φ)
  | .stepB _ K next, φ => ∑ i, (next i).avg f (QAlgorithms.act (liftB (K i)) φ)
  | .stepC _ K next, φ => ∑ i, (next i).avg f (QAlgorithms.act (liftC (K i)) φ)

end LindenReversibility


