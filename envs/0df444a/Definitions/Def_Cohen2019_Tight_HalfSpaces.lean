-- Prove2me | Definitions.Def_Cohen2019_Tight_HalfSpaces
-- name    : Cohen2019_Tight_HalfSpaces
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T18:09:05.975883+00:00
-- url     : https://prove2.me/theorems/ebb37504-33ba-417f-a8a3-88c93e4a9f82
-- title:
--   Appendix A — the half-spaces A = {δᵀ(z − x) ≤ σ‖δ‖Φ⁻¹(p_A)} and B = {δᵀ(z − x) ≥ σ‖δ‖Φ⁻¹(1 − p_B)}
-- statement:
--   Fix $x,\delta\in\mathbb R^d$, a noise level $\sigma$, and numbers $\underline{p_A},\overline{p_B}\in(0,1)$. The proofs of Theorems 1 and 2 use the two half-spaces
--   $$A=\{z\in\mathbb R^d:\ \delta^T(z-x)\le\sigma\|\delta\|\,\Phi^{-1}(\underline{p_A})\},\qquad B=\{z\in\mathbb R^d:\ \delta^T(z-x)\ge\sigma\|\delta\|\,\Phi^{-1}(1-\overline{p_B})\},$$
--   whose boundaries are hyperplanes orthogonal to the perturbation $\delta$. Under $\mathcal N(x,\sigma^2 I)$ they carry probabilities $\underline{p_A}$ and $\overline{p_B}$, and they are the decision regions of the "worst-case" base classifier.
--
--   **Formalization Note.** $\delta^T(z-x)$ is the Euclidean inner product. The proof of the Claim $\mathbb P(X\in B)=\overline{p_B}$ (p. 15) recalls $B$ with "$\le$"; that is a misprint, and $B$ is defined here as on p. 14.
-- source:
--   Cohen, Rosenfeld, Kolter, Certified Adversarial Robustness via Randomized Smoothing, arXiv:1902.02918v2, Appendix A, proof of Theorem 1, definitions of A and B, p. 14

import Mathlib
import Definitions.Def_Cohen2019_Tight_Model

open MeasureTheory ProbabilityTheory

namespace Cohen2019.Tight

/-- The half-space `A := {z : δᵀ(z − x) ≤ σ‖δ‖Φ⁻¹(p̲A)}` (arXiv:1902.02918v2, Appendix A,
proof of Theorem 1, p. 14; reused in the proof of Theorem 2, p. 15).

**Formalization Note.** `δᵀ(z − x)` is the Euclidean inner product `⟪δ, z - x⟫`. -/
def setA {d : ℕ} (x δ : Space d) (σ pA : ℝ) : Set (Space d) :=
  {z | inner ℝ δ (z - x) ≤ σ * ‖δ‖ * Cohen2019.Robust.PhiInvReal pA}

/-- The half-space `B := {z : δᵀ(z − x) ≥ σ‖δ‖Φ⁻¹(1 − p̄B)}` (arXiv:1902.02918v2, Appendix A,
proof of Theorem 1, p. 14; reused in the proof of Theorem 2, p. 15). The recollection of `B`
printed on p. 15 has `≤`; that is a misprint, and this is the definition of p. 14. -/
def setB {d : ℕ} (x δ : Space d) (σ pB : ℝ) : Set (Space d) :=
  {z | σ * ‖δ‖ * Cohen2019.Robust.PhiInvReal (1 - pB) ≤ inner ℝ δ (z - x)}

end Cohen2019.Tight


