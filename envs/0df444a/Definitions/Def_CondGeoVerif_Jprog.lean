-- Prove2me | Definitions.Def_CondGeoVerif_Jprog
-- name    : CondGeoVerif_Jprog
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:24:37.771209+00:00
-- url     : https://prove2.me/theorems/b574a41d-09f8-45fc-a82d-bea0e8a028ed
-- title:
--   Contractions, $B_A=(I_k-A^\top A)^{1/2}$, $D_{f,g,A}$ and the envelopes $J_j(f,g,A;\eta)$
-- statement:
--   A matrix $A\in\mathbb R^{k\times k}$ is a **contraction** if $\|A\|_{\mathrm{op}}\le1$, and then $B_A=(I_k-A^\top A)^{1/2}$ is the positive semidefinite square root. For an ordered pair of rules $f$ (the anchor) and $g$ (the competitor) and a contraction $A$ (the overlap of two frames), the **conditional disagreement** is
--   $$D_{f,g,A}(u,z)=\mathbf 1\{g(A^\top u+B_Az)\ne f(u)\},\qquad u,z\in\mathbb R^k,$$
--   and the **envelopes** are, for $j\in\{0,1\}$,
--   $$J_j(f,g,A;\eta)=\mathbb E_U\big[2M_{j,\eta}(D_{f,g,A}(U,\cdot))-\mathbb E_G D_{f,g,A}(U,G)\big],$$
--   with $U,G\sim N(0,I_k)$ independent. For a single rule, $J_j(A;\eta)=J_j(f,f,A;\eta)$.
--
--   The signs of $J_0$ and $J_1$ over all ordered pairs and contractions classify the private sample complexity of verification.
--
--   **Formalization Note** $\|A\|_{\mathrm{op}}\le1$ is encoded as positive semidefiniteness of $I_k-A^\top A$, which is equivalent. $B_A$ is the continuous-functional-calculus square root. The outer expectation is a Bochner integral of a bounded integrand that is measurable for Borel rules (Lemma B.2), so it is the expectation; $\mathbb E_G D$ is the Gaussian measure of the disagreement section.
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), §3, p.4 (PDF p.7); §A.1, p.13 (PDF p.16); §A.9, p.21 (PDF p.24)

import Mathlib
import Definitions.Def_CondGeoVerif_Mprog

set_option autoImplicit false

namespace CondGeoVerif

open MeasureTheory
open scoped Matrix MatrixOrder

/-- `A ∈ ℝ^{k×k}` is a **contraction**, `‖A‖_op ≤ 1`, encoded as `I_k − AᵀA ⪰ 0`. -/
def IsContraction {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  (1 - Aᵀ * A).PosSemidef

/-- `B_A = (I_k − AᵀA)^{1/2}`, the positive semidefinite square root (continuous functional
calculus). -/
noncomputable def sqrtGram {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  CFC.sqrt (1 - Aᵀ * A)

/-- The disagreement indicator `D_{f,g,A}(u, z) = 1{g(Aᵀu + B_A z) ≠ f(u)}`. -/
noncomputable def Dfga {k : ℕ} (f g : Vec k → Bool) (A : Matrix (Fin k) (Fin k) ℝ) (u z : Vec k) :
    Bool :=
  decide (g (matVec Aᵀ u + matVec (sqrtGram A) z) ≠ f u)

/-- **The envelopes** `J_j(f, g, A; η)` (Chen, *The Conditional Geometry of Statistical
Verification*, manuscript, October 2026, sha256 07a66d18…, §3, p.4 = PDF p.7; §A.9, p.21):
for an anchor rule `f`, a competitor rule `g` and a contraction `A`,
`J_j(f, g, A; η) = E_U[2 M_{j,η}(D_{f,g,A}(U, ·)) − E_G D_{f,g,A}(U, G)]`,
`U, G ∼ N(0, I_k)` independent. The fixed-rule envelope `J_j(A; η)` of §A.1 is `Jprog j f f A η`.

**Formalization Note** The outer expectation is a Bochner integral. Its integrand is bounded
(`|·| ≤ 2`) and, for Borel `f, g`, measurable by Lemma B.2 of the paper (the mission's milestone
`lemma_B_2`), so the integral is the expectation. `E_G D(U, G)` is the Gaussian measure of the
disagreement section. `B_A` is the continuous-functional-calculus square root of `I_k − AᵀA`. -/
noncomputable def Jprog (j : Fin 2) {k : ℕ} (f g : Vec k → Bool) (A : Matrix (Fin k) (Fin k) ℝ)
    (η : ℝ) : ℝ :=
  ∫ u, (2 * Mprog j η (Dfga f g A u) - (gauss k {z | Dfga f g A u z = true}).toReal) ∂(gauss k)

end CondGeoVerif


