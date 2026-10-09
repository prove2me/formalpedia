-- Prove2me | Definitions.Def_SLQSolv_Finite_Comparison
-- name    : SLQSolv_Finite_Comparison
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T09:19:28.412414+00:00
-- url     : https://prove2.me/theorems/7474a8a8-7a5a-433b-b599-f4f9b006c1ff
-- title:
--   (5.12) and N(t), Theorem 5.3, p. 2295 — the fundamental matrix Φ_A and the lower comparison function N
-- statement:
--   Let $\Phi_A$ be the solution of the matrix ODE (5.12),
--
--   $$
--   \dot\Phi_A(s)=A(s)\Phi_A(s),\qquad \Phi_A(0)=I,
--   $$
--
--   and, for a symmetric matrix $P(0)$ and the solution $M_0$ of the Lyapunov equation (3.2), define
--
--   $$
--   N(t)=\big[\Phi_A(t)^\top\big]^{-1}\Big\{P(0)-\int_0^t\Phi_A(s)^\top\big[C(s)^\top M_0(s)C(s)+Q(s)\big]\Phi_A(s)\,ds\Big\}\Phi_A(t)^{-1}.
--   $$
--
--   In Theorem 5.3, with $P(0)$ the matrix representing $V^0(0,\cdot)$, $N$ is the lower bound in the sandwich $N(t)\le P(t)\le M_0(t)$ of (5.11).
--
--   **Formalization Note** (5.12) is stated in integral form on $[0,T]$, $\Phi_A(t)=I+\int_0^tA(s)\Phi_A(s)\,ds$, with a continuous $\Phi_A$ and an integrable integrand; the paper states (5.12) for $s\ge0$, but only $[0,T]$ enters. A fundamental matrix is invertible (Liouville's formula), so Lean's matrix inverse `⁻¹`, which returns $0$ on a singular matrix, is the true inverse here. `nMat` takes the function $P$ and reads only $P(0)$; integrals are entrywise.
-- source:
--   Sun–Li–Yong, SIAM J. Control Optim. 54 (2016), Theorem 5.3, (5.12) and the definition of N(t), p. 2295

import Mathlib
import Definitions.Def_SLQSolv_Finite_Riccati

open MeasureTheory Set
open scoped NNReal Matrix

namespace SLQSolv.Finite

variable {Ω : Type*} {n m : ℕ}

/-- (5.12), p. 2295: `Φ_A` solves `Φ̇_A = AΦ_A`, `Φ_A(0) = I`, in integral form on `[0, T]`
(`Φ_A(t) = I + ∫₀ᵗ A(s)Φ_A(s) ds` with an integrable integrand). -/
def IsFundSolA (d : Data Ω n m) (Φ : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ContinuousOn Φ (Icc 0 d.T) ∧
  (∀ i j, IntegrableOn (fun s : ℝ => (d.A s.toNNReal * Φ s.toNNReal) i j) (Icc 0 (d.T : ℝ))) ∧
  ∀ t ≤ d.T, Φ t = 1 + matInt 0 t (fun s => d.A s * Φ s)

/-- `N(t) = [Φ_A(t)ᵀ]⁻¹ {P(0) − ∫₀ᵗ Φ_A(s)ᵀ[C(s)ᵀM₀(s)C(s) + Q(s)]Φ_A(s) ds} Φ_A(t)⁻¹`
(Theorem 5.3, p. 2295), built from `P(0)`, the Lyapunov solution `M₀` of (3.2) and `Φ_A` of (5.12). -/
noncomputable def nMat (d : Data Ω n m) (M0 Φ P : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (t : ℝ≥0) :
    Matrix (Fin n) (Fin n) ℝ :=
  ((Φ t)ᵀ)⁻¹ * (P 0 - matInt 0 t (fun s => (Φ s)ᵀ * ((d.C s)ᵀ * M0 s * d.C s + d.Q s) * Φ s))
    * (Φ t)⁻¹

end SLQSolv.Finite


