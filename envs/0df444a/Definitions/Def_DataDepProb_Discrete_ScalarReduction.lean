-- Prove2me | Definitions.Def_DataDepProb_Discrete_ScalarReduction
-- name    : DataDepProb_Discrete_ScalarReduction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:11:39.365731+00:00
-- url     : https://prove2.me/theorems/d9caa9d7-b58c-4fa4-931a-7d888d84aed9
-- title:
--   Appendix C: the projection inputs, $A_s$, $p_\theta$, $\varphi$, $\Psi$, and $\Gamma,\Lambda,\Theta$
-- statement:
--   The penalized projection of Appendix C takes two vectors as input: $e=e_s$ for a sample $s\in[d]^n$ with $n\ge1$, and $q^+=\mathrm{MW}_\eta(q,f,b)$ with $q\in\tilde\Delta_d$, $f:[d]\to[0,1]$, $y\in[d]$ and $b=(f(y)+E_u[f])/2$, as in (14). For $\lambda\ge0$ the objective is
--   $$A_s(p)=\mathrm{KL}(p\|q^+)+8\lambda H(p-e)^2 .$$
--   For $\theta\ge0$ (Eq. (39))
--   $$p_\theta=\arg\min_{p\in\tilde\Delta_d}\{\mathrm{KL}(p\|q^+)+\theta H(p-e)\},\qquad \varphi(\theta)=H(p_\theta-e),$$
--   and $\Psi(\theta)=\theta-16\lambda\varphi(\theta)$ (Lemma C.3). The constants are $\Gamma=1+\log(1+d)$, $\Lambda=\log(2d)$ and $\Theta=16\lambda\log(1+d)$.
--
--   **Formalization Note.** $p_\theta$ is the minimizer selected by `Classical.epsilon`; for $\theta\ge0$ and $q^+>0$ the objective is continuous and strictly convex on the compact set $\tilde\Delta_d$, so the minimizer exists and is unique. The input condition is a predicate on $(\eta,q^+,e)$.
-- source:
--   Feldman, Kale, Majid, Talwar, Data-Dependent Probability Estimation via Sample Amplification, STOC 2027 submission (manuscript sha256 28400f1c…), p. 37, Appendix C and Proposition C.1; p. 38, Eq. (39), Lemma C.3

import Mathlib
import Definitions.Def_DataDepProb_Discrete_Simplex
import Definitions.Def_DataDepProb_Discrete_Divergence
import Definitions.Def_DataDepProb_Discrete_MW

namespace DataDepProb.Discrete

/-!
# Appendix C: the inputs of the penalized projection, `A_s`, `p_θ`, `φ`, `Ψ` and the constants

Feldman, Kale, Majid, Talwar, *Data-Dependent Probability Estimation via Sample Amplification*,
STOC 2027 submission (manuscript sha256 28400f1c…), Appendix C pp. 37–38, Eqs. (39)–(40).

* `ProjInput η qplus e` is the standing assumption of Appendix C (p. 37): `e = e_s` for a sample
  `s ∈ [d]^n` with `n ≥ 1`, and `q⁺ = MW_η(q, f, b)` with `q ∈ ∆̃_d`, `f : [d] → [0, 1]`, `y ∈ [d]`
  and `b = (f(y) + E_u[f])/2` as in (14).
* `objA lam qplus e p = A_s(p) = KL(p‖q⁺) + λ P_s(p)` with `P_s(p) = 8H(p − e)²`.
* `pTheta qplus e θ = p_θ = argmin_{p ∈ ∆̃_d} {KL(p‖q⁺) + θ H(p − e)}` (Eq. (39)), the minimizer
  chosen by `Classical.epsilon`. For `θ ≥ 0` and `q⁺ > 0` the minimizer exists (continuous
  objective on a compact nonempty set) and is unique (strictly convex objective), so this is the
  paper's `p_θ`.
* `phi = φ(θ) = H(p_θ − e)`, `Psi = Ψ(θ) = θ − 16λφ(θ)`; `gammaC d = Γ = 1 + log(1 + d)`,
  `LambdaC d = Λ = log(2d)`, `ThetaC lam d = Θ = 16λ log(1 + d)`.
-/

/-- The standing inputs of Appendix C: `e = e_s` for some sample `s ∈ [d]^n`, `n ≥ 1`, and
`q⁺ = MW_η(q, f, b)` for some `q ∈ ∆̃_d`, `f : [d] → [0, 1]`, `y ∈ [d]`, `b = (f(y) + E_u[f])/2`. -/
def ProjInput {d : ℕ} (η : ℝ) (qplus e : Fin d → ℝ) : Prop :=
  (∃ n : ℕ, 0 < n ∧ ∃ s : Fin n → Fin d, e = eInit s) ∧
    ∃ q ∈ truncSimplex d, ∃ f : Fin d → ℝ, (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
      ∃ y : Fin d, qplus = mw η q f ((f y + expect (unif d) f) / 2)

/-- `A_s(p) = KL(p‖q⁺) + λ P_s(p)`, `P_s(p) = 8H(p − e)²` (Proposition C.1). -/
noncomputable def objA {d : ℕ} (lam : ℝ) (qplus e p : Fin d → ℝ) : ℝ :=
  kl p qplus + lam * penalty e p

/-- `p_θ = argmin_{p ∈ ∆̃_d} {KL(p‖q⁺) + θH(p − e)}` (Eq. (39)). -/
noncomputable def pTheta {d : ℕ} (qplus e : Fin d → ℝ) (θ : ℝ) : Fin d → ℝ :=
  Classical.epsilon fun p => p ∈ truncSimplex d ∧
    IsMinOn (fun p => kl p qplus + θ * HFun (p - e)) (truncSimplex d) p

/-- `φ(θ) = H(p_θ − e)` (Eq. (39)). -/
noncomputable def phi {d : ℕ} (qplus e : Fin d → ℝ) (θ : ℝ) : ℝ :=
  HFun (pTheta qplus e θ - e)

/-- `Ψ(θ) = θ − 16λφ(θ)` (Lemma C.3). -/
noncomputable def Psi {d : ℕ} (lam : ℝ) (qplus e : Fin d → ℝ) (θ : ℝ) : ℝ :=
  θ - 16 * lam * phi qplus e θ

/-- `Γ = 1 + log(1 + d)` (Appendix C, p. 37). -/
noncomputable def gammaC (d : ℕ) : ℝ := 1 + Real.log (1 + (d : ℝ))

/-- `Λ = log(2d)` (Appendix C, p. 37). -/
noncomputable def LambdaC (d : ℕ) : ℝ := Real.log (2 * (d : ℝ))

/-- `Θ = 16λ log(1 + d)` (Lemma C.3). -/
noncomputable def ThetaC (lam : ℝ) (d : ℕ) : ℝ := 16 * lam * Real.log (1 + (d : ℝ))

end DataDepProb.Discrete


