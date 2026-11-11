-- Prove2me | Definitions.Def_GainShareOpt_StochBalance_Canonical
-- name    : GainShareOpt_StochBalance_Canonical
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:48:25.076266+00:00
-- url     : https://prove2.me/theorems/b2e36390-62b8-4387-8811-5811a1f6d199
-- title:
--   The canonical functional (6), $W_1,W_2$, the critical interval $\tau(f)$, $\Phi_1,\Phi_2,\Psi_f$ and Program (31)
-- statement:
--   For $f\in F_0$ the **canonical functional** (6) is
--   $$\inf_{\ell\ge0,\ 0<\psi\le1,\ 0\le\tilde\psi\le\psi}\ \frac{\int_0^\ell e^{-z}f(z)\,dz+\int_\ell^{\ell+\tilde\psi}e^{-z}\,dz+(\psi-\tilde\psi)\bigl(1-f(\ell+\tilde\psi)\bigr)}{\psi}.$$
--   With $\psi=1$ the test is $\Psi_f(\ell,\tilde\psi)=\int_0^\ell e^{-z}f+\int_\ell^{\ell+\tilde\psi}e^{-z}+(1-\tilde\psi)(1-f(\ell+\tilde\psi))$. Further, $W_1=\int_0^1e^{-z}f(z)\,dz+e^{-1}(1-e^{-1})$ and $W_2=\min\{\Psi_f(\ell,\tilde\psi):\ell,\tilde\psi\in[0,1],\ \ell+\tilde\psi\le1\}$ ((11)–(12)).
--
--   The critical time is $\tau(f)=\inf\{z\in[0,1]:f(z)\ge1-1/e\}$, with $\tau(f)=1$ if $f(1)<1-1/e$ (24). Then $\Phi_1(f)=\int_0^{\tau(f)}e^{-z}f(z)\,dz+(1-1/e)e^{-\tau(f)}$ (25), $\Phi_2(f)=\min\{\Psi_f(\ell,\tilde\psi):\ell,\tilde\psi\in[0,1],\ \ell+\tilde\psi\le\tau(f)\}$ (26), $\Psi_{f,\sigma}(\ell)=\Psi_f(\ell,\sigma-\ell)$ and $\Psi_f(\sigma)=\min_{0\le\ell\le\sigma}\Psi_{f,\sigma}(\ell)$ ((28)–(30)).
--
--   **Program (31)** maximizes $\gamma$ over $\gamma\in\mathbb R$, $f\in F_0$ subject to $\Phi_1(f)\ge\gamma$ and $\Psi_f(\sigma)\ge\gamma$ for all $\sigma\in[0,\tau(f)]$; $\gamma^*$ is its supremal value.
--
--   **Formalization Note** Minima over compact parameter sets are written as real `sInf`; for continuous $f$ they are attained. $1/e$ is `Real.exp (-1)`.
-- source:
--   Pan Xu, Gain-Sharing Optimization in Randomized Primal–Dual Analysis: Structure and Certification, arXiv:2503.09508 (held copy of 2026-10-31, sha256 d28f3b77…6c70b), p. 5, (6); p. 11, (11)–(12); pp. 15–16, (24)–(31)

import Mathlib
import Definitions.Def_GainShareOpt_StochBalance_CertFunctional

namespace GainShareOpt.StochBalance

/-- The ratio inside the canonical infimum (6), at initial load `ℓ`, total load `ψ` and
load-adding portion `ψ̃`. -/
noncomputable def canonicalTest (f : ℝ → ℝ) (ℓ ψ ψt : ℝ) : ℝ :=
  ((∫ z in (0 : ℝ)..ℓ, Real.exp (-z) * f z) + (∫ z in ℓ..(ℓ + ψt), Real.exp (-z))
    + (ψ - ψt) * (1 - f (ℓ + ψt))) / ψ

/-- The canonical functional (6): the infimum of `canonicalTest f ℓ ψ ψ̃` over
`ℓ ≥ 0`, `0 < ψ ≤ 1`, `0 ≤ ψ̃ ≤ ψ`. -/
noncomputable def canonicalL (f : ℝ → ℝ) : ℝ :=
  sInf {r | ∃ ℓ ψ ψt : ℝ, 0 ≤ ℓ ∧ 0 < ψ ∧ ψ ≤ 1 ∧ 0 ≤ ψt ∧ ψt ≤ ψ ∧
    r = canonicalTest f ℓ ψ ψt}

/-- The test `Ψ_f(ℓ, ψ̃)` with `ψ = 1` (the expression in (12), (26), (51), (52)). -/
noncomputable def partialTest (f : ℝ → ℝ) (ℓ ψt : ℝ) : ℝ :=
  (∫ z in (0 : ℝ)..ℓ, Real.exp (-z) * f z) + (∫ z in ℓ..(ℓ + ψt), Real.exp (-z))
    + (1 - ψt) * (1 - f (ℓ + ψt))

/-- `W1` of (11). -/
noncomputable def W1 (f : ℝ → ℝ) : ℝ :=
  (∫ z in (0 : ℝ)..1, Real.exp (-z) * f z) + Real.exp (-1) * (1 - Real.exp (-1))

/-- `W2` of (12): the minimum of `Ψ_f(ℓ, ψ̃)` over `ℓ, ψ̃ ∈ [0, 1]`, `ℓ + ψ̃ ≤ 1`. -/
noncomputable def W2 (f : ℝ → ℝ) : ℝ :=
  sInf {r | ∃ ℓ ψt : ℝ, ℓ ∈ Set.Icc (0 : ℝ) 1 ∧ ψt ∈ Set.Icc (0 : ℝ) 1 ∧ ℓ + ψt ≤ 1 ∧
    r = partialTest f ℓ ψt}

/-- The end `τ(f)` of the critical interval (24): `inf{z ∈ [0, 1] : f(z) ≥ 1 - 1/e}`, and `1`
when `f(1) < 1 - 1/e`. -/
noncomputable def critTime (f : ℝ → ℝ) : ℝ :=
  if f 1 < 1 - Real.exp (-1) then 1
  else sInf {z | z ∈ Set.Icc (0 : ℝ) 1 ∧ 1 - Real.exp (-1) ≤ f z}

/-- `Φ1(f)` of (25). -/
noncomputable def Phi1 (f : ℝ → ℝ) : ℝ :=
  (∫ z in (0 : ℝ)..(critTime f), Real.exp (-z) * f z)
    + (1 - Real.exp (-1)) * Real.exp (-(critTime f))

/-- `Φ2(f)` of (26): the minimum of `Ψ_f(ℓ, ψ̃)` over `ℓ, ψ̃ ∈ [0, 1]`, `ℓ + ψ̃ ≤ τ(f)`. -/
noncomputable def Phi2 (f : ℝ → ℝ) : ℝ :=
  sInf {r | ∃ ℓ ψt : ℝ, ℓ ∈ Set.Icc (0 : ℝ) 1 ∧ ψt ∈ Set.Icc (0 : ℝ) 1 ∧ ℓ + ψt ≤ critTime f ∧
    r = partialTest f ℓ ψt}

/-- `Ψ_{f,σ}(ℓ) = Ψ_f(ℓ, σ - ℓ)` for `0 ≤ ℓ ≤ σ`. -/
noncomputable def psiSigma (f : ℝ → ℝ) (σ ℓ : ℝ) : ℝ :=
  partialTest f ℓ (σ - ℓ)

/-- The minimized partial-load test `Ψ_f(σ) = min_{ℓ ∈ [0, σ]} Ψ_{f,σ}(ℓ)` ((28)–(30)). -/
noncomputable def psiMin (f : ℝ → ℝ) (σ : ℝ) : ℝ :=
  sInf (psiSigma f σ '' Set.Icc 0 σ)

/-- Feasibility of `(γ, f)` in Program (31): `f ∈ F0`, `Φ1(f) ≥ γ`, and `Ψ_f(σ) ≥ γ` for all
`σ ∈ [0, τ(f)]`. -/
def Feasible31 (γ : ℝ) (f : ℝ → ℝ) : Prop :=
  f ∈ F0 ∧ γ ≤ Phi1 f ∧ ∀ σ ∈ Set.Icc 0 (critTime f), γ ≤ psiMin f σ

/-- `γ*`, the supremal value of Program (31). -/
noncomputable def gammaStar : ℝ :=
  sSup {γ | ∃ f, Feasible31 γ f}

end GainShareOpt.StochBalance


