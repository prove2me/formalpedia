-- Prove2me | Definitions.Def_RobustMultitask_Estimator_Supplement_BanditTuning
-- name    : RobustMultitask_Estimator_Supplement_BanditTuning
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T07:00:53.861671+00:00
-- url     : https://prove2.me/theorems/514bbea8-0d41-41cf-a58b-9891b18f17a3
-- title:
--   Appendices D.1–D.2, pp. 56, 67 — hyperparameters, q and the constants C₁–C₆ of RMBandit
-- statement:
--   The tuning of RMBandit. Write $a=\frac{C_0-2}{4C_0}$ and $|\mathcal B_0|=\lceil q\log H\rceil$.
--
--   1. **Standard regime (D.1).** $\zeta_0=\zeta_{1,0}=a\sqrt{\min(s,d)/d}$, $\eta_0=\sqrt{27\log(d)|\mathcal B_0|/(qN)}$, $\omega_0=\zeta_0+\eta_0$, $\eta_{1,0}=\sqrt{9/(\rho N)}$, $\lambda_0^{(j)}=\sqrt{96\sigma_j^2x_{\max}^2K\log(d)|\mathcal B_0|/q}$, $\lambda_{1,0}^{(j)}=\sqrt{384\sigma_j^2x_{\max}^2/p_*}$, all instances as donors, and
--   $$q=\max\Bigl\{\tfrac{2\cdot384^3C_0^2x_{\max}^4(\max_i\sigma_i^2/p_i)Ksd\log d}{(C_0-2)^2h^2p_*^2\psi^2},\ \tfrac{576C_0^2x_{\max}^2(\max_i\sigma_i^2/p_i)Ksd\log N}{h^2p_*\psi},\ \tfrac{6\cdot192^2C_0^2x_{\max}^2(\max_i\sigma_i^2/p_i)Kd^2\log d\log N}{h^2p_*\psi N},\ \tfrac{96x_{\max}^2Kd\log(dN)}{p_*\psi\min_ip_i}\Bigr\}.$$
--   Constants: $C_1=\frac{96^2C_0\sigma_jx_{\max}}{(C_0-2)p_*^{3/2}\psi}$, $C_2=\frac{3C_0}{2p_*}\max_i\sqrt{\frac{2\sigma_i^2p_j}{\psi p_i}}$, $C_3=\frac{24C_0}{p_*}\max_i\sqrt{\frac{2\sigma_i^2p_j}{\psi\rho p_i}}$.
--   2. **Data-poor regime (D.2), target $j$.** $\zeta_0=\zeta_{1,0}=a$, the same $\eta_0,\omega_0,\eta_{1,0},\lambda_0^{(i)},\lambda_{1,0}^{(i)}$, donors $[N]\setminus\{j\}$, and
--   $$q=\max\Bigl\{\tfrac{2\cdot384^3C_0^2x_{\max}^4\max\{\max_{i\ne j}\sigma_i^2sd/p_i,\ \sigma_j^2s^2/p_j\}K\log d}{(C_0-2)^2h^2p_*^2\psi^2},\ \tfrac{576C_0^2x_{\max}^2(\max_{i\ne j}d^2\sigma_i^2/p_i)Ks^2\log N}{h^2p_*\psi},\ \tfrac{6\cdot192^2C_0^2x_{\max}^2(\max_{i\ne j}d^2\sigma_i^2/p_i)K\log d\log N}{h^2p_*\psi N},\ \tfrac{96x_{\max}^2Kd\log(dN)}{p_*\psi\min_{i\ne j}p_i},\ \tfrac{20K}{p_*p_j}\Bigr\}.$$
--   Constants: $C_4=C_1$, $C_5=\frac{3C_0}{2p_*}\max_{i\ne j}\sqrt{\frac{2\sigma_i^2d^2p_j}{\psi p_i}}$, $C_6=\frac{24C_0}{p_*}\max_{i\ne j}\sqrt{\frac{2\sigma_i^2d^2p_j}{\psi\rho p_i}}$.
--
--   **Formalization Note** The regularization inputs are instance-specific, the levels the proofs use (pp. 59, 63, 68, 69); the D.1 display prints a maximum over instances for $\lambda_0$ and $\lambda_{1,0}$, and the D.2 display prints $\max_{i\in[N]}\sqrt{384\sigma_j^2x_{\max}^2/p_*}$, which is the instance-specific value. In $\zeta_0$ of D.1, $s$ is capped at $d$. $p_*^{3/2}$ is written $p_*\sqrt{p_*}$.
-- source:
--   Xu & Bastani, Multitask Learning and Bandits via Robust Statistics, arXiv:2112.14233v5, p. 56 (Appendix D.1 hyperparameters, q, C₁–C₃), p. 67 (Appendix D.2 hyperparameters, q, C₄–C₆); proof levels pp. 59, 63, 68, 69

import Mathlib
import Definitions.Def_RobustMultitask_Estimator_Supplement_BanditAlgorithm

namespace RobustMultitask.Estimator.Supplement

open scoped NNReal

section Standard

variable {N : ℕ}

/-- `q` of Appendix D.1 (p. 56):
`q = max{ 2·384³ C₀² x⁴_max (max_i σ_i²/p_i) K s d log d / ((C₀−2)² h² p*² ψ²),
576 C₀² x²_max (max_i σ_i²/p_i) K s d log N / (h² p* ψ),
6·192² C₀² x²_max (max_i σ_i²/p_i) K d² log d log N / (h² p* ψ N),
96 x²_max K d log(dN) / (p* ψ min_i p_i) }`. -/
noncomputable def qStd (K d s : ℕ) (σ : Fin N → ℝ≥0) (p : Fin N → ℝ)
    (C₀ xmax h pstar ψ : ℝ) : ℝ :=
  let r : ℝ := ⨆ i, (σ i : ℝ) ^ 2 / p i
  max (max (max
    (2 * 384 ^ 3 * C₀ ^ 2 * xmax ^ 4 * r * K * s * d * Real.log d
      / ((C₀ - 2) ^ 2 * h ^ 2 * pstar ^ 2 * ψ ^ 2))
    (576 * C₀ ^ 2 * xmax ^ 2 * r * K * s * d * Real.log N / (h ^ 2 * pstar * ψ)))
    (6 * 192 ^ 2 * C₀ ^ 2 * xmax ^ 2 * r * K * (d : ℝ) ^ 2 * Real.log d * Real.log N
      / (h ^ 2 * pstar * ψ * N)))
    (96 * xmax ^ 2 * K * d * Real.log (d * N) / (pstar * ψ * (⨅ i, p i)))

/-- `ζ₀ = ζ_{1,0} = ((C₀−2)/(4C₀)) √(s/d)` of Appendix D.1, with `s` replaced by `min(s, d)`
(a sparsity bound larger than `d` carries no information). -/
noncomputable def zeta0Std (d s : ℕ) (C₀ : ℝ) : ℝ :=
  (C₀ - 2) / (4 * C₀) * Real.sqrt ((min s d : ℕ) / (d : ℝ))

/-- `η₀ = √(27 log(d) |B₀| / (qN))` of Appendices D.1 and D.2. -/
noncomputable def eta0 (N d b0 : ℕ) (q : ℝ) : ℝ :=
  Real.sqrt (27 * Real.log d * b0 / (q * N))

/-- The RMBandit inputs of Appendix D.1 (p. 56) for total horizon `H`:
`|B₀| = ⌈q log H⌉`, `ω₀ = ζ₀ + η₀`, `η_{1,0} = √(9/(ρN))`, `ζ_{1,0} = ζ₀`, the instance-specific
`λ₀^{(j)} = √(96σ_j² x²_max K log(d)|B₀|/q)` and `λ_{1,0}^{(j)} = √(384σ_j² x²_max/p*)` (the
levels used in the proofs on pp. 59 and 63), and all instances as donors. -/
noncomputable def stdTuning (K d s : ℕ) (σ : Fin N → ℝ≥0) (p : Fin N → ℝ)
    (C₀ xmax h pstar ψ ρ : ℝ) (H : ℕ) : BanditParams N :=
  let q := qStd K d s σ p C₀ xmax h pstar ψ
  let b0 := forcedLength q H
  { H := H
    b0 := b0
    h := h
    ω0 := zeta0Std d s C₀ + eta0 N d b0 q
    lam0 := fun j => Real.sqrt (96 * (σ j : ℝ) ^ 2 * xmax ^ 2 * K * Real.log d * b0 / q)
    ζ10 := zeta0Std d s C₀
    η10 := Real.sqrt (9 / (ρ * N))
    lam10 := fun j => Real.sqrt (384 * (σ j : ℝ) ^ 2 * xmax ^ 2 / pstar)
    donors := Finset.univ }

/-- `C₁ = 96² C₀ σ_j x_max / ((C₀−2) p*^{3/2} ψ)` (Appendix D.1). -/
noncomputable def constC1 (σ : Fin N → ℝ≥0) (C₀ xmax pstar ψ : ℝ) (j : Fin N) : ℝ :=
  96 ^ 2 * C₀ * (σ j : ℝ) * xmax / ((C₀ - 2) * (pstar * Real.sqrt pstar) * ψ)

/-- `C₂ = (3C₀/(2p*)) max_i √(2σ_i² p_j/(ψ p_i))` (Appendix D.1). -/
noncomputable def constC2 (σ : Fin N → ℝ≥0) (p : Fin N → ℝ) (C₀ pstar ψ : ℝ) (j : Fin N) : ℝ :=
  3 * C₀ / (2 * pstar) * ⨆ i, Real.sqrt (2 * (σ i : ℝ) ^ 2 * p j / (ψ * p i))

/-- `C₃ = (24C₀/p*) max_i √(2σ_i² p_j/(ψ ρ p_i))` (Appendix D.1). -/
noncomputable def constC3 (σ : Fin N → ℝ≥0) (p : Fin N → ℝ) (C₀ pstar ψ ρ : ℝ) (j : Fin N) :
    ℝ :=
  24 * C₀ / pstar * ⨆ i, Real.sqrt (2 * (σ i : ℝ) ^ 2 * p j / (ψ * ρ * p i))

end Standard

section DataPoor

variable {N : ℕ}

/-- `q` of Appendix D.2 (p. 67) for the data-poor instance `j`:
`q = max{ 2·384³ C₀² x⁴_max max{max_{i≠j} σ_i² s d/p_i, σ_j² s²/p_j} K log d / ((C₀−2)² h² p*² ψ²),
576 C₀² x²_max (max_{i≠j} d²σ_i²/p_i) K s² log N / (h² p* ψ),
6·192² C₀² x²_max (max_{i≠j} d²σ_i²/p_i) K log d log N / (h² p* ψ N),
96 x²_max K d log(dN) / (p* ψ min_{i≠j} p_i), 20K/(p* p_j) }`. -/
noncomputable def qPoor (K d s : ℕ) (σ : Fin N → ℝ≥0) (p : Fin N → ℝ)
    (C₀ xmax h pstar ψ : ℝ) (j : Fin N) : ℝ :=
  let r1 : ℝ := max (⨆ i : {i // i ≠ j}, (σ i : ℝ) ^ 2 * s * d / p i)
    ((σ j : ℝ) ^ 2 * (s : ℝ) ^ 2 / p j)
  let r2 : ℝ := ⨆ i : {i // i ≠ j}, (d : ℝ) ^ 2 * (σ i : ℝ) ^ 2 / p i
  max (max (max (max
    (2 * 384 ^ 3 * C₀ ^ 2 * xmax ^ 4 * r1 * K * Real.log d
      / ((C₀ - 2) ^ 2 * h ^ 2 * pstar ^ 2 * ψ ^ 2))
    (576 * C₀ ^ 2 * xmax ^ 2 * r2 * K * (s : ℝ) ^ 2 * Real.log N / (h ^ 2 * pstar * ψ)))
    (6 * 192 ^ 2 * C₀ ^ 2 * xmax ^ 2 * r2 * K * Real.log d * Real.log N
      / (h ^ 2 * pstar * ψ * N)))
    (96 * xmax ^ 2 * K * d * Real.log (d * N) / (pstar * ψ * (⨅ i : {i // i ≠ j}, p i))))
    (20 * K / (pstar * p j))

/-- The RMBandit inputs of Appendix D.2 (p. 67) for the data-poor instance `j` and total horizon
`H`: `|B₀| = ⌈q log H⌉`, `ζ₀ = ζ_{1,0} = (C₀−2)/(4C₀)`, `ω₀ = ζ₀ + η₀`, `η_{1,0} = √(9/(ρN))`, the
instance-specific `λ₀^{(i)} = √(96σ_i² x²_max K log(d)|B₀|/q)` and
`λ_{1,0}^{(i)} = √(384σ_i² x²_max/p*)` (pp. 67–69), and every instance except `j` as donor
(Remark 4). -/
noncomputable def poorTuning (K d s : ℕ) (σ : Fin N → ℝ≥0) (p : Fin N → ℝ)
    (C₀ xmax h pstar ψ ρ : ℝ) (j : Fin N) (H : ℕ) : BanditParams N :=
  let q := qPoor K d s σ p C₀ xmax h pstar ψ j
  let b0 := forcedLength q H
  { H := H
    b0 := b0
    h := h
    ω0 := (C₀ - 2) / (4 * C₀) + eta0 N d b0 q
    lam0 := fun i => Real.sqrt (96 * (σ i : ℝ) ^ 2 * xmax ^ 2 * K * Real.log d * b0 / q)
    ζ10 := (C₀ - 2) / (4 * C₀)
    η10 := Real.sqrt (9 / (ρ * N))
    lam10 := fun i => Real.sqrt (384 * (σ i : ℝ) ^ 2 * xmax ^ 2 / pstar)
    donors := Finset.univ.erase j }

/-- `C₄ = 96² C₀ σ_j x_max / ((C₀−2) p*^{3/2} ψ)` (Appendix D.2). -/
noncomputable def constC4 (σ : Fin N → ℝ≥0) (C₀ xmax pstar ψ : ℝ) (j : Fin N) : ℝ :=
  96 ^ 2 * C₀ * (σ j : ℝ) * xmax / ((C₀ - 2) * (pstar * Real.sqrt pstar) * ψ)

/-- `C₅ = (3C₀/(2p*)) max_{i≠j} √(2σ_i² d² p_j/(ψ p_i))` (Appendix D.2). -/
noncomputable def constC5 (d : ℕ) (σ : Fin N → ℝ≥0) (p : Fin N → ℝ) (C₀ pstar ψ : ℝ)
    (j : Fin N) : ℝ :=
  3 * C₀ / (2 * pstar) *
    ⨆ i : {i // i ≠ j}, Real.sqrt (2 * (σ i : ℝ) ^ 2 * (d : ℝ) ^ 2 * p j / (ψ * p i))

/-- `C₆ = (24C₀/p*) max_{i≠j} √(2σ_i² d² p_j/(ψ ρ p_i))` (Appendix D.2). -/
noncomputable def constC6 (d : ℕ) (σ : Fin N → ℝ≥0) (p : Fin N → ℝ) (C₀ pstar ψ ρ : ℝ)
    (j : Fin N) : ℝ :=
  24 * C₀ / pstar *
    ⨆ i : {i // i ≠ j}, Real.sqrt (2 * (σ i : ℝ) ^ 2 * (d : ℝ) ^ 2 * p j / (ψ * ρ * p i))

end DataPoor

end RobustMultitask.Estimator.Supplement


