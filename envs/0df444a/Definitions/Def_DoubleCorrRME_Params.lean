-- Prove2me | Definitions.Def_DoubleCorrRME_Params
-- name    : DoubleCorrRME_Params
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:54:29.995916+00:00
-- url     : https://prove2.me/theorems/dd942ff1-5f30-4006-999d-7f6a3abf5277
-- title:
--   The parameters $m, L, \alpha', \Delta, \kappa, \rho, \lambda$ of §4.1
-- statement:
--   With $m=Nn$ and $L=\log(2/\delta)$ for $\delta\in(0,0.1)$, §4.1 sets
--
--   $$\alpha'=C_{\mathrm{ref}}\Big(\alpha+\frac{d+L}{m}\Big),\quad \Delta=C_\Delta\sqrt{\alpha'},\quad \kappa=1+\frac{\Delta^2}{\alpha'},\quad \rho=C_\rho\sqrt\kappa\Big(\frac1{\sqrt n}+\sqrt{\frac{d+L}{m}}\Big),\quad \lambda=\frac{\rho^2}{\varepsilon}.$$
--
--   The constants $C_{\mathrm{ref}},C_\Delta,C_\rho$ are the paper's $O(\cdot)$ constants; each statement quantifies them.
--
--   **Formalization Note** The logarithm is natural. Algorithm 2 uses $\Delta=C_\Delta(\sqrt{d/m}+\sqrt{\alpha'}+\sqrt{L/m})$, which agrees with $C_\Delta\sqrt{\alpha'}$ up to the constant.
-- source:
--   Aliakbarpour, Liu, Yin, Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time and Sub-Gaussian Rate, STOC 2027 submission (manuscript sha256 49e26e5e…), §4.1, p.20 (PDF p.21); Algorithm 2, line 2, p.30 (PDF p.31)

import Mathlib

namespace DoubleCorrRME

/-!
# The parameters of §4.1

Aliakbarpour, Liu, Yin, *Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time
and Sub-Gaussian Rate*, STOC 2027 submission (manuscript sha256 49e26e5e…), §4.1, p.20 (PDF p.21):
"We let m := Nn and L := log(2/δ), for all δ ∈ (0, 0.1). We further define α′ := O(α + (d+L)/m),
∆ := O(√α′), κ := 1 + ∆²/α′, ρ := O(√κ (1/√n + √((d+L)/m))), and λ := ρ²/ε."

**Formalization Note.** Each `O(·)` is a constant: `C_ref` in `α′`, `C_∆` in `∆`, `C_ρ` in `ρ`. They
are arguments here; each statement quantifies them (existentially in Lemma 4.1, universally in the
filter lemmas of §5, whose constants may then depend on them). `log` is the natural logarithm.
Algorithm 2, line 2, uses `∆ = C_∆(√(d/m) + √α′ + √(L/m))` instead of `C_∆√α′`; since
`d/m, L/m ≤ α′/C_ref`, the two agree up to a change of `C_∆`.
-/

/-- `L := log(2/δ)`. -/
noncomputable def Lδ (δ : ℝ) : ℝ := Real.log (2 / δ)

/-- `α′ := C_ref (α + (d + L)/m)` with `m = Nn`. -/
noncomputable def alphaP (Cref : ℝ) (N n d : ℕ) (α δ : ℝ) : ℝ :=
  Cref * (α + ((d : ℝ) + Lδ δ) / ((N : ℝ) * n))

/-- `∆ := C_∆ √α′`. -/
noncomputable def deltaP (CΔ α' : ℝ) : ℝ := CΔ * Real.sqrt α'

/-- `κ := 1 + ∆²/α′`. -/
noncomputable def kappaP (α' Δ : ℝ) : ℝ := 1 + Δ ^ 2 / α'

/-- `ρ := C_ρ √κ (1/√n + √((d + L)/m))` with `m = Nn`. -/
noncomputable def rhoP (Cρ κ : ℝ) (N n d : ℕ) (δ : ℝ) : ℝ :=
  Cρ * Real.sqrt κ * (1 / Real.sqrt n + Real.sqrt (((d : ℝ) + Lδ δ) / ((N : ℝ) * n)))

/-- `λ := ρ²/ε`. -/
noncomputable def lambdaP (ρ ε : ℝ) : ℝ := ρ ^ 2 / ε

end DoubleCorrRME


