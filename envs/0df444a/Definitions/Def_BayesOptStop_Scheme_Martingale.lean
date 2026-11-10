-- Prove2me | Definitions.Def_BayesOptStop_Scheme_Martingale
-- name    : BayesOptStop_Scheme_Martingale
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T21:18:07.303839+00:00
-- url     : https://prove2.me/theorems/78975b07-872b-4d25-b8b4-24671f956b74
-- title:
--   Martingales, Doob martingales, dual martingales, dual certificates and the dual update
-- statement:
--   For processes $Z_t$, $t\in[n]$, on the finite path space: $(Z_t)$ is a **martingale** if each $Z_t$ is $F_t$-measurable and $\mathbb E[Z_{t+1}\mid F_t]=Z_t$ almost surely (Definition 1). The **Doob martingale** of a terminal variable $M$ is $Z_t=\mathbb E[M\mid F_t]$. $(Z_t)$ is a **dual martingale** if it is a martingale with $Z_t\ge X_t$ almost surely for every $t\in[n]$, and $M$ is a **dual certificate** if it is $F_n$-measurable and its Doob martingale is a dual martingale (Definition 2). The **dual update** of the Primal-Dual Improvement is $M^+=M\max\{\rho,\alpha\}$ with $\rho=\max_tX_t/Z_t$ (p. 14). "Almost surely" means on every path of positive probability; a ratio with $Z_t=0$ is $0$.
-- source:
--   AmaniHamedani, Aouad, Işık, Kesselheim, Saberi (2026), Bayesian Optimal Stopping: Invincible Prophets and Achievable Philosophers, held STOC 2027 submission, SHA-256 fecfa05a3285ac21a7efbed099d2afed88a382dfcc9d91836b6e5210d70c4241, Definitions 1–2, pp. 9–10; Primal-Dual Improvement, p. 14

import Mathlib
import Definitions.Def_BayesOptStop_Scheme_Model

open scoped BigOperators

namespace BayesOptStop.Scheme

/-!
# Martingales, dual martingales and the dual update (Definitions 1–2, pp. 9–10; §3.2, p. 14)

Source: AmaniHamedani, Aouad, Işık, Kesselheim, Saberi (2026), held STOC 2027 submission,
SHA-256 fecfa05a…c4241, Definitions 1 and 2 (pp. 9–10) and the Primal-Dual Improvement box (p. 14).

A process is a family `Z : ℕ → (Fin n → Fin m) → ℝ`; `Z t` is the paper's `Z_t`, `t ∈ [n]`
(history length `t`). On a finite space every process is integrable. "Almost surely" means
"on every path of positive probability". The dominance `Z_t ≥ X_t` at the paper's time
`t ∈ [n]` reads `Z (s+1) ω ≥ X s ω` at 0-based time `s`.
-/

namespace Instance

variable {K m n : ℕ} (I : Instance K m n)

/-- `f` is `F_t`-measurable: it is constant on every history `h_t`. -/
def Measurable_t (t : ℕ) (f : (Fin n → Fin m) → ℝ) : Prop :=
  ∀ ω ω', I.Agree t ω ω' → f ω = f ω'

/-- Definition 1 (p. 9): `(Z_t)_{t ∈ [n]}` is a martingale for the natural filtration: each
`Z_t` is `F_t`-measurable and `E[Z_{t+1} | F_t] = Z_t` almost surely for `t < n`. -/
def IsMartingale (Z : ℕ → (Fin n → Fin m) → ℝ) : Prop :=
  (∀ t, 1 ≤ t → t ≤ n → I.Measurable_t t (Z t)) ∧
    ∀ t, 1 ≤ t → t < n → ∀ ω, 0 < I.prob ω → I.condExp (Z (t + 1)) t ω = Z t ω

/-- Doob's martingale `Z_t = E[M | F_t]` of a terminal random variable `M` (p. 9). -/
noncomputable def doob (M : (Fin n → Fin m) → ℝ) : ℕ → (Fin n → Fin m) → ℝ :=
  fun t => I.condExp M t

/-- Definition 2 (p. 10): a martingale `(Z_t)` is a dual martingale for `(X_t)` if
`Z_t ≥ X_t` almost surely for every `t ∈ [n]`. -/
def IsDualMartingale (Z : ℕ → (Fin n → Fin m) → ℝ) : Prop :=
  I.IsMartingale Z ∧ ∀ s : Fin n, ∀ ω, 0 < I.prob ω → I.X s ω ≤ Z (s.val + 1) ω

/-- Definition 2 (p. 10): `M` is a dual certificate, i.e. the terminal value `Z_n` of a dual
martingale: `M` is a terminal (`F_n`-measurable) random variable whose Doob martingale is a dual
martingale. -/
def IsDualCertificate (M : (Fin n → Fin m) → ℝ) : Prop :=
  I.Measurable_t n M ∧ I.IsDualMartingale (I.doob M)

/-- `ρ = max_{t ∈ [n]} X_t / Z_t` on a path (p. 14). The ratios are `≥ 0`, so the fold from `0`
is the maximum; a ratio with `Z_t = 0` is `X_t / 0 = 0` (Lean's convention). -/
noncomputable def ratioMax (Z : ℕ → (Fin n → Fin m) → ℝ) (ω : Fin n → Fin m) : ℝ :=
  Finset.univ.fold max 0 (fun s : Fin n => I.X s ω / Z (s.val + 1) ω)

/-- The dual update of the Primal-Dual Improvement (p. 14): `M⁺ = M · max{ρ, α}` with
`ρ = max_t X_t / Z_t` for the Doob martingale `Z_t = E[M | F_t]`. -/
noncomputable def dualUpdate (M : (Fin n → Fin m) → ℝ) (α : ℝ) (ω : Fin n → Fin m) : ℝ :=
  M ω * max (I.ratioMax (I.doob M) ω) α

end Instance

end BayesOptStop.Scheme


