-- Prove2me | Definitions.Def_RiskStopTC_tauStar
-- name    : RiskStopTC_tauStar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:35:09.438784+00:00
-- url     : https://prove2.me/theorems/f7a80b13-add3-4577-ae50-5e09a80a9010
-- title:
--   The first time the Snell envelope meets the reward, $\tau^*_m=\min\{t\ge m: E_t=Z_t\}$ (5.16)
-- statement:
--   For $m\in\{0,\dots,T\}$ and $\omega\in\Omega$,
--   $$\tau^*_m(\omega):=\min\{t:\ E_t(\omega)=Z_t(\omega),\ m\le t\le T\}.$$
--   The set is nonempty since $E_T=Z_T$, so $m\le\tau^*_m\le T$.
--
--   Theorem 5.6 shows that $\tau^*_m$ is an optimal stopping time for the problem started at $m$.
--
--   **Formalization Note** Defined as the least $t\ge m$ with $E_t(\omega)=Z_t(\omega)$ or $t\ge T$; for $m\le T$ this is exactly (5.16) (it is never $\top$ and never a default value). For $m>T$ (not used by the paper) it is $m$. The value is cast to `WithTop ℕ`.
-- source:
--   Pichler, Liu & Shapiro, Risk averse stochastic programming: time consistency and optimal stopping, arXiv:1808.10807v3, equation (5.16), p.20

import Mathlib
import Definitions.Def_RiskStopTC_snell

namespace RiskStopTC

/-- **The candidate stopping time (5.16).** Pichler, Liu & Shapiro, arXiv:1808.10807v3, p.20:
"τ∗m(ω) := min{t : Et(ω) = Zt(ω), m ≤ t ≤ T}, ω ∈ Ω."

`tauStar ϱ Z T m ω` is the least `t ≥ m` such that `E_t(ω) = Z_t(ω)` or `t ≥ T`.

**Formalization Note.** For `m ≤ T` this is exactly (5.16): `t = T` qualifies (and `E_T = Z_T`
holds pointwise), so the least qualifying `t` lies in `[m, T]` and is the least `t ∈ [m, T]` with
`E_t(ω) = Z_t(ω)`. It is never `⊤` and never a default value. For `m > T` (not used by the
paper) it is `m`. The value is cast to `WithTop ℕ`, the type of Mathlib's stopping times. -/
noncomputable def tauStar {Ω : Type*} (ϱ : ℕ → (Ω → ℝ) → Ω → ℝ) (Z : ℕ → Ω → ℝ) (T m : ℕ)
    (ω : Ω) : WithTop ℕ :=
  ((@Nat.find (fun t => m ≤ t ∧ (snell ϱ Z T t ω = Z t ω ∨ T ≤ t))
    (fun _ => Classical.propDecidable _)
    ⟨max m T, le_max_left m T, Or.inr (le_max_right m T)⟩ : ℕ) : WithTop ℕ)

end RiskStopTC


