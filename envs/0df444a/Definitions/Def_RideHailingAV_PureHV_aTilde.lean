-- Prove2me | Definitions.Def_RideHailingAV_PureHV_aTilde
-- name    : RideHailingAV_PureHV_aTilde
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:53:19.607203+00:00
-- url     : https://prove2.me/theorems/357dfd2b-0275-432a-a762-3897a7697072
-- title:
--   The constant $\tilde a$ of Lemma 1
-- statement:
--   For the ETA function $t_1(s)=as^{-r}$, the constant
--   $$\tilde a=r^{\frac1{r+1}}a^{\frac1{r+1}}+r^{-\frac{r}{r+1}}a^{\frac1{r+1}}$$
--   is the coefficient in the closed form $\underline n(d)=\tilde a d^{1/(r+1)}+t_2 d$ of the minimal supply (Lemma 1).
--
--   **Formalization Note** Real powers are evaluated with Lean's conventions $0^1=0$ and $0^0=1$, so at $r=0$ the constant is $\tilde a=a$. This is the paper's value at $r=0$: there $t_1\equiv a$ and $\underline n(d)=(a+t_2)d$, consistent with eq. (45), which uses $\tilde a+t_2$ at $r=0$.
-- source:
--   Lian, van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), Lemma 1, Item 1, p. 38

import Mathlib
import Definitions.Def_RideHailingAV_PureHV_Market

namespace RideHailingAV.PureHV

/-- **The constant `ã` of Lemma 1.** Lian, van Ryzin, *Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of
Market Configuration*, SSRN 3716491 (version of 23 August 2023), Lemma 1, Item 1, p. 38:
`ã = r^(1/(r+1)) a^(1/(r+1)) + r^(−r/(r+1)) a^(1/(r+1))`.

**Formalization Note.** Real powers are `Real.rpow`. At `r = 0` Lean evaluates `0 ^ 1 = 0`
and `0 ^ (−0) = 0 ^ 0 = 1`, so `ã = a`, which is the paper's value at `r = 0`: then
`t₁ ≡ a` and `n(d) = (a + t₂) d` (eq. (45), p. 45 uses `ã + t₂` at `r = 0`). -/
noncomputable def aTilde (M : Market) : ℝ :=
  M.r ^ (1 / (M.r + 1)) * M.a ^ (1 / (M.r + 1)) + M.r ^ (-M.r / (M.r + 1)) * M.a ^ (1 / (M.r + 1))

end RideHailingAV.PureHV


