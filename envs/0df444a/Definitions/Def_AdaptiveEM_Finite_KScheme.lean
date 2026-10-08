-- Prove2me | Definitions.Def_AdaptiveEM_Finite_KScheme
-- name    : AdaptiveEM_Finite_KScheme
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T17:06:54.210976+00:00
-- url     : https://prove2.me/theorems/a5ba9bfd-5800-4f4c-b7ef-7ff28a47e7f2
-- title:
--   (34), p. 547 — the projected K-scheme X̂^K, P_K(Y) = min(1, K/‖Y‖)Y, and its interpolants
-- statement:
--   This file defines the auxiliary scheme (34) used in the proof of Theorem 1 of Fang and Giles (2020).
--
--   For $K>0$ the radial projection onto the closed ball of radius $K$ is
--   $$P_K(Y)=\min\Big(1,\frac{K}{\|Y\|}\Big)\,Y .$$
--   With $f,g,h,x_0,W$ as in the scheme (5), the K-scheme starts at $t_0=0$, $\widehat X^K_0=x_0$, uses the step $h_n=h(\widehat X^K_{t_n})$ and sets
--   $$t_{n+1}=t_n+h_n,\qquad \widehat X^K_{t_{n+1}}=P_K\big(\widehat X^K_{t_n}+f(\widehat X^K_{t_n})h_n+g(\widehat X^K_{t_n})(W_{t_{n+1}}-W_{t_n})\big).$$
--   With $\underline t$ the last grid time of this scheme not after $t$, the piecewise constant interpolant is $\overline X^K_t=\widehat X^K_{\underline t}$ and the continuous approximation is
--   $$\widehat X^K_t=P_K\big(\widehat X^K_{\underline t}+f(\widehat X^K_{\underline t})(t-\underline t)+g(\widehat X^K_{\underline t})(W_t-W_{\underline t})\big).$$
--
--   Every state of the K-scheme lies in the ball of radius $K$ (for $K>\|x_0\|$). The proof of Theorem 1 bounds its moments uniformly in $K$ and lets $K\to\infty$.
--
--   **Formalization Note** At $Y=0$ the Lean convention $K/0=0$ gives $P_K(0)=0$, the correct value. The paper writes $h_n$ for the K-scheme's steps; they are read as $h(\widehat X^K_{t_n})$, which is what makes the paper's remark that $\inf_{\|x\|\le K}h(x)>0$ implies attainability of $T$ meaningful. The K-scheme has its own grid, defined pathwise like that of (5), with the same junk index $0$ if the grid never passes $t$.
-- source:
--   Fang, Giles, Adaptive Euler–Maruyama method for SDEs with nonglobally Lipschitz drift, Ann. Appl. Probab. 30 (2020), p. 547, §6.1 Step 1, (34)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting
import Definitions.Def_AdaptiveEM_Finite_Scheme

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace AdaptiveEM.Finite

open EthierKurtz

/-- Fang–Giles (2020), p. 547: the radial projection `P_K(Y) = min(1, K/‖Y‖) Y` onto the closed
ball of radius `K`. At `Y = 0` Lean's `K / 0 = 0` gives `P_K(0) = 0`, the correct value. -/
noncomputable def PK {m : ℕ} (K : ℝ) (y : SDEState m) : SDEState m :=
  min 1 (K / ‖y‖) • y

/-- Fang–Giles (2020), (34), p. 547: the K-scheme on its own random grid.
`gridK … K n ω = (t_n, X̂^K_{t_n})` with `t_0 = 0`, `X̂^K_0 = x0`,
`t_{n+1} = t_n + h(X̂^K_{t_n})`,
`X̂^K_{t_{n+1}} = P_K(X̂^K_{t_n} + f(X̂^K_{t_n}) h(X̂^K_{t_n}) + g(X̂^K_{t_n}) (W_{t_{n+1}} - W_{t_n}))`. -/
noncomputable def gridK {m d : ℕ} {Ω : Type*} (f : SDEState m → SDEState m)
    (g : SDEState m → SabanisEuler.Shared.Diffusion m d) (h : SDEState m → ℝ)
    (x0 : SDEState m) (W : ℝ≥0 → Ω → SDEState d) (K : ℝ) : ℕ → Ω → ℝ≥0 × SDEState m
  | 0, _ => (0, x0)
  | n + 1, ω =>
    let p := gridK f g h x0 W K n ω
    let t' := p.1 + (h p.2).toNNReal
    (t', PK K (p.2 + h p.2 • f p.2 + mulVec (g p.2) (W t' ω - W p.1 ω)))

/-- The index `n_t` of the last K-scheme grid time not after `t` (junk `0` if the grid never
passes `t`). -/
noncomputable def idxK {m d : ℕ} {Ω : Type*} (f : SDEState m → SDEState m)
    (g : SDEState m → SabanisEuler.Shared.Diffusion m d) (h : SDEState m → ℝ)
    (x0 : SDEState m) (W : ℝ≥0 → Ω → SDEState d) (K : ℝ) (t : ℝ≥0) (ω : Ω) : ℕ := by
  classical
  exact if H : ∃ n, t < (gridK f g h x0 W K (n + 1) ω).1 then Nat.find H else 0

/-- `t̲` for the K-scheme grid. -/
noncomputable def tlowK {m d : ℕ} {Ω : Type*} (f : SDEState m → SDEState m)
    (g : SDEState m → SabanisEuler.Shared.Diffusion m d) (h : SDEState m → ℝ)
    (x0 : SDEState m) (W : ℝ≥0 → Ω → SDEState d) (K : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  (gridK f g h x0 W K (idxK f g h x0 W K t ω) ω).1

/-- `X̄^K_t = X̂^K_{t̲}`. -/
noncomputable def XbarK {m d : ℕ} {Ω : Type*} (f : SDEState m → SDEState m)
    (g : SDEState m → SabanisEuler.Shared.Diffusion m d) (h : SDEState m → ℝ)
    (x0 : SDEState m) (W : ℝ≥0 → Ω → SDEState d) (K : ℝ) (t : ℝ≥0) (ω : Ω) : SDEState m :=
  (gridK f g h x0 W K (idxK f g h x0 W K t ω) ω).2

/-- Fang–Giles (2020), p. 547: the continuous K-scheme approximation
`X̂^K_t = P_K(X̂^K_{t̲} + f(X̂^K_{t̲}) (t - t̲) + g(X̂^K_{t̲}) (W_t - W_{t̲}))`. -/
noncomputable def XhatK {m d : ℕ} {Ω : Type*} (f : SDEState m → SDEState m)
    (g : SDEState m → SabanisEuler.Shared.Diffusion m d) (h : SDEState m → ℝ)
    (x0 : SDEState m) (W : ℝ≥0 → Ω → SDEState d) (K : ℝ) (t : ℝ≥0) (ω : Ω) : SDEState m :=
  PK K (XbarK f g h x0 W K t ω +
    ((t : ℝ) - (tlowK f g h x0 W K t ω : ℝ)) • f (XbarK f g h x0 W K t ω) +
    mulVec (g (XbarK f g h x0 W K t ω)) (W t ω - W (tlowK f g h x0 W K t ω) ω))

end AdaptiveEM.Finite


