-- Prove2me | Definitions.Def_MeanOnlyProphet_Rq
-- name    : MeanOnlyProphet_Rq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:26:14.81299+00:00
-- url     : https://prove2.me/theorems/dc495b56-9266-4a05-831b-c99bf88b9144
-- title:
--   One-step quantities $p$, $u$, $I_q$, $E_q$, $I_r$, $R_q$, $\phi_j$, $y_j$, $x_j$
-- statement:
--   Fix $t=k/N_t$, $\Delta=1/N_t$, a state $0\le x<y\le1$, and write $b$ for the constant drop rate on $[t,t+\Delta]$. Define
--   1. $p=c\,x+y(1-\theta(t)-b)$ and $u=b(1-y+t\,y)$;
--   2. $I_q=\int_t^{t+\Delta}S_t(s)\,ds$, $E_q=\int_t^{t+\Delta}e^{-q(s)}\,ds$ and, for $r\ge0$, $I_r=\int_0^\Delta e^{-r s}\,ds$;
--   3. $R_q=p\,I_q-y\,b\int_t^{t+\Delta}S_t(s)\log S_t(s)\,ds+u\,E_q+y\,b\,I_q\,E_q$;
--   4. for $\rho=r_{j-1}$: $\phi_j=1-y+y\big(t+I_{\rho}+e^{-\Delta\rho}(1-t-\Delta)\big)$, $y_j=y\,e^{-\Delta\rho}/\phi_j$ and
--   $$
--   x_j=\min\left\{y_j,\ \frac{e^{-\Delta\rho}\big(c\,x+y\,b\,\Delta(\rho+e^{-\rho}-1)\big)}{c\,\phi_j}\right\}.
--   $$
--   They give the one-step recursion $V_t(y,x)\ge\min_j\{a_j+\phi_jV_{t+\Delta}(y_j,x_j)\}$ that the certificate of §3.3 evaluates.
--
--   **Formalization Note** The constant drop rate on $[t,t+\Delta]$ is read as $b(t)$. $S_t>0$, so the logarithm is the true one.
-- source:
--   Feng, Jin, Wu, Xiang, Mean-only Prophet Inequalities, arXiv:2610.24711 (held version, sha256 c68bfec4…74e93a), App. A.1, p.25 (PDF p.26)

import Mathlib
import Definitions.Def_MeanOnlyProphet_Vinf

namespace MeanOnlyProphet

/-- **`p = c · x + y · (1 − θ(t) − b)`.** Feng, Jin, Wu, Xiang, *Mean-only Prophet Inequalities*,
arXiv:2610.24711 (held version, sha256 c68bfec4…), App. A.1, p.25 (PDF p.26). Here `b` is the constant
drop rate on `[t, t + ∆]`, read as `b t`. -/
noncomputable def pCoef (b : ℝ → ℝ) (c t y x : ℝ) : ℝ :=
  c * x + y * (1 - thetaOf b t - b t)

/-- **`u = b · (1 − y + t · y)`.** Feng, Jin, Wu, Xiang, arXiv:2610.24711 (held version), App. A.1,
p.25 (PDF p.26); `b` is read as `b t`. -/
noncomputable def uCoef (b : ℝ → ℝ) (t y : ℝ) : ℝ :=
  b t * (1 - y + t * y)

/-- **`I_q = ∫_t^{t+∆} S_t(s) ds`.** App. A.1, p.25 (PDF p.26) of Feng, Jin, Wu, Xiang,
arXiv:2610.24711 (held version). -/
noncomputable def Iq (q : ℝ → ℝ) (t Δ : ℝ) : ℝ :=
  ∫ s in t..t + Δ, survFrom q t s

/-- **`E_q = ∫_t^{t+∆} e^{−q(s)} ds`.** App. A.1, p.25 (PDF p.26) of Feng, Jin, Wu, Xiang,
arXiv:2610.24711 (held version). -/
noncomputable def Eexp (q : ℝ → ℝ) (t Δ : ℝ) : ℝ :=
  ∫ s in t..t + Δ, Real.exp (-q s)

/-- **`I_r = ∫_0^∆ e^{−r·s} ds`** (the value of `I_q` at the constant rate `r`). App. A.1, p.25 (PDF
p.26) of Feng, Jin, Wu, Xiang, arXiv:2610.24711 (held version). -/
noncomputable def Ir (r Δ : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..Δ, Real.exp (-r * s)

/-- **`R_q = p · I_q − y · b · ∫_t^{t+∆} S_t(s) · log S_t(s) ds + u · E_q + y · b · I_q · E_q`.** Feng,
Jin, Wu, Xiang, *Mean-only Prophet Inequalities*, arXiv:2610.24711 (held version, sha256 c68bfec4…), App.
A.1, p.25 (PDF p.26).

**Formalization Note.** `b` (the constant drop rate on `[t, t + ∆]`) is read as `b t`. `S_t(s) > 0`
always, so `Real.log` is the true logarithm here. -/
noncomputable def Rq (b : ℝ → ℝ) (c t Δ y x : ℝ) (q : ℝ → ℝ) : ℝ :=
  pCoef b c t y x * Iq q t Δ
    - y * b t * ∫ s in t..t + Δ, survFrom q t s * Real.log (survFrom q t s)
    + uCoef b t y * Eexp q t Δ + y * b t * Iq q t Δ * Eexp q t Δ

/-- **`ϕ_j = 1 − y + y · (t + I_{r_{j−1}} + e^{−∆·r_{j−1}} · (1 − t − ∆))`**, written for
`ρ = r_{j−1}`. Feng, Jin, Wu, Xiang, arXiv:2610.24711 (held version), App. A.1, p.25 (PDF p.26). -/
noncomputable def phiJ (t Δ y ρ : ℝ) : ℝ :=
  1 - y + y * (t + Ir ρ Δ + Real.exp (-Δ * ρ) * (1 - t - Δ))

/-- **`y_j = y · e^{−∆·r_{j−1}} / ϕ_j`**, written for `ρ = r_{j−1}`. Feng, Jin, Wu, Xiang,
arXiv:2610.24711 (held version), App. A.1, p.25 (PDF p.26). -/
noncomputable def yJ (t Δ y ρ : ℝ) : ℝ :=
  y * Real.exp (-Δ * ρ) / phiJ t Δ y ρ

/-- **`x_j = min{y_j, e^{−∆·r_{j−1}} · (c · x + y · b · ∆ · (r_{j−1} + e^{−r_{j−1}} − 1)) / (c · ϕ_j)}`**,
written for `ρ = r_{j−1}`, with `b` read as `b t`. Feng, Jin, Wu, Xiang, arXiv:2610.24711 (held
version), App. A.1, p.25 (PDF p.26). -/
noncomputable def xJ (b : ℝ → ℝ) (c t Δ y x ρ : ℝ) : ℝ :=
  min (yJ t Δ y ρ)
    (Real.exp (-Δ * ρ) * (c * x + y * b t * Δ * (ρ + Real.exp (-ρ) - 1)) / (c * phiJ t Δ y ρ))

end MeanOnlyProphet


