-- Prove2me | Definitions.Def_DynkinIncInfo_Saddle_Game
-- name    : DynkinIncInfo_Saddle_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:12:18.568257+00:00
-- url     : https://prove2.me/theorems/8097aff7-b9ad-4459-a3e3-f81292155b8b
-- title:
--   (1.3)–(1.4), (3.6)–(3.7), pp. 2–3, 8 — the payoff M, the upper and lower values, V, saddle points, the entry times γ* and τ*
-- statement:
--   This file instantiates the general Dynkin game (`DynkinGame`) as the game call option of the paper, and defines its candidate equilibrium.
--
--   For stopping times $\tau,\gamma$ (with values in $[0,\infty]$), the buyer exercises at $\tau$ and the seller cancels at $\gamma$. The expected discounted payoff is
--   $$M_{x,y}(\tau,\gamma)=\mathbb E\big[e^{-r\tau}G_1(S_\tau)\mathbf 1_{\{\tau\le\gamma\}}+e^{-r\gamma}G_2(S_\gamma)\mathbf 1_{\{\gamma<\tau\}}\big],$$
--   with the convention that the payoff is $0$ on $\{\tau\wedge\gamma=\infty\}$ (p. 3). The upper and lower values are
--   $$\overline V(x,y)=\inf_{\gamma}\sup_{\tau}M_{x,y}(\tau,\gamma),\qquad \underline V(x,y)=\sup_{\tau}\inf_{\gamma}M_{x,y}(\tau,\gamma),$$
--   over $\overline{\mathcal F}^S$-stopping times, and $V(x,y):=\overline V(x,y)$. A pair $(\tau_*,\gamma_*)$ is a **saddle point** if both are stopping times and
--   $$M_{x,y}(\tau,\gamma_*)\le M_{x,y}(\tau_*,\gamma_*)\le M_{x,y}(\tau_*,\gamma)\quad\text{for all stopping times }\tau,\gamma.$$
--
--   The **entry times** of the observed state $(X_t,Y_t)=(S_t,Y_t)$ into the two stopping regions are
--   $$\gamma_*(x,y)=\inf\{t\ge0\mid G_2(X_t)\le V(X_t,Y_t)\},\qquad \tau_*(x,y)=\inf\{t\ge0\mid V(X_t,Y_t)\le G_1(X_t)\},$$
--   with $\inf\emptyset=+\infty$ ((3.6)–(3.7)). The discounted value process is $e^{-rt}V(X_t,Y_t)$.
--
--   **Formalization Note.** The payoff processes are $L_t=e^{-rt}G_1(S_t)$ and $U_t=e^{-rt}G_2(S_t)$. $M$ is the Lebesgue integral of the nonnegative payoff, valued in $[0,\infty]$: the payoffs are not uniformly integrable ((1.5)), so no integrability is presupposed. $V$ is the real number $\overline V(x,y)$, which is finite because $\overline V(x,y)\le G_2(x)$ (take $\gamma\equiv0$). The entry times are Mathlib's `hittingAfter … 0`, which is $\top$ when the set is never reached.
-- source:
--   De Angelis, Gensbittel, Villeneuve, A Dynkin Game on Assets with Incomplete Information on the Return, arXiv:1705.07352v4, pp. 2–3, (1.3), the zero-payoff convention, (1.4) and the saddle-point definition; p. 8, (3.6)–(3.7)

import Mathlib
import Definitions.Def_DynkinIncInfo_Saddle_DynkinGame
import Definitions.Def_DynkinIncInfo_Saddle_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DynkinIncInfo.Saddle

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The buyer's discounted exercise payoff process `e^{−rt} G1(S_t)` ((1.3), p. 2,
arXiv:1705.07352v4), as a nonnegative extended real. -/
noncomputable def L1 (p : Params) (st : Setting Ω) (x y : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-p.r * (t : ℝ)) * G1 p (S p st x y t ω))

/-- The seller's discounted cancellation cost process `e^{−rt} G2(S_t)` ((1.3), p. 2,
arXiv:1705.07352v4), as a nonnegative extended real. -/
noncomputable def U2 (p : Params) (st : Setting Ω) (x y : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-p.r * (t : ℝ)) * G2 p (S p st x y t ω))

/-- **The expected payoff** `M_{x,y}(τ, γ) = E[e^{−rτ}G1(S_τ)1{τ≤γ} + e^{−rγ}G2(S_γ)1{γ<τ}]`
((1.3), p. 2, arXiv:1705.07352v4), with payoff `0` on `{τ ∧ γ = ∞}` (p. 3): the Dynkin game
`dynkinM` with payoff processes `L1`, `U2`.

**Formalization Note.** `M` is the Lebesgue (`lintegral`) integral of the nonnegative payoff,
valued in `ℝ≥0∞`; no integrability is presupposed (the payoffs are not uniformly integrable,
(1.5), p. 3). Stopping times take values in `WithTop ℝ≥0`. -/
noncomputable def M (p : Params) (st : Setting Ω) (x y : ℝ) (τ γ : Ω → WithTop ℝ≥0) : ℝ≥0∞ :=
  dynkinM st.P (L1 p st x y) (U2 p st x y) τ γ

/-- **The upper value** `V̄(x, y) = inf_γ sup_τ M_{x,y}(τ, γ)` over `𝓕̄^S`-stopping times
((1.4), p. 3, arXiv:1705.07352v4). -/
noncomputable def Vup (p : Params) (st : Setting Ω) (x y : ℝ) : ℝ≥0∞ :=
  dynkinUpper (FS p st x y) st.P (L1 p st x y) (U2 p st x y)

/-- **The lower value** `V̲(x, y) = sup_τ inf_γ M_{x,y}(τ, γ)` over `𝓕̄^S`-stopping times
((1.4), p. 3, arXiv:1705.07352v4). -/
noncomputable def Vlow (p : Params) (st : Setting Ω) (x y : ℝ) : ℝ≥0∞ :=
  dynkinLower (FS p st x y) st.P (L1 p st x y) (U2 p st x y)

/-- **The value** `V(x, y)` (p. 3 and Theorem 3.2, p. 8, arXiv:1705.07352v4), taken as the real
number `V̄(x, y)`.

**Formalization Note.** `V̄(x, y) ≤ G2(x) < ∞` (take `γ ≡ 0`), so `toReal` loses nothing. -/
noncomputable def V (p : Params) (st : Setting Ω) (x y : ℝ) : ℝ := (Vup p st x y).toReal

/-- **Saddle point** (p. 3, arXiv:1705.07352v4): `τs`, `γs` are `𝓕̄^S`-stopping times and
`M(τ, γs) ≤ M(τs, γs) ≤ M(τs, γ)` for all `𝓕̄^S`-stopping times `τ`, `γ`. `τs` is the buyer's
(maximiser's) time, `γs` the seller's (minimiser's). -/
def IsSaddle (p : Params) (st : Setting Ω) (x y : ℝ) (τs γs : Ω → WithTop ℝ≥0) : Prop :=
  IsDynkinSaddle (FS p st x y) st.P (L1 p st x y) (U2 p st x y) τs γs

/-- The observed state process `(X_t, Y_t) = (S_t, Y_t)`. -/
noncomputable def state (p : Params) (st : Setting Ω) (x y : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ × ℝ :=
  (S p st x y t ω, Y p st x y t ω)

/-- **The seller's entry time** `γ*(x, y) = inf{t ≥ 0 | G2(X_t) ≤ V(X_t, Y_t)}`, `inf ∅ = +∞`
((3.6), p. 8, arXiv:1705.07352v4). -/
noncomputable def γstar (p : Params) (st : Setting Ω) (x y : ℝ) : Ω → WithTop ℝ≥0 :=
  hittingAfter (state p st x y) {q : ℝ × ℝ | G2 p q.1 ≤ V p st q.1 q.2} 0

/-- **The buyer's entry time** `τ*(x, y) = inf{t ≥ 0 | V(X_t, Y_t) ≤ G1(X_t)}`, `inf ∅ = +∞`
((3.7), p. 8, arXiv:1705.07352v4). -/
noncomputable def τstar (p : Params) (st : Setting Ω) (x y : ℝ) : Ω → WithTop ℝ≥0 :=
  hittingAfter (state p st x y) {q : ℝ × ℝ | V p st q.1 q.2 ≤ G1 p q.1} 0

/-- The discounted value process `e^{−rt} V(X_t, Y_t)` (Theorem 3.2, p. 8,
arXiv:1705.07352v4). -/
noncomputable def discV (p : Params) (st : Setting Ω) (x y : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (-p.r * (t : ℝ)) * V p st (S p st x y t ω) (Y p st x y t ω)

end DynkinIncInfo.Saddle


