-- Prove2me | Definitions.Def_DynkinAsymInfo_Linear_Game
-- name    : DynkinAsymInfo_Linear_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:16:35.57779+00:00
-- url     : https://prove2.me/theorems/9c436734-e6d2-4711-8c89-8955ac4fda3b
-- title:
--   §2–§3 — admissible controls, randomised stops, payoffs, and filtering
-- statement:
--   Player 1 chooses an almost surely finite $\mathcal F^X$ stopping time $\tau$. Player 2 chooses an $\mathcal F^{X,\theta}$ adapted, almost surely right continuous and nondecreasing process $\Gamma$ taking values in $[0,1]$, with $\Gamma_{0-}=0$. The randomised stopping time is
--   $$\gamma_\Gamma=\inf\{t\ge0:\Gamma_t>U\}.$$
--   For nonnegative continuous payoffs $0\le f\le g$, the realised amount is $f(X_\tau)$ if $\tau<\gamma_\Gamma$ and $g(X_{\gamma_\Gamma})$ if $\gamma_\Gamma\le\tau$; it is zero if both times are infinite. Its expectation $J(\tau,\Gamma)$ is a nonnegative extended integral. A saddle point satisfies $J(\tau,\Gamma^*)\le J(\tau^*,\Gamma^*)\le J(\tau^*,\Gamma)$ against every admissible strategy.
--
--   The odds process $\Phi$, posterior $\Pi=\Phi/(1+\Phi)$, conditional laws $P^i=P(\cdot\mid\theta=i)$, interim payoffs $J^i$, and scaled payoff $\widehat J=(1+\phi)J$ with $\phi=\pi/(1-\pi)$ are also defined. $J^i$ uses a Stieltjes integral whose atom at zero is included.
--
--   **Formalization Note.** Payoffs use $[0,\infty]$ to avoid an integrability default. Ties pay $g$. The strict inequality in the randomised time is literal. On paths that fail the Stieltjes regularity conditions, its measure is set to zero.
-- source:
--   De Angelis, Ekström, Glover, Dynkin Games with Incomplete and Asymmetric Information, arXiv:1810.07674v5, pp. 4–11, (2)–(5), (8), (19), (23), (27)–(29)

import Mathlib
import Definitions.Def_DynkinAsymInfo_Linear_AbstractGame
import Definitions.Def_DynkinAsymInfo_Linear_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DynkinAsymInfo.Linear
set_option autoImplicit false
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The §2 GBM model as an instance of the abstract two-filtration game. -/
noncomputable def gameFrame (p : Params) (st : Setting Ω) (x pi : ℝ) :
    RandomisedDynkinFrame Ω where
  P := st.P
  Fmax := FX p st x pi
  Fmin := FXTheta p st x pi
  U := st.U
  Y := X p st x pi

/-- Admissible observation stopping times, §2, p. 4. -/
def InT (p : Params) (st : Setting Ω) (x pi : ℝ)
    (tau : Ω → WithTop ℝ≥0) : Prop :=
  (gameFrame p st x pi).InT tau

/-- Admissible controls for either of the §2 filtrations, p. 4. -/
def InA (st : Setting Ω) (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (G : ℝ≥0 → Ω → ℝ) : Prop :=
  (⟨st.P, F, F, st.U, fun _ _ => 0⟩ : RandomisedDynkinFrame Ω).InA F G

/-- The pair of type-conditional controls, composed according to the hidden type (§2, p. 5). -/
noncomputable def mixControl (st : Setting Ω) (pi : ℝ)
    (G0 G1 : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (a : Ω) : ℝ :=
  if hiddenType st pi a = 0 then G0 t a else G1 t a

/-- The strict randomised crossing time, (2), p. 5. -/
noncomputable def randST (st : Setting Ω) (G : ℝ≥0 → Ω → ℝ) (a : Ω) :
    WithTop ℝ≥0 :=
  randomisedTime st.U G a

/-- The realised §2 GBM payoff, with `g` paid on finite ties. -/
noncomputable def pay (p : Params) (st : Setting Ω) (x pi : ℝ)
    (f g : ℝ → ℝ) (tau gamma : Ω → WithTop ℝ≥0) (a : Ω) : ℝ≥0∞ :=
  (gameFrame p st x pi).pay f g tau gamma a

/-- The GBM ex-ante payoff (5), p. 5. -/
noncomputable def J (p : Params) (st : Setting Ω) (x pi : ℝ) (f g : ℝ → ℝ)
    (tau : Ω → WithTop ℝ≥0) (G : ℝ≥0 → Ω → ℝ) : ℝ≥0∞ :=
  (gameFrame p st x pi).J f g tau G

/-- The GBM ex-ante saddle point, Definition 2.4, p. 5. -/
def IsSaddle (p : Params) (st : Setting Ω) (x pi : ℝ) (f g : ℝ → ℝ)
    (taus : Ω → WithTop ℝ≥0) (Gs : ℝ≥0 → Ω → ℝ) : Prop :=
  (gameFrame p st x pi).IsSaddle f g taus Gs

/-- Closed likelihood ratio (19), (23), pp. 9, 18, in the GBM instance. -/
noncomputable def Phi (p : Params) (st : Setting Ω) (x pi : ℝ)
    (t : ℝ≥0) (a : Ω) : ℝ :=
  let phi := pi / (1 - pi)
  phi * Real.exp ((signalNoise p / p.sigma) *
    (Real.log (X p st x pi t a / x) - (p.mu0 - p.sigma ^ 2 / 2) * (t : ℝ)) -
    signalNoise p ^ 2 * (t : ℝ) / 2)

/-- Posterior probability (8), p. 7. -/
noncomputable def Pi (p : Params) (st : Setting Ω) (x pi : ℝ)
    (t : ℝ≥0) (a : Ω) : ℝ :=
  Phi p st x pi t a / (1 + Phi p st x pi t a)

/-- The conditional law `P^i=P(·|θ=i)`, p. 9. -/
noncomputable def Ptype (st : Setting Ω) (pi i : ℝ) : Measure Ω :=
  ProbabilityTheory.cond st.P {a | hiddenType st pi a = i}

/-- The Stieltjes measure of a monotone right-continuous path on nonnegative time.
Outside that path class it is the zero measure. -/
noncomputable def pathStieltjes (G : ℝ≥0 → ℝ) : StieltjesFunction ℝ≥0 := by
  classical
  exact if h : Monotone G ∧ ∀ t, ContinuousWithinAt G (Set.Ici t) t then
    { toFun := G, mono' := h.1, right_continuous' := h.2 }
  else StieltjesFunction.const ℝ≥0 0

/-- The Stieltjes integral `∫₀^τ h(t)dΓ_t`, pp. 7, 10, with the jump at
zero counted explicitly. For `τ=∞`, the integral runs over `(0,∞)`. -/
noncomputable def stInt (h G : ℝ≥0 → ℝ) (tau : WithTop ℝ≥0) : ℝ≥0∞ :=
  ENNReal.ofReal (h 0 * G 0) +
    if tau = ⊤ then
      ∫⁻ t in Set.Ioi (0 : ℝ≥0), ENNReal.ofReal (h t) ∂(pathStieltjes G).measure
    else
      ∫⁻ t in Set.Ioc (0 : ℝ≥0) tau.untopA,
        ENNReal.ofReal (h t) ∂(pathStieltjes G).measure

/-- The interim payoff (27)–(28), pp. 10–11, under the conditional law of type i. -/
noncomputable def Ji (p : Params) (st : Setting Ω) (x pi i : ℝ) (f g : ℝ → ℝ)
    (tau : Ω → WithTop ℝ≥0) (G : ℝ≥0 → Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ a, (if tau a = ⊤ then 0 else
      ENNReal.ofReal ((1 - G (tau a).untopA a) *
        f (X p st x pi (tau a).untopA a))) +
    stInt (fun t => g (X p st x pi t a)) (fun t => G t a) (tau a) ∂(Ptype st pi i)

noncomputable def J0 (p : Params) (st : Setting Ω) (x pi : ℝ) (f g : ℝ → ℝ)
    (tau : Ω → WithTop ℝ≥0) (G : ℝ≥0 → Ω → ℝ) : ℝ≥0∞ :=
  Ji p st x pi 0 f g tau G

noncomputable def J1 (p : Params) (st : Setting Ω) (x pi : ℝ) (f g : ℝ → ℝ)
    (tau : Ω → WithTop ℝ≥0) (G : ℝ≥0 → Ω → ℝ) : ℝ≥0∞ :=
  Ji p st x pi 1 f g tau G

/-- The scaled ex-ante payoff `(1+ϕ)J`, (29), p. 11, where `ϕ=π/(1-π)`. -/
noncomputable def Jhat (p : Params) (st : Setting Ω) (x pi : ℝ) (f g : ℝ → ℝ)
    (tau : Ω → WithTop ℝ≥0) (G : ℝ≥0 → Ω → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 + pi / (1 - pi)) * J p st x pi f g tau G

end DynkinAsymInfo.Linear


