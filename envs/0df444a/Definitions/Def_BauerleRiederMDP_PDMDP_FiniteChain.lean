-- Prove2me | Definitions.Def_BauerleRiederMDP_PDMDP_FiniteChain
-- name    : BauerleRiederMDP_PDMDP_FiniteChain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:32:11.226344+00:00
-- url     : https://prove2.me/theorems/fde40f8a-c8b6-46f6-a6e1-8e6323b2188b
-- title:
--   Continuous-time Markov Decision Chain with finite horizon: $V_\pi$, $V$ (8.12), $T$ and upper bounding functions
-- statement:
--   A chain **with finite time horizon** $T$ has rate data and a measurable terminal reward $g:E\to\mathbb R$. A Markov policy is $\pi_t=f_n(T_n,Z_n)(t-T_n)$ with $f_n:[0,T]\times E\to A$, and
--   $$
--   V_\pi(t,x):=\mathbb E^\pi_{tx}\Big[\int_t^Tr(X_s,\pi_s)\,ds+g(X_T)\Big],\qquad V(t,x):=\sup_\pi V_\pi(t,x).\tag{8.12}
--   $$
--   The maximal reward operator is
--   $$
--   (Tv)(t,x)=e^{-\lambda(T-t)}g(x)+\int_0^{T-t}e^{-\lambda s}\sup_{u\in U}\Big[r(x,u)+\lambda\sum_{y\in E}v(t+s,y)Q(\{y\}|x,u)\Big]\,ds,
--   $$
--   and $b:E\to\mathbb R_+$ is an **upper bounding function** if there are $c_r,c_g,c_Q\in\mathbb R_+$ with $r^+(x,u)\le c_rb(x)$, $g^+(x)\le c_gb(x)$ and $\sum_yb(y)Q(\{y\}|x,u)\le c_Qb(x)$. The rule of the proof of Theorem 8.3.3 is $f(t,x)(s):=f^*(t+s,x)$.
--
--   **Formalization Note** $V_\pi$ is computed from the law of $(T_n,Z_n)$ started at $(t,x)$. Control functions on $[0,T]$ (8.11) are read from functions on `ℝ`, which loses nothing.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), (8.11)–(8.12), pp.258–259, and p.260

import Mathlib
import Definitions.Def_BauerleRiederMDP_PDMDP_DecisionRule
import Definitions.Def_BauerleRiederMDP_PDMDP_RateModel
import Definitions.Def_BauerleRiederMDP_PDMDP_pathLaw

open MeasureTheory ProbabilityTheory
open MDPFinance.PDMDP (erealIntegral)

namespace BauerleRiederMDP.PDMDP

/-- A continuous-time Markov Decision Chain **with finite time horizon** `T` (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §8.3, p.258,
PDF 269): rate data, the horizon and a measurable terminal reward `g : E → ℝ`. -/
structure FiniteChain (E U : Type*) [MeasurableSpace E] [MeasurableSpace U]
    extends RateModel E U where
  /-- The terminal reward. -/
  g : E → ℝ
  g_measurable : Measurable g
  /-- The time horizon `T`. -/
  horizon : ℝ
  horizon_pos : 0 < horizon

namespace FiniteChain

variable {E U : Type*} [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E]
  [MeasurableSpace U]

/-- The one-step kernel of `(T_n, Z_n)` under `f_n : [0,T] × E → A`: the sojourn is exponential
with rate `λ` and the state stays `Z_n` until the jump, with control action `f_n(T_n,Z_n)(s)`.

**Formalization Note** As in `DecisionRule`, `f_n` is the jointly measurable map
`(s, (t, z)) ↦ f_n(t,z)(s)`. Control functions are read on `[0, T]` only (8.11); a rule on `[0,T]`
extends to `ℝ` measurably, so nothing is lost by its domain. -/
noncomputable def step (C : FiniteChain E U) (f : DecisionRule (ℝ × E) U) :
    Kernel (ℝ × E) (ℝ × E) :=
  jumpStep C.lam C.Q (fun p => (p.1.2, f.1 (p.2, p.1)))
    ((measurable_snd.comp measurable_fst).prodMk (f.2.comp (measurable_snd.prodMk measurable_fst)))

instance (C : FiniteChain E U) (f : DecisionRule (ℝ × E) U) : IsMarkovKernel (C.step f) :=
  isMarkovKernel_jumpStep C.lam_pos _ _ _

/-- `V_π(t,x) := IE^π_{tx}[∫_t^T r(X_s,π_s) ds + g(X_T)]` (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.258, PDF 269) for a Markov
policy `π = (f_n)`, with `X_s = Z_n` and `π_s = f_n(T_n,Z_n)(s - T_n)` on the sojourn containing `s`.

**Formalization Note** The law is that of `(T_n, Z_n)` started from `(T_0, Z_0) = (t, x)`, which is
the conditional law given `X_t = x`. -/
noncomputable def Vpi (C : FiniteChain E U) (π : ℕ → DecisionRule (ℝ × E) U) (t : ℝ) (x : E) :
    EReal :=
  erealIntegral (pathLaw (fun n => C.step (π n)) (t, x)) fun ω =>
    erealIntegral (volume.restrict (Set.Ioc t C.horizon)) (fun s =>
      ((C.r ((ω (jumpIndex ω s)).2,
        (π (jumpIndex ω s)).1 (s - (ω (jumpIndex ω s)).1, ω (jumpIndex ω s))) : ℝ) : EReal)) +
      ((C.g (ω (jumpIndex ω C.horizon)).2 : ℝ) : EReal)

/-- The value function `V(t,x) := sup_π V_π(t,x)`, the supremum over all Markov policies
(Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), eq. (8.12), pp.258–259, PDF 269–270). -/
noncomputable def V (C : FiniteChain E U) (t : ℝ) (x : E) : EReal :=
  ⨆ π : ℕ → DecisionRule (ℝ × E) U, C.Vpi π t x

/-- The maximal reward operator of the finite-horizon chain in the form after pointwise
maximization (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.260, PDF 271):
`(Tv)(t,x) = e^{-λ(T-t)} g(x) + ∫_0^{T-t} e^{-λs} sup_u {r(x,u) + λ ∑_y v(t+s,y) Q({y}|x,u)} ds`. -/
noncomputable def T (C : FiniteChain E U) (v : ℝ → E → EReal) (t : ℝ) (x : E) : EReal :=
  ((Real.exp (-C.lam * (C.horizon - t)) * C.g x : ℝ) : EReal) +
    erealIntegral (volume.restrict (Set.Ioc (0 : ℝ) (C.horizon - t))) fun s =>
      ((Real.exp (-C.lam * s) : ℝ) : EReal) *
        ⨆ u, ((C.r (x, u) : ℝ) : EReal) + (C.lam : EReal) * erealIntegral (C.Q (x, u)) (v (t + s))

/-- An **upper bounding function** for the finite-horizon chain (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.260, PDF 271): there are
`c_r, c_g, c_Q ∈ ℝ₊` with (i) `r⁺(x,u) ≤ c_r b(x)`, (ii) `g⁺(x) ≤ c_g b(x)`,
(iii) `∑_y b(y) Q({y}|x,u) ≤ c_Q b(x)`. -/
def IsUpperBounding (C : FiniteChain E U) (b : E → ℝ) : Prop :=
  (∀ x, 0 ≤ b x) ∧ ∃ cr cg cQ : ℝ, 0 ≤ cr ∧ 0 ≤ cg ∧ 0 ≤ cQ ∧
    (∀ x u, max (C.r (x, u)) 0 ≤ cr * b x) ∧ (∀ x, max (C.g x) 0 ≤ cg * b x) ∧
    ∀ x u, ∫⁻ y, ENNReal.ofReal (b y) ∂(C.Q (x, u)) ≤ ENNReal.ofReal (cQ * b x)

end FiniteChain

/-- The rule of Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), proof of Theorem 8.3.3, p.261, PDF 272: `f(t,x)(s) := f*(t+s,x)`, so that
`π*_t = f*(t, X_{t-})` for `t ∈ (T_n, T_{n+1}]`. -/
def timedRule {E U : Type*} [MeasurableSpace E] [MeasurableSpace U] (f : ℝ × E → U)
    (hf : Measurable f) : DecisionRule (ℝ × E) U :=
  ⟨fun p => f (p.2.1 + p.1, p.2.2),
    hf.comp (((measurable_fst.comp measurable_snd).add measurable_fst).prodMk
      (measurable_snd.comp measurable_snd))⟩

end BauerleRiederMDP.PDMDP


