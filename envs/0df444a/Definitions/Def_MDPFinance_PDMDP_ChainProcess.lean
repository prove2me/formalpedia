-- Prove2me | Definitions.Def_MDPFinance_PDMDP_ChainProcess
-- name    : MDPFinance_PDMDP_ChainProcess
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:07:39.969795+00:00
-- url     : https://prove2.me/theorems/60c11f75-09a9-4332-91d7-f63923f47d93
-- title:
--   A realization of the finite-horizon chain and its value V (Eq. before Theorem 8.3.2)
-- statement:
--   The finite-horizon analogue of `PDMDPRealization`, adapted to the countable-state chain: a probability space carrying absolute jump times $T_n$ (started at $T_0=t_0$) and post-jump states $Z_n$ (started at $Z_0=x$), whose conditional law matches the chain's own uniformized jump mechanism. Since the chain's flow is trivial, the state process is simply $X_t = Z_n$ for $t \in [T_n,T_{n+1})$ — no ODE/flow data is needed, unlike `PDMDPRealization`. $V^\pi(t_0,x) := \mathbb E^\pi_{t_0,x}\big[\int_{t_0}^{Th}r(X_s,\pi_s)\,ds + g(X_{Th})\big]$ is the resulting genuine expectation, matching the book's own definition immediately preceding Theorem 8.3.2.
--
--   **Formalization Note.** As with `PDMDPRealization`, conditioning on the current state $(T_n,Z_n)$ rather than the full history is equivalent here since the book's own conditional-law formula is already measurable with respect to $(T_n,Z_n)$ alone.
--
--   **Moderation note.** As for `PDMDPRealization`: the draft conditioned only on `Z_n` and read the value as a real Bochner integral. Now the jump-chain realization conditions on the full history `(T_k,Z_k)_{k≤n}`, the post-jump law is `Q(·|Z_n, f_n(T_n, Z_n))` weighted by `λ`-exponential inter-jump times, and `V_π(t,x)` is the `[-∞,∞]`-valued expected reward up to the horizon.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 258, PDF 269, the unnumbered display preceding Theorem 8.3.2

import Mathlib
import Definitions.Def_MDPFinance_PDMDP_Model
import Definitions.Def_MDPFinance_PDMDP_Chain

open MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal

namespace MDPFinance.PDMDP

variable {E U : Type*} [MeasurableSpace E] [Countable E] [MeasurableSpace U]

/-- A **realization of a Markov policy** `f = (f_n)` for the finite-horizon continuous-time Markov
Decision Chain, started at time `t_0` in state `x` (Bäuerle–Rieder, p. 258, PDF 269): a probability
space carrying the jump times `T` and post-jump states `Z`, with the conditional law of
`(T_{n+1}-T_n, Z_{n+1})` given the **full history** `(T_0,Z_0,…,T_n,Z_n)` equal to the
uniformized chain's jump mechanism `λ ∫_0^t e^{-λs} Q(B | Z_n, f_n(T_n,Z_n)(s)) ds`. -/
structure MDChainRealizationFinite (Ω : Type*) [MeasurableSpace Ω] (Ch : MDChainFinite E U)
    (f : ℕ → ℝ → E → ControlFn U) (t0 : ℝ) (x : E) where
  ℙrob : Measure Ω
  hprob : IsProbabilityMeasure ℙrob
  T : ℕ → Ω → ℝ
  Z : ℕ → Ω → E
  hT0 : ∀ ω, T 0 ω = t0
  hZ0 : ∀ ω, Z 0 ω = x
  hTmeas : ∀ n, Measurable (T n)
  hZmeas : ∀ n, Measurable (Z n)
  hTmono : ∀ n ω, T n ω < T (n + 1) ω
  hlaw : ∀ n (B : Set E) (t : ℝ), MeasurableSet B →
    condExp (MeasurableSpace.comap (fun ω => fun k : Fin (n + 1) => (T k ω, Z k ω)) inferInstance)
        ℙrob (Set.indicator {ω | T (n + 1) ω - T n ω ≤ t ∧ Z (n + 1) ω ∈ B} 1)
      =ᵐ[ℙrob] fun ω =>
        Ch.lam * ∫ s in Set.Ioc (0 : ℝ) t, Real.exp (-Ch.lam * s) *
          (Ch.Qmeas (Z n ω) ((f n (T n ω) (Z n ω)).1 s) B).toReal

variable {Ω : Type*} [MeasurableSpace Ω] {Ch : MDChainFinite E U}
  {f : ℕ → ℝ → E → ControlFn U} {t0 : ℝ} {x : E}

/-- The step `n` with `t ∈ [T_n(ω),T_{n+1}(ω))`; `0` as a junk value otherwise. -/
noncomputable def MDChainRealizationFinite.jumpIndex
    (R : MDChainRealizationFinite Ω Ch f t0 x) (ω : Ω) (t : ℝ) : ℕ :=
  if h : ∃ n, R.T n ω ≤ t ∧ t < R.T (n + 1) ω then h.choose else 0

/-- `X_t = Z_n` for `t ∈ [T_n,T_{n+1})` (the chain's state is constant between jumps). -/
noncomputable def MDChainRealizationFinite.X (R : MDChainRealizationFinite Ω Ch f t0 x) (ω : Ω)
    (t : ℝ) : E :=
  R.Z (R.jumpIndex ω t) ω

/-- The control process `π_t = f_n(T_n,Z_n)(t-T_n)` for `t ∈ [T_n,T_{n+1})`. -/
noncomputable def MDChainRealizationFinite.piCtrl (R : MDChainRealizationFinite Ω Ch f t0 x)
    (ω : Ω) (t : ℝ) : U :=
  (f (R.jumpIndex ω t) (R.T (R.jumpIndex ω t) ω) (R.Z (R.jumpIndex ω t) ω)).1
    (t - R.T (R.jumpIndex ω t) ω)

/-- `V^π(t_0,x) := 𝔼^π_{t_0,x}[∫_{t_0}^{T} r(X_s,π_s) ds + g(X_T)] ∈ [-∞,∞]` (Bäuerle–Rieder,
p. 258, PDF 269). -/
noncomputable def MDChainRealizationFinite.Vpi (R : MDChainRealizationFinite Ω Ch f t0 x) :
    EReal :=
  erealIntegral R.ℙrob fun ω =>
    erealIntegral (volume.restrict (Set.Ioc (0 : ℝ) (Ch.Th - t0)))
        (fun s => ((Ch.r (R.X ω (t0 + s), R.piCtrl ω (t0 + s)) : ℝ) : EReal)) +
      ((Ch.g (R.X ω Ch.Th) : ℝ) : EReal)

end MDPFinance.PDMDP


