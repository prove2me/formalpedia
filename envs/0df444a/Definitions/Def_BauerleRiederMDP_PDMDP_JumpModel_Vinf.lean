-- Prove2me | Definitions.Def_BauerleRiederMDP_PDMDP_JumpModel_Vinf
-- name    : BauerleRiederMDP_PDMDP_JumpModel_Vinf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:31:53.501332+00:00
-- url     : https://prove2.me/theorems/e27f5f18-41e1-4a9f-92bd-042ff62029a8
-- title:
--   The law $\mathbb P^\pi_x$, the process $X_t$, $V_\pi$ (8.2) and $V_\infty$ (8.3)
-- statement:
--   For a Markov policy $\pi=(f_n)$ and $x\in E$, the module constructs the law $\mathbb P^\pi_x$ of the marked point process with $T_0=0$, $Z_0=x$ and
--   $$
--   \mathbb P^\pi_x\big(T_{n+1}-T_n\le t,\ Z_{n+1}\in B\mid T_0,Z_0,\dots,T_n,Z_n\big)=\lambda\int_0^te^{-\lambda s}Q\big(B\mid\varphi^\pi_s(Z_n),f_n(Z_n)(s)\big)\,ds,
--   $$
--   the process $X_t=\varphi^\pi_{t-T_n}(Z_n)$ for $t\in[T_n,T_{n+1})$ and $\pi_t=f_n(Z_n)(t-T_n)$, and
--   $$
--   V_\pi(x):=\mathbb E^\pi_x\Big[\int_0^\infty e^{-\beta t}r(X_t,\pi_t)\,dt\Big],\qquad V_\infty(x):=\sup_\pi V_\pi(x),
--   $$
--   the supremum over all Markov policies.
--
--   This is the continuous-time control problem. That its value equals the embedded value is a theorem, not a definition.
--
--   **Formalization Note** $\pi_t$ uses the index of $X_t$; it differs from the book's predictable version at the jump times only, a null set of $t$. Integrals are the difference of the Lebesgue integrals of the positive and the negative part.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.245, eq. (8.2), and p.246, eq. (8.3)

import Mathlib
import Definitions.Def_BauerleRiederMDP_PDMDP_DecisionRule
import Definitions.Def_BauerleRiederMDP_PDMDP_JumpModel
import Definitions.Def_BauerleRiederMDP_PDMDP_pathLaw
import Definitions.Def_MDPFinance_PDMDP_Core

open MeasureTheory ProbabilityTheory
open MDPFinance.PDMDP (erealIntegral)

namespace BauerleRiederMDP.PDMDP

namespace JumpModel

variable {E U : Type*} [TopologicalSpace E] [TopologicalSpace.PseudoMetrizableSpace E]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace U]

/-- `(z, s) ↦ φ^{f(z)}_s(z)` is jointly measurable: measurable in `z` for fixed `s` (the flow is
measurable in `(x, α)`) and continuous in `s`. -/
theorem measurable_flow_rule (M : JumpModel E U) (f : DecisionRule E U) :
    Measurable fun p : E × ℝ => M.flow (f.control p.1).toRelaxed p.1 p.2 := by
  have hm : Measurable fun z : E => (z, f.control z) :=
    measurable_id.prodMk f.measurable_control
  have hs : ∀ s : ℝ, Measurable fun z : E => M.flow (f.control z).toRelaxed z s := by
    intro s
    have := (M.flow_measurable s).comp hm
    exact this
  have hc : ∀ z : E, Continuous fun s : ℝ => M.flow (f.control z).toRelaxed z s :=
    fun z => M.flow_continuous (f.control z).toRelaxed z
  have h : Measurable (Function.uncurry fun (s : ℝ) (z : E) =>
      M.flow (f.control z).toRelaxed z s) := by
    apply measurable_uncurry_of_continuous_of_measurable hc hs
  have hsw : Measurable fun p : E × ℝ => (p.2, p.1) := measurable_snd.prodMk measurable_fst
  have e : (fun p : E × ℝ => M.flow (f.control p.1).toRelaxed p.1 p.2) =
      (Function.uncurry fun (s : ℝ) (z : E) => M.flow (f.control z).toRelaxed z s) ∘
        fun p : E × ℝ => (p.2, p.1) := by
    funext p
    simp only [Function.comp_apply, Function.uncurry_apply_pair]
  rw [e]
  exact h.comp hsw

/-- The state and the action at time `s` after the jump, from the post-jump state `z`, under `f`. -/
noncomputable def jumpPoint (M : JumpModel E U) (f : DecisionRule E U) (p : (ℝ × E) × ℝ) : E × U :=
  (M.flow (f.control p.1.2).toRelaxed p.1.2 p.2, f.1 (p.2, p.1.2))

theorem measurable_jumpPoint (M : JumpModel E U) (f : DecisionRule E U) :
    Measurable (M.jumpPoint f) :=
  ((M.measurable_flow_rule f).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)).prodMk
    (f.2.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))

/-- The one-step kernel of the marked point process `(T_n, Z_n)` under the decision rule `f`
(Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.245, PDF 256):
`IP^π_x(T_{n+1} - T_n ≤ t, Z_{n+1} ∈ B | T_0, Z_0, …, T_n, Z_n)
  = λ ∫_0^t e^{-λs} Q(B|φ^π_s(Z_n), f_n(Z_n)(s)) ds`. -/
noncomputable def step (M : JumpModel E U) (f : DecisionRule E U) : Kernel (ℝ × E) (ℝ × E) :=
  jumpStep M.lam M.Q (M.jumpPoint f) (M.measurable_jumpPoint f)

instance (M : JumpModel E U) (f : DecisionRule E U) : IsMarkovKernel (M.step f) :=
  isMarkovKernel_jumpStep M.lam_pos _ _ _

/-- The law `IP^π_x` of the marked point process `(T_n, Z_n)` under the Markov policy `π = (f_n)`,
on the path space, with `T_0 = 0` and `Z_0 = x` (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.245, PDF 256). -/
noncomputable def law (M : JumpModel E U) (π : ℕ → DecisionRule E U) (x : E) :
    Measure (ℕ → ℝ × E) :=
  pathLaw (fun n => M.step (π n)) (0, x)

/-- The piecewise deterministic process `X_t = φ^π_{t-T_n}(Z_n)` for `t ∈ [T_n, T_{n+1})`
(Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.245, PDF 256). -/
noncomputable def X (M : JumpModel E U) (π : ℕ → DecisionRule E U) (ω : ℕ → ℝ × E) (t : ℝ) : E :=
  M.flow ((π (jumpIndex ω t)).control (ω (jumpIndex ω t)).2).toRelaxed (ω (jumpIndex ω t)).2
    (t - (ω (jumpIndex ω t)).1)

/-- The control process `π_t = f_n(Z_n)(t - T_n)` (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.245, PDF 256).

**Formalization Note** The book takes `t ∈ (T_n, T_{n+1}]`, the predictable version, and here the
index is that of `X`, `t ∈ [T_n, T_{n+1})`. The two differ at the jump times only, a Lebesgue-null
set of `t`, and `π_t` appears only under `dt`. -/
noncomputable def control (_M : JumpModel E U) (π : ℕ → DecisionRule E U) (ω : ℕ → ℝ × E)
    (t : ℝ) : U :=
  (π (jumpIndex ω t)).1 (t - (ω (jumpIndex ω t)).1, (ω (jumpIndex ω t)).2)

/-- The expected discounted total reward `V_π(x) := IE^π_x[∫_0^∞ e^{-βt} r(X_t, π_t) dt]`
(Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), eq. (8.2), p.245, PDF 256), for a Markov policy `π = (f_n)`.

**Formalization Note** It is computed from the law of the continuous-time process, independently
of the embedded model. Both integrals are `erealIntegral`, the difference of the Lebesgue integrals
of the positive and the negative part. The Integrability Assumption (A) makes the positive parts
finite; an upper bounding function with `α_b < 1` implies (A). -/
noncomputable def Vpi (M : JumpModel E U) (π : ℕ → DecisionRule E U) (x : E) : EReal :=
  erealIntegral (M.law π x) fun ω =>
    erealIntegral (volume.restrict (Set.Ioi (0 : ℝ))) fun t =>
      ((Real.exp (-M.β * t) * M.r (M.X π ω t, M.control π ω t) : ℝ) : EReal)

/-- The value function `V_∞(x) := sup_π V_π(x)`, the supremum over all Markov policies
(Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), eq. (8.3), p.246, PDF 257). -/
noncomputable def Vinf (M : JumpModel E U) (x : E) : EReal :=
  ⨆ π : ℕ → DecisionRule E U, M.Vpi π x

end JumpModel

end BauerleRiederMDP.PDMDP


