-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_finiteChainEmbStage
-- name    : BauerleRiederMDP_LQ_Supplement_finiteChainEmbStage
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:42:46.636638+00:00
-- url     : https://prove2.me/theorems/2b2c37c9-ce2a-5311-bbf0-7e724e5a05c9
-- title:
--   The embedded discrete-time model of a finite-horizon Markov Decision Chain
-- statement:
--   **The embedded discrete-time model of a finite-horizon Markov Decision Chain** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), (8.13)–(8.14), p.259, PDF 270): state space $E' = [0, T] \times  E$, actions the control functions $\alpha  \in  A$, $Q'(B \times  {y} | t, x, \alpha ) = \lambda  \int _0^{T-t} e^{-\lambda s} 1_B(t + s) Q({y}|x, \alpha _s) ds$ and $r'(t, x, \alpha ) = \int _0^{T-t} e^{-\lambda s} r(x, \alpha _s) ds + e^{-\lambda (T-t)} g(x)$, discount factor $1$.
--
--   **Formalization Note.** The published substochastic `StageModel` shape (cemetery skipped, as the book does). The state type is $\mathbb R  \times  E$; only $t \in  [0, T]$ is used. $Q'$ is the image of the measure $\lambda  e^{-\lambda s} ds$ on $(0, T - t]$ under the kernel $s \mapsto  \delta _{t+s} \otimes  Q(\cdot |x, \alpha _s)$. The reward integral is the published `erealIntegral`.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), (8.13)–(8.14), p.259, PDF 270

import Mathlib
import Definitions.Def_MDPFinance_PDMDP_Core
import Definitions.Def_BauerleRiederMDP_PDMDP_ControlFn
import Definitions.Def_BauerleRiederMDP_PDMDP_RateModel
import Definitions.Def_BauerleRiederMDP_PDMDP_StageModel
import Definitions.Def_BauerleRiederMDP_PDMDP_FiniteChain

open MeasureTheory ProbabilityTheory
open MDPFinance.PDMDP (erealIntegral)
open BauerleRiederMDP.PDMDP

namespace BauerleRiederMDP.LQ.Supplement

/-- **The embedded discrete-time model of a finite-horizon Markov Decision Chain** (Bäuerle &
Rieder, *Markov Decision Processes with Applications to Finance* (2011), (8.13)–(8.14), p.259,
PDF 270): state space `E′ = [0, T] × E`, actions the control functions `α ∈ A`,
`Q′(B × {y} | t, x, α) = λ ∫_0^{T−t} e^{−λs} 1_B(t + s) Q({y}|x, α_s) ds` and
`r′(t, x, α) = ∫_0^{T−t} e^{−λs} r(x, α_s) ds + e^{−λ(T−t)} g(x)`, discount factor `1`.

**Formalization Note.** The published substochastic `StageModel` shape (cemetery skipped, as the
book does). The state type is `ℝ × E`; only `t ∈ [0, T]` is used. `Q′` is the image of the
measure `λ e^{−λs} ds` on `(0, T − t]` under the kernel `s ↦ δ_{t+s} ⊗ Q(·|x, α_s)`. The reward
integral is the published `erealIntegral`. -/
noncomputable def finiteChainEmbStage {E U : Type*} [MeasurableSpace E] [Countable E]
    [MeasurableSingletonClass E] [MeasurableSpace U] (C : FiniteChain E U) :
    StageModel (ℝ × E) (ControlFn U) where
  rew p α := erealIntegral (volume.restrict (Set.Ioc (0 : ℝ) (C.horizon - p.1))) (fun s =>
      ((Real.exp (-C.lam * s) * C.r (p.2, α.1 s) : ℝ) : EReal)) +
    ((Real.exp (-C.lam * (C.horizon - p.1)) * C.g p.2 : ℝ) : EReal)
  kern p α := ENNReal.ofReal C.lam •
    ((Kernel.deterministic (fun s : ℝ => p.1 + s) (measurable_const.add measurable_id) ×ₖ
        C.Q.comap (fun s : ℝ => (p.2, α.1 s)) (measurable_const.prodMk α.2)) ∘ₘ
      ((volume.restrict (Set.Ioc (0 : ℝ) (C.horizon - p.1))).withDensity fun s =>
        ENNReal.ofReal (Real.exp (-C.lam * s))))

end BauerleRiederMDP.LQ.Supplement


