-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_relaxedStage
-- name    : BauerleRiederMDP_LQ_Supplement_JumpMarket_relaxedStage
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:14:11.416984+00:00
-- url     : https://prove2.me/theorems/7964c394-78d8-414c-b7e8-333bcfa376ad
-- title:
--   The discrete-time model of the terminal wealth problem, with relaxed controls
-- statement:
--   **The discrete-time model of the terminal wealth problem, with relaxed controls** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §9.3, p.282, PDF 292, and its extension to relaxed controls, p.285, PDF 295): states $(t, x) \in  E = [0, T] \times  \mathbb R _+$ (jump time, post-jump wealth), actions $\alpha  \in  R$, reward $r(t, x, \alpha ) = e^{-\lambda (T-t)} U(\varphi ^\alpha _{T-t}(x))$ and $\int  v dQ(\cdot |t, x, \alpha ) = \lambda  \int _0^{T-t} e^{-\lambda s} \int \int  v(t + s, \varphi ^\alpha _s(x)(1 + u \cdot  y)) \alpha _s(du) Q^Y(dy) ds$; discount factor $1$, the cemetery state $\Delta $ skipped (substochastic).
--
--   **Formalization Note.** The published substochastic `StageModel` shape. $Q(\cdot |t, x, \alpha )$ is the image of the measure $\lambda  e^{-\lambda s} ds$ on $(0, T - t]$ under the kernel $s \mapsto $ law of $(t + s, \varphi ^\alpha _s(x)(1 + u \cdot  y))$, $u ∼ \alpha _s$, $y ∼ Q^Y$. The state type is $\mathbb R  \times  \mathbb R $; only $E$ is used.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §9.3, p.282, PDF 292, and its extension to relaxed controls, p.285, PDF 295

import Mathlib
import Definitions.Def_BauerleRiederMDP_PDMDP_RelaxedControl
import Definitions.Def_BauerleRiederMDP_PDMDP_StageModel
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_Ufrac
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_flow

open MeasureTheory ProbabilityTheory
open BauerleRiederMDP.PDMDP (RelaxedControl StageModel)

namespace BauerleRiederMDP.LQ.Supplement

/-- **The discrete-time model of the terminal wealth problem, with relaxed controls** (Bäuerle &
Rieder, *Markov Decision Processes with Applications to Finance* (2011), §9.3, p.282, PDF 292, and
its extension to relaxed controls, p.285, PDF 295): states `(t, x) ∈ E = [0, T] × ℝ_+` (jump time,
post-jump wealth), actions `α ∈ R`, reward `r(t, x, α) = e^{−λ(T−t)} U(φ^α_{T−t}(x))` and
`∫ v dQ(·|t, x, α) = λ ∫_0^{T−t} e^{−λs} ∫∫ v(t + s, φ^α_s(x)(1 + u · y)) α_s(du) Q^Y(dy) ds`;
discount factor `1`, the cemetery state `Δ` skipped (substochastic).

**Formalization Note.** The published substochastic `StageModel` shape. `Q(·|t, x, α)` is the image
of the measure `λ e^{−λs} ds` on `(0, T − t]` under the kernel `s ↦` law of
`(t + s, φ^α_s(x)(1 + u · y))`, `u ∼ α_s`, `y ∼ Q^Y`. The state type is `ℝ × ℝ`; only `E` is used. -/
noncomputable def JumpMarket.relaxedStage {d : ℕ} (Mk : JumpMarket d) (U : ℝ → ℝ) :
    StageModel (ℝ × ℝ) (RelaxedControl (Ufrac d)) where
  rew p α := ((Real.exp (-Mk.lam * (Mk.T - p.1)) * U (Mk.flow α p.2 (Mk.T - p.1)) : ℝ) : EReal)
  kern p α := haveI := α.2
    ENNReal.ofReal Mk.lam •
      (((Kernel.id ×ₖ (α.1 ×ₖ Kernel.const ℝ Mk.QY)).map fun q : ℝ × (Ufrac d × (Fin d → ℝ)) =>
          ((p.1 + q.1, Mk.flow α p.2 q.1 * (1 + q.2.1.1 ⬝ᵥ q.2.2)) : ℝ × ℝ)) ∘ₘ
        ((volume.restrict (Set.Ioc (0 : ℝ) (Mk.T - p.1))).withDensity fun s =>
          ENNReal.ofReal (Real.exp (-Mk.lam * s))))

end BauerleRiederMDP.LQ.Supplement


