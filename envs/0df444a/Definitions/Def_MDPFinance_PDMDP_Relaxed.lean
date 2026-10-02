-- Prove2me | Definitions.Def_MDPFinance_PDMDP_Relaxed
-- name    : MDPFinance_PDMDP_Relaxed
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:07:17.736734+00:00
-- url     : https://prove2.me/theorems/5e683857-61d4-428e-bbf6-ed1a999ccfb6
-- title:
--   The embedded discrete-time model with relaxed controls (Eq. 8.6-8.7)
-- statement:
--   To prove existence of an optimal policy, §8.2 enlarges the control-function space $A$ to the space $R$ of **relaxed controls** $\alpha : \mathbb R_{\ge0} \to \mathbb P(U)$ (Eq. (8.6)), compact in a suitable (Young) topology, unlike $A$ itself. This item restates the same value-function/operator apparatus as `PDMDPRealization`'s embedded-model half (`JnEmbed`/`JinfEmbed`/`JinfSup`/`LEmbed`/`TEmbed`), but for policies valued in $R$ instead of $A$: `JnEmbedRelaxed`/`JinfEmbedRelaxed` give the $n$-stage and limiting reward-to-go of a relaxed Markov policy, $J^{rel}_\infty(x) := \sup_{(f_n)}J_\infty(f_n)(x)$ (`JrelInfSup`) is the value function of the relaxed embedded model, and `Lrel`/`Trel` are its one-stage and maximal-reward operators. Since $A \subset R$ (a deterministic control is a relaxed control whose measures are point masses), $J^{rel}_\infty \ge J_\infty$: the decision maker can only do at least as well with more available controls — this inequality is not itself a numbered result and is not separately stated here, but is the conceptual reason `theorem_8_2_7` is needed to recover equality.
--
--   **Formalization Note.** A genuinely separate set of definitions from `PDMDPRealization`'s nonrelaxed ones (rather than a single definition parametrized by a control-type), matching the chapter-specific pitfall that relaxed and nonrelaxed controls are deliberately distinct objects in this chapter, not different instances of one abstraction.
--
--   **Moderation note.** The draft's relaxed value functions were real-valued suprema (junk `0` on unbounded or empty sets) over arbitrary maps. Now relaxed policies are measurable decision rules `E → R` (the relaxed control functions with the Young topology's Borel σ-algebra), `J_n^r`, `J_∞^r`, the supremum `J^r_∞` and the operators `L^r`, `T^r` are `[-∞,∞]`-valued and built from the relaxed embedded reward and kernel.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 249-252, PDF 260-263, Remark 8.2.3 and the unnumbered displays through Definition 8.2.4

import Mathlib
import Definitions.Def_MDPFinance_PDMDP_Model
import Definitions.Def_MDPFinance_PDMDP_Embedding

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace MDPFinance.PDMDP

variable {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [MeasurableSpace U] [TopologicalSpace U]

/-- A Markov policy of the embedded model with relaxed controls: measurable `f_n : E → R`. -/
def IsRelaxedPolicy (f : ℕ → E → RelaxedControlFn U) : Prop := ∀ n, Measurable (f n)

/-- The `n`-stage reward-to-go of the embedded model **with relaxed controls** under a reward
rate `rew` (Bäuerle–Rieder, p. 250-251, PDF 261-262), in `[-∞,∞]`. -/
noncomputable def JnEmbedRelaxedWith (Mk : PDMDPModel E U) (EmbR : EmbeddedKernelRelaxed Mk)
    (rew : E × U → ℝ) (f : ℕ → E → RelaxedControlFn U) : ℕ → E → EReal
  | 0, _ => 0
  | (n + 1), x =>
      Mk.rprimeRelaxedWith rew (x, f 0 x) +
        erealIntegral (EmbR.QprimeR (x, f 0 x))
          (JnEmbedRelaxedWith Mk EmbR rew (fun k => f (k + 1)) n)

/-- `J_n(f)` of the relaxed embedded model for the reward `r`. -/
noncomputable def JnEmbedRelaxed (Mk : PDMDPModel E U) (EmbR : EmbeddedKernelRelaxed Mk)
    (f : ℕ → E → RelaxedControlFn U) : ℕ → E → EReal :=
  JnEmbedRelaxedWith Mk EmbR Mk.r f

/-- `J_∞(f)(x)` for a relaxed Markov policy, as a `limsup`. -/
noncomputable def JinfEmbedRelaxed (Mk : PDMDPModel E U) (EmbR : EmbeddedKernelRelaxed Mk)
    (f : ℕ → E → RelaxedControlFn U) (x : E) : EReal :=
  atTop.limsup fun n => JnEmbedRelaxed Mk EmbR f n x

/-- `J^{rel}_∞(x) := sup_{(f_n)} J_∞(f_n)(x)` over relaxed Markov policies (Bäuerle–Rieder,
p. 251, PDF 262). -/
noncomputable def JrelInfSup (Mk : PDMDPModel E U) (EmbR : EmbeddedKernelRelaxed Mk) (x : E) :
    EReal :=
  ⨆ f ∈ {f : ℕ → E → RelaxedControlFn U | IsRelaxedPolicy f}, JinfEmbedRelaxed Mk EmbR f x

/-- `(Lv)(x,α) := r'(x,α) + ∫ v dQ'(·|x,α)` for relaxed controls. -/
noncomputable def Lrel (Mk : PDMDPModel E U) (EmbR : EmbeddedKernelRelaxed Mk) (v : E → EReal)
    (xα : E × RelaxedControlFn U) : EReal :=
  Mk.rprimeRelaxed xα + erealIntegral (EmbR.QprimeR xα) v

/-- `(Tv)(x) := sup_{α ∈ R} (Lv)(x,α)` (Bäuerle–Rieder, p. 250, PDF 261). -/
noncomputable def Trel (Mk : PDMDPModel E U) (EmbR : EmbeddedKernelRelaxed Mk) (v : E → EReal)
    (x : E) : EReal :=
  ⨆ α : RelaxedControlFn U, Lrel Mk EmbR v (x, α)

end MDPFinance.PDMDP


