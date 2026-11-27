-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesStopping_mdp
-- name    : BauerleRiederMDP_LQ_Supplement_BayesStopping_mdp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:59:51.599931+00:00
-- url     : https://prove2.me/theorems/4fd430c4-c4e2-49da-bc38-986f5cf49079
-- title:
--   The filtered Markov Decision Model of the $n$-stage Bayesian stopping problem
-- statement:
--   **The filtered Markov Decision Model of the $n$-stage Bayesian stopping problem** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §10.3.4, data list pp.323–324, PDF 331–332, with the stopping problems as Markov Decision Models of §10.1, and the substochastic formulation of Example 2.3.13): states $(x, i) \in  E = \mathbb R  \times  I$ (current offer, information state), actions $a \in  {0, 1}$ ($1$ = stop), transition $\hat{T}((x, i), a, z) = (z, \hat{\Phi}(i, z))$ with $z ∼ \hat{Q}^Z(\cdot |i) = \int  Q(\cdot |\theta ) \hat{\mu}(d\theta |i)$, reward $-c$ for continuing, $x$ for stopping in $(x, i)$, terminal reward $g(x, i) = x$, $\beta  = 1$, horizon $n$.
--
--   **Formalization Note.** The substochastic model is made stochastic with an absorbing cemetery: a state is `(stopped, x, i)`; stopping, and any action in a stopped state, moves to the stopped state `(true, x, i)`, where all rewards and the terminal reward are $0$. `true : Bool` is the action "stop". $D(x) = A$. The model is the published finite-horizon `MDPFinance.Bellman` model.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §10.3.4, data list pp.323–324, PDF 331–332, with the stopping problems as Markov Decision Models of §10.1, and the substochastic formulation of Example 2.3.13

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesStopping

open MeasureTheory ProbabilityTheory
open MDPFinance.Bellman (MarkovDecisionModel)

namespace BauerleRiederMDP.LQ.Supplement

open Classical in
/-- **The filtered Markov Decision Model of the `n`-stage Bayesian stopping problem** (Bäuerle &
Rieder, *Markov Decision Processes with Applications to Finance* (2011), §10.3.4, data list
pp.323–324, PDF 331–332, with the stopping problems as Markov Decision Models of §10.1, and the
substochastic formulation of Example 2.3.13): states `(x, i) ∈ E = ℝ × I` (current offer, information
state), actions `a ∈ {0, 1}` (`1` = stop), transition `T̂((x, i), a, z) = (z, Φ̂(i, z))` with
`z ∼ Q̂^Z(·|i) = ∫ Q(·|θ) μ̂(dθ|i)`, reward `−c` for continuing, `x` for stopping in `(x, i)`, terminal
reward `g(x, i) = x`, `β = 1`, horizon `n`.

**Formalization Note.** The substochastic model is made stochastic with an absorbing cemetery: a
state is `(stopped, x, i)`; stopping, and any action in a stopped state, moves to the stopped state
`(true, x, i)`, where all rewards and the terminal reward are `0`. `true : Bool` is the action
"stop". `D(x) = A`. The model is the published finite-horizon `MDPFinance.Bellman` model. -/
noncomputable def BayesStopping.mdp {SΘ : Set ℝ} {I : Type} [MeasurableSpace I]
    (P : BayesStopping SΘ I) (n : ℕ) : MarkovDecisionModel (Bool × ℝ × I) Bool n where
  D := fun _ => Set.univ
  hD_meas := fun _ _ => MeasurableSet.univ
  hD_sel := fun _ _ => ⟨fun _ => true, measurable_const, fun _ => trivial⟩
  Q := fun _ =>
    Kernel.piecewise
      (s := ((fun p : (Bool × ℝ × I) × Bool => p.1.1) ⁻¹' {false}) ∩
        ((fun p : (Bool × ℝ × I) × Bool => p.2) ⁻¹' {false}))
      (((measurableSet_singleton false).preimage (measurable_fst.comp measurable_fst)).inter
        ((measurableSet_singleton false).preimage measurable_snd))
      (((Kernel.id ×ₖ (P.Qk ∘ₖ P.muhat)).map
          (fun q : I × ℝ => ((false, q.2, P.Phihat q) : Bool × ℝ × I))).comap
        (fun p : (Bool × ℝ × I) × Bool => p.1.2.2)
        (measurable_snd.comp (measurable_snd.comp measurable_fst)))
      (Kernel.deterministic (fun p : (Bool × ℝ × I) × Bool => ((true, p.1.2.1, p.1.2.2) : Bool × ℝ × I))
        (measurable_const.prodMk ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
          (measurable_snd.comp (measurable_snd.comp measurable_fst)))))
  hQ_prob := fun _ _ p => by
    have : IsMarkovKernel ((Kernel.id ×ₖ (P.Qk ∘ₖ P.muhat)).map
        (fun q : I × ℝ => ((false, q.2, P.Phihat q) : Bool × ℝ × I))) :=
      Kernel.IsMarkovKernel.map _ (measurable_const.prodMk (measurable_snd.prodMk P.Phihat_meas))
    simp only [Kernel.piecewise_apply]
    split_ifs
    · rw [Kernel.comap_apply]; exact this.isProbabilityMeasure _
    · rw [Kernel.deterministic_apply]; infer_instance
  r := fun _ p => if p.1.1 = false then (if p.2 = true then p.1.2.1 else -P.c) else 0
  hr_meas := fun _ _ => by
    refine Measurable.ite ((measurableSet_singleton false).preimage
      (measurable_fst.comp measurable_fst)) (Measurable.ite
        ((measurableSet_singleton true).preimage measurable_snd)
        (measurable_fst.comp (measurable_snd.comp measurable_fst)) measurable_const)
      measurable_const
  g := fun s => if s.1 = false then s.2.1 else 0
  hg_meas := Measurable.ite ((measurableSet_singleton false).preimage measurable_fst)
    (measurable_fst.comp measurable_snd) measurable_const

end BauerleRiederMDP.LQ.Supplement


