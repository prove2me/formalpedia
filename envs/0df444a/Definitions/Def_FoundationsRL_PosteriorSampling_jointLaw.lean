-- Prove2me | Definitions.Def_FoundationsRL_PosteriorSampling_jointLaw
-- name    : FoundationsRL_PosteriorSampling_jointLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:19:26.471879+00:00
-- url     : https://prove2.me/theorems/d466efc0-faa7-49a3-9115-261bb4bc68f6
-- title:
--   The joint law of $(M^\star,H^n)$
-- statement:
--   Fix a prior $\mu$ on models and an algorithm $\pi$, that is, a Markov kernel per round from the history to the decisions. The **joint law** of $(M^\star,H^n)$, where $H^n=((\pi^1,r^1),\dots,(\pi^n,r^n))$, is the law of the following experiment: draw $M^\star\sim\mu$, and in each round draw $\pi^t\sim p^t(\cdot\mid H^{t-1})$ and then $r^t\sim M^\star(\cdot\mid\pi^t)$.
--
--   The decision of a round depends on the history only, so it is conditionally independent of $M^\star$ given the history. The module also defines the law of $H^n$ alone.
--
--   **Formalization Note** The law of the first $n$ rounds uses only the kernels of those rounds, which lets the definition of posterior sampling refer to it without circularity.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, p. 31 and §2.6, p. 35 (the joint law over M⋆ and H^T)

import Mathlib
import Definitions.Def_BanditPolicy
import Definitions.Def_FoundationsRL_PosteriorSampling_BanditModel

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace FoundationsRL.PosteriorSampling

/-- Append the round `(π, r)` to a history: `H^t = (H^{t-1}, π^t, r^t)`. -/
def appendRound {A n : ℕ} (h : BanditHistory A n) (z : Fin A × ℝ) : BanditHistory A (n + 1) :=
  Fin.snoc (α := fun _ => Fin A × ℝ) h z

lemma measurable_appendRound {A n : ℕ} :
    Measurable fun x : BanditHistory A n × (Fin A × ℝ) => appendRound x.1 x.2 :=
  measurable_banditHistorySnoc

/-- One round of the Bayesian bandit given the model and the history: sample `π ∼ K(· | H)`,
then `r ∼ M(· | π)`. The decision depends on the history only, not on the model (the learner's
decision `πᵗ` is conditionally independent of `M⋆` given `H^{t-1}`, Foster & Rakhlin,
arXiv:2312.16730v1, p. 31). -/
noncomputable def stepKernel {A n : ℕ} (K : Kernel (BanditHistory A n) (Fin A))
    [IsMarkovKernel K] : Kernel (BanditModel A × BanditHistory A n) (Fin A × ℝ) :=
  (K.comap Prod.snd measurable_snd) ⊗ₖ
    ((rewardKernel A).comap (fun x => (x.1.1, x.2))
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd))

instance {A n : ℕ} (K : Kernel (BanditHistory A n) (Fin A)) [IsMarkovKernel K] :
    IsMarkovKernel (stepKernel K) := by
  rw [stepKernel]; infer_instance

/-- One step of the recursion for the joint law: `P ↦` the law of `(M, (H, π, r))` when
`(M, H) ∼ P` and `(π, r)` follows `stepKernel K`. -/
noncomputable def extendLaw {A n : ℕ} (P : Measure (BanditModel A × BanditHistory A n))
    (K : Kernel (BanditHistory A n) (Fin A)) [IsMarkovKernel K] :
    Measure (BanditModel A × BanditHistory A (n + 1)) :=
  (P ⊗ₘ stepKernel K).map fun x => (x.1.1, appendRound x.1.2 x.2)

/-- The joint law `ℙ` of `(M⋆, H^n)` (Foster & Rakhlin, *Foundations of Reinforcement Learning
and Interactive Decision Making*, arXiv:2312.16730v1, p. 31 and p. 35): sample `M⋆ ∼ μ`, then
run the algorithm `π` against `M⋆` for `n` rounds, with `πᵗ ∼ pᵗ(· | H^{t-1})` and
`rᵗ ∼ M⋆(· | πᵗ)`.

**Formalization Note.** `BanditPolicy A` is the published policy type: one Markov kernel per
round from the history to `Fin A`. The law of the first `n` rounds uses only the kernels of
those rounds, which is what lets `IsPosteriorSampling` refer to it without circularity. -/
noncomputable def jointLaw {A : ℕ} (μ : Measure (BanditModel A)) (π : BanditPolicy A) :
    (n : ℕ) → Measure (BanditModel A × BanditHistory A n)
  | 0 => μ.map fun M => (M, fun t => t.elim0)
  | n + 1 => extendLaw (jointLaw μ π n) (π.select n)

instance {A n : ℕ} (P : Measure (BanditModel A × BanditHistory A n)) [IsProbabilityMeasure P]
    (K : Kernel (BanditHistory A n) (Fin A)) [IsMarkovKernel K] :
    IsProbabilityMeasure (extendLaw P K) := by
  rw [extendLaw]
  refine Measure.isProbabilityMeasure_map (Measurable.aemeasurable ?_)
  exact (measurable_fst.comp measurable_fst).prodMk
    (measurable_appendRound.comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

instance {A : ℕ} (μ : Measure (BanditModel A)) [IsProbabilityMeasure μ] (π : BanditPolicy A)
    (n : ℕ) : IsProbabilityMeasure (jointLaw μ π n) := by
  induction n with
  | zero =>
      rw [jointLaw]
      exact Measure.isProbabilityMeasure_map
        (measurable_id.prodMk measurable_const).aemeasurable
  | succ n ih =>
      rw [jointLaw]
      infer_instance

/-- The law of the history `H^n` alone. -/
noncomputable def histLaw {A : ℕ} (μ : Measure (BanditModel A)) (π : BanditPolicy A) (n : ℕ) :
    Measure (BanditHistory A n) :=
  (jointLaw μ π n).map Prod.snd

instance {A : ℕ} (μ : Measure (BanditModel A)) [IsProbabilityMeasure μ] (π : BanditPolicy A)
    (n : ℕ) : IsProbabilityMeasure (histLaw μ π n) :=
  Measure.isProbabilityMeasure_map measurable_snd.aemeasurable

end FoundationsRL.PosteriorSampling


