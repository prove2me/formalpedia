-- Prove2me | Definitions.Def_ListReplicableBias_LowerBound_Sampling
-- name    : ListReplicableBias_LowerBound_Sampling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:22:15.656012+00:00
-- url     : https://prove2.me/theorems/0ba2c80e-73f1-439c-bf76-dc270820ff0d
-- title:
--   Arbitrary randomized adaptive coin sampling and transcript laws
-- statement:
--   An $N$-toss sampling algorithm on $d$ coins has an arbitrary measurable seed space $\Omega$ with probability law $\mu$, measurable coin choices $I_t(\omega,x_{<t})\in[d]$, and a measurable output $Y(\omega,x)\in\mathbb R^d\cup\{\bot\}$. It may use its seed and all preceding outcomes when choosing a coin. For $p\in[0,1]^d$ its transcript law is
--   $$P_p(d\omega,x)=\mu(d\omega)\prod_{t=1}^N b(p_{I_t(\omega,x_{<t})},x_t),\qquad b(u,1)=u,\ b(u,0)=1-u.$$
--   The reference measure is $\mu$ times counting measure on the finite set of outcome strings. Output probabilities are the masses of preimages under $Y$.
--
--   This is an operational sampling model, independent of accuracy or replication. The coin choices in the full history are recoverable from the seed and outcome prefix; all private random choices are included in the initial seed. A fixed sample cap can be padded with ignored tosses. No finite or countable restriction is imposed on the seed space. Lean uses `Option` for failure, with the disjoint-union measurable structure of Borel vectors and an isolated failure point; its indices start at zero. The density is used only for valid bias vectors; outside the unit cube its nonnegative-part extension is not asserted to be a probability law.
-- source:
--   Chen, Bastan, Pavan, Vinodchandran, The Price of List Replicability: Tight Bounds for Bias Estimation, STOC 2027 submission #681 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/681.pdf, §3.2, PDF p. 3; Appendix B, PDF pp. 14–15

import Mathlib

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace ListReplicableBias.LowerBound

/-- A Bernoulli mass (not a new distribution): true has mass p, false mass 1-p.
Used only with p ∈ [0,1], as in §3.2, PDF p. 3. -/
def bernMass (p : ℝ) (x : Bool) : ℝ := if x then p else 1 - p

/-- The disjoint-union measurable structure on vector outputs plus failure.
Vector outputs carry the usual Borel sigma algebra; failure is an isolated point. -/
instance outputMeasurableSpace (d : ℕ) : MeasurableSpace (Option (Fin d → ℝ)) :=
  MeasurableSpace.comap
    (fun y : Option (Fin d → ℝ) => match y with
      | none => (Sum.inr () : (Fin d → ℝ) ⊕ Unit)
      | some v => Sum.inl v) inferInstance

/-- Randomized adaptive N-toss coin sampler, §3.2 and Appendix B, PDF pp. 3, 14–15.
All internal randomness is sampled once from an arbitrary probability space. Earlier
coin choices are recoverable from the seed and earlier outcomes. There are no
accuracy, replication, or likelihood-ratio assumptions in this structure. -/
structure SamplingAlgorithm (d N : ℕ) where
  Ω : Type
  [space : MeasurableSpace Ω]
  μ : Measure Ω
  [probability : IsProbabilityMeasure μ]
  choose : (t : Fin N) → Ω → (Fin t.val → Bool) → Fin d
  choose_measurable : ∀ t x, Measurable (fun ω => choose t ω x)
  out : Ω → (Fin N → Bool) → Option (Fin d → ℝ)
  out_measurable : ∀ x, Measurable (fun ω => out ω x)

attribute [instance] SamplingAlgorithm.space SamplingAlgorithm.probability

/-- The prefix before toss t, using zero-based Fin indices. -/
def historyPrefix {N : ℕ} (x : Fin N → Bool) (t : Fin N) : Fin t.val → Bool :=
  fun s => x ⟨s.val, lt_trans s.isLt t.isLt⟩

/-- Conditional path mass given the internal seed; the chosen coin uses exactly
its preceding outcomes. Appendix B, PDF p. 15. -/
def pathWeight {d N : ℕ} (A : SamplingAlgorithm d N) (p : Fin d → ℝ)
    (z : A.Ω × (Fin N → Bool)) : ℝ :=
  ∏ t : Fin N, bernMass (p (A.choose t z.1 (historyPrefix z.2 t))) (z.2 t)

/-- Law of the seed and all toss outcomes, Appendix B, PDF p. 15.
The reference measure is the seed law times counting measure on Bool^N.
For bias vectors in the unit cube this is a probability measure, by successive
summation over the final bit, since each Bernoulli factor sums to one. -/
def transcriptLaw {d N : ℕ} (A : SamplingAlgorithm d N) (p : Fin d → ℝ) :
    Measure (A.Ω × (Fin N → Bool)) :=
  (A.μ.prod Measure.count).withDensity (fun z => ENNReal.ofReal (pathWeight A p z))

/-- Probability of an output event. The preimage is taken directly, without
using Measure.map, and all applications below are measurable events. -/
def outputProb {d N : ℕ} (A : SamplingAlgorithm d N) (p : Fin d → ℝ)
    (S : Set (Option (Fin d → ℝ))) : ℝ :=
  (transcriptLaw A p {z | A.out z.1 z.2 ∈ S}).toReal

end ListReplicableBias.LowerBound


