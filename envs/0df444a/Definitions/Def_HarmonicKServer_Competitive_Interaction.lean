-- Prove2me | Definitions.Def_HarmonicKServer_Competitive_Interaction
-- name    : HarmonicKServer_Competitive_Interaction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T12:00:08.73092+00:00
-- url     : https://prove2.me/theorems/5d3a21df-eab9-45bb-845b-7564ccd46962
-- title:
--   §2 — Adaptive interaction law and extended expected costs
-- statement:
--   Fix initial configurations $X_0,Y_0$. For a deterministic adaptive policy $A$, the probability of a finite label history $h$ is the product of its actual Harmonic conditional probabilities, recomputing each request and service schedule from the completed prefix. For a horizon $N$, write $w\in[k]^N$ for a branch and $S_A(w)$ for its final state. Its expected online cost is
--   $$\sum_{w\in[k]^N}P_A(w)\,C_{\rm H}(S_A(w)),$$
--   with the same definition for adversary cost. The requests are endogenous functions of the branch; no request sequence is fixed in advance.
--
--   A randomized adversary chooses an arbitrary private seed $\omega$ from a probability space $(\Omega,\mu)$ and uses the adaptive policy $A_\omega$. All of its private randomness may be sampled initially; decisions still depend on the completed online history. The joint seed-and-history law is the finite sum of the measures with seed density $P_{A_\omega}(w)$ at branch $w$. Mixed expectations are the nonnegative integrals of the branch expectations. Measurability of the scalar probabilities and costs is required, as is necessary to speak of these expectations; no measurable structure, finiteness or separability is imposed on $V$.
--
--   Harmonic is $\rho$-competitive from $X_0,Y_0$ when
--   $$\exists B\in\mathbb R_{\ge0}\ \forall (\Omega,\mu,A)\ \forall N\ge0:\quad
--   \mathbb E[C_{\rm H}(N)]\le\rho\mathbb E[C_{\rm ADV}(N)]+B.$$
--   The finite $B$ precedes the seed space, seed law, policies and horizon. Extended nonnegative expectations retain infinite expected costs and never use a nonintegrable real integral's default value.
-- source:
--   Yichen Huang, STOC 2027 submission #95 (October 2026), p. 3, §2 adaptive interaction and competitiveness, with Lemma 2.3 on p. 4 (PDF p. 4); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/95.pdf; pinned PDF SHA256 20635ef9c29593d01fa406f1a63fdc6b98250e5fc1b1b5c4ed088b407a4e8fd6. Title-page date: November 3, 2026; canonical metadata citation: October 2026.

import Mathlib
import Definitions.Def_HarmonicKServer_Competitive_Harmonic

namespace HarmonicKServer.Competitive
open scoped BigOperators ENNReal
open MeasureTheory

noncomputable def pathWeightFrom {k : ℕ} {V : Type*} [MetricSpace V]
    (A : Adversary k V) : History k → State k V → List (Fin k) → ℝ≥0∞
  | _, _, [] => 1
  | h, S, i :: tail => ENNReal.ofReal (harmonicProbability S.online (A h).request i) *
      pathWeightFrom A (h ++ [i]) (advance S (A h) i) tail

noncomputable def pathWeight {k : ℕ} {V : Type*} [MetricSpace V]
    (A : Adversary k V) (X Y : KServer.Config k V) (h : History k) : ℝ≥0∞ :=
  pathWeightFrom A [] (initial X Y) h

noncomputable def treeExpectation {k : ℕ} {V : Type*} [MetricSpace V]
    (A : Adversary k V) (X Y : KServer.Config k V) (N : ℕ)
    (g : State k V → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ w : Fin N → Fin k,
    pathWeight A X Y (List.ofFn w) * g (stateAt A X Y (List.ofFn w))

noncomputable def onlineExpectation {k : ℕ} {V : Type*} [MetricSpace V]
    (A : Adversary k V) (X Y : KServer.Config k V) (N : ℕ) : ℝ≥0∞ :=
  treeExpectation A X Y N (fun S => ENNReal.ofReal S.onlineCost)

noncomputable def adversaryExpectation {k : ℕ} {V : Type*} [MetricSpace V]
    (A : Adversary k V) (X Y : KServer.Config k V) (N : ℕ) : ℝ≥0∞ :=
  treeExpectation A X Y N (fun S => ENNReal.ofReal S.adversaryCost)

/-- The seed space can be arbitrary: pre-sampling an adversary's private randomness does not
remove its dependence on the completed online history. No metric measurability is imposed. -/
def MeasurableMixture {k : ℕ} {V Ω : Type*} [MetricSpace V] [MeasurableSpace Ω]
    (μ : Measure Ω) (A : Ω → Adversary k V) (X Y : KServer.Config k V) : Prop :=
  (∀ ω, ValidAdversary (A ω) X Y) ∧
  (∀ h, AEMeasurable (fun ω => pathWeight (A ω) X Y h) μ) ∧
  (∀ h, AEMeasurable (fun ω => ENNReal.ofReal (stateAt (A ω) X Y h).onlineCost) μ) ∧
  (∀ h, AEMeasurable (fun ω => ENNReal.ofReal (stateAt (A ω) X Y h).adversaryCost) μ)

noncomputable def mixedOnline {k : ℕ} {V Ω : Type*} [MetricSpace V] [MeasurableSpace Ω]
    (μ : Measure Ω) (A : Ω → Adversary k V) (X Y : KServer.Config k V) (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, onlineExpectation (A ω) X Y N ∂μ

noncomputable def mixedAdversary {k : ℕ} {V Ω : Type*} [MetricSpace V] [MeasurableSpace Ω]
    (μ : Measure Ω) (A : Ω → Adversary k V) (X Y : KServer.Config k V) (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, adversaryExpectation (A ω) X Y N ∂μ

/-- B is finite and fixed before the seed space, policy, seed law and horizon. -/
def AdaptiveCompetitive {k : ℕ} {V : Type*} [MetricSpace V]
    (X Y : KServer.Config k V) (ρ : ℝ) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (A : Ω → Adversary k V),
    MeasurableMixture μ A X Y → ∀ N,
    mixedOnline μ A X Y N ≤ ENNReal.ofReal ρ * mixedAdversary μ A X Y N + ENNReal.ofReal B

/-- The actual joint distribution of the adversary seed and the finite fresh-label history. -/
noncomputable def interactionLaw {k : ℕ} {V Ω : Type*} [MetricSpace V] [MeasurableSpace Ω]
    (μ : Measure Ω) (A : Ω → Adversary k V) (X Y : KServer.Config k V) (N : ℕ) :
    Measure (Ω × (Fin N → Fin k)) :=
  ∑ w : Fin N → Fin k, Measure.map (fun ω => (ω, w))
    (μ.withDensity (fun ω => pathWeight (A ω) X Y (List.ofFn w)))

/-- Concrete complete-round observable; summing its branch law is the conditioning bridge. -/
noncomputable def roundObservable {k : ℕ} {V : Type*} [MetricSpace V]
    (A : Adversary k V) (X Y : KServer.Config k V) (h : History k)
    (g : State k V → Action k V → Fin k → ℝ≥0∞) (i : Fin k) : ℝ≥0∞ :=
  let S := stateAt A X Y h
  g S (A h) i

end HarmonicKServer.Competitive


