-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P21
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P21
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T07:51:12.942764+00:00
-- url     : https://prove2.me/theorems/91b6c260-30b3-4459-b571-fb471b29a9ec
-- title:
--   Definitions for I-concurrence and tangle for isotropic states
-- statement:
--   The objects the formalized statements of *I-concurrence and tangle for isotropic states* (arXiv:quant-ph/0208002) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `marginalTangle`: PDF pp.3--5, (1.3),(2.3): the marginal linear-entropy cost.
--   - `pureTangle`: PDF pp.3--4, (1.3),(2.2): pure tangle, with Alice the first factor. Only normalized vectors are used as physical states.
--   - `tangle`: PDF p.3, (1.5): convex roof of pure tangle, not squared mixed concurrence. The attainment conclusion below pins the source's minimum convention.
--   - `IsPureProductState`: PDF pp.2--4: a normalized pure product state, including arbitrary phase.
--   - `IsMaximallyEntangled`: PDF p.4: maximal pure entanglement has uniform Schmidt probabilities on min(dA,dB) entries, also for unequal local dimensions.
--   - `IsOptimalPureEnsemble`: PDF p.3, (1.4)--(1.5): an attaining normalized finite decomposition. A zero-weight member is unrestricted beyond being normalized.
--   - `isotropicReferenceVector`: PDF p.5, (3.1): the accepted maximally entangled vector, with a total zero-dimensional fallback used nowhere in physical statements.
--   - `isotropicDensityAtFidelity`: PDF p.5, (3.2): rho_(d,F); physical domain d>=2 and 0<=F<=1.
--   - `maximallyEntangledOverlap`: PDF pp.5--6: squared overlap with Phi, not root fidelity.
--   - `SchmidtProbabilities`: PDF pp.4,8: nonnegative, normalized squared Schmidt probabilities. Zero entries are explicitly permitted.
--   - `schmidtCost`: PDF p.4, (2.2): pure tangle from squared Schmidt probabilities.
--   - `fidelityProfile`: PDF p.6, (3.6): no conjugation is applied to the diagonal of V.
--   - `canonicalVector`: PDF pp.4,6: canonical Schmidt vector before Alice's and Bob's unitaries.
--   - `profileValues`: PDF pp.7--8, (3.15),(3.18)--(3.19): the constrained cost values. The nonempty physical domain of this profile is [1/d,1].
--   - `constrainedSchmidtTangle`: PDF p.7, (3.15): raw squared-concurrence profile. Theorems always restrict its arguments to the nonempty feasible domain [1/d,1].
--   - `rawC`: PDF p.7: raw concurrence profile c_d=sqrt(q_d).
--   - `minimizingLargeAmplitude`: PDF p.9, (3.31): sqrt(F/d)(1+w sqrt(d-1)), written without w.
--   - `minimizingSmallAmplitude`: PDF p.9, (3.32): sqrt(F/d)(1-w/sqrt(d-1)), written without w.
--   - `explicitQ`: PDF p.9, (3.30): factor 2 multiplies the entire parenthesis.
--   - `minimizingProbabilities`: PDF p.9, (3.30)--(3.32): one gamma-squared entry, d-1 delta-squared entries.
--   - `ScalarMixture`: PDF p.7, (3.14): finite normalized scalar mixtures in a fixed interval.
--   - `hullValues`: PDF p.7, (3.14): attainable average costs with mean fidelity F.
--   - `scalarConvexRoofAtFidelity`: PDF p.7: scalar lower convex hull, only evaluated on [1/d,1].
--   - `IsConvexEnvelope`: PDF p.7: the largest convex minorant, stated as the full universal property.
--   - `relaxedValues`: PDF p.6, (3.9): relaxed pure ensembles constrain only average fidelity, not the full density. Via Schmidt decomposition these are exactly the source's (p_j,mu_j,V_j); component fidelities can be anywhere in [0,1].
--   - `relaxedRoof`: PDF p.6, (3.9)--(3.10): fidelity-only minimum; attainment is stated below.
--   - `tangentPoint`: PDF p.13: supporting tangent breakpoint, with d^2 in the denominator.
--   - `tangleFormula`: PDF p.13, (3.41): the three branches of isotropic tangle (d>=3).
--   - `concurrenceFormula`: PDF p.13, (3.42): only 2d/(d-1) is under the radical.
--   - `spectralTrace`: PDF p.4, (2.3): real spectral trace for a Hermitian matrix. Finite spectra allow arbitrary scalar f; no operator-concavity is assumed.
-- source:
--   I-concurrence and tangle for isotropic states, arXiv:quant-ph/0208002v1, https://arxiv.org/abs/quant-ph/0208002v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P03
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P30
import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P37

/-!
Statements from Rungta--Caves, arXiv:quant-ph/0208002v1.
All page references are PDF pages. Only pinned accepted modules are imported.
The tangle roof is distinct from the square of the mixed concurrence.
Source corrections on pp.6,7,10 are documented in MODERATION_NOTES.md;
independent moderation and mechanical compilation remain pending.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P21

open scoped Matrix ComplexConjugate
open Filter
open QAlgorithms
open QAlgorithms.Papers.Independent.Information100.P03
  (PureEnsemble convexRoof pureConcurrence concurrence SchmidtData schmidtVector)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.3--5, (1.3),(2.3): the marginal linear-entropy cost. -/
def marginalTangle {I : Type*} [Fintype I] (A : Matrix I I ℂ) : ℝ :=
  2 * (1 - (A * A).trace.re)

/-- PDF pp.3--4, (1.3),(2.2): pure tangle, with Alice the first factor.
Only normalized vectors are used as physical states. -/
def pureTangle {I J : Type*} [Fintype I] [Fintype J]
    (psi : EuclideanSpace ℂ (I × J)) : ℝ :=
  marginalTangle (traceRight (pureDensity psi))

/-- PDF p.3, (1.5): convex roof of pure tangle, not squared mixed concurrence.
The attainment conclusion below pins the source's minimum convention. -/
def tangle {I J : Type*} [Fintype I] [Fintype J]
    (rho : Matrix (I × J) (I × J) ℂ) : ℝ :=
  convexRoof pureTangle rho

/-- PDF pp.2--4: a normalized pure product state, including arbitrary phase. -/
def IsPureProductState {I J : Type*} [Fintype I] [Fintype J]
    (psi : EuclideanSpace ℂ (I × J)) : Prop :=
  ∃ a : EuclideanSpace ℂ I, ∃ b : EuclideanSpace ℂ J,
    IsState a ∧ IsState b ∧ psi = tensorVec a b

/-- PDF p.4: maximal pure entanglement has uniform Schmidt probabilities
on min(dA,dB) entries, also for unequal local dimensions. -/
def IsMaximallyEntangled {a b : ℕ} (psi : EuclideanSpace ℂ (Fin a × Fin b)) : Prop :=
  ∃ s : SchmidtData a b, psi = schmidtVector s ∧
    ∀ i, s.probability i = 1 / (min a b : ℝ)

/-- PDF p.3, (1.4)--(1.5): an attaining normalized finite decomposition.
A zero-weight member is unrestricted beyond being normalized. -/
def IsOptimalPureEnsemble {I : Type*} [Fintype I] (cost : EuclideanSpace ℂ I → ℝ)
    (rho : Matrix I I ℂ) (e : PureEnsemble I) : Prop :=
  ensembleDensity e.weight e.vector = rho ∧
    (∑ k, e.weight k * cost (e.vector k)) = convexRoof cost rho

/-- PDF p.5, (3.1): the accepted maximally entangled vector, with a total
zero-dimensional fallback used nowhere in physical statements. -/
def isotropicReferenceVector (d : ℕ) : EuclideanSpace ℂ (Fin d × Fin d) :=
  if hd : 0 < d then
    letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    finiteMaxEntangled (Fin d)
  else 0

/-- PDF p.5, (3.2): rho_(d,F); physical domain d>=2 and 0<=F<=1. -/
def isotropicDensityAtFidelity (d : ℕ) (F : ℝ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  if hd : 0 < d then
    letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
    Bridge50.P37.isotropicState d F
  else 0

/-- PDF pp.5--6: squared overlap with Phi, not root fidelity. -/
def maximallyEntangledOverlap {d : ℕ} (rho : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : ℝ :=
  effectProb (pureDensity (isotropicReferenceVector d)) rho

/-- PDF pp.4,8: nonnegative, normalized squared Schmidt probabilities.
Zero entries are explicitly permitted. -/
structure SchmidtProbabilities (d : ℕ) where
  probability : Fin d → ℝ
  nonnegative : ∀ i, 0 ≤ probability i
  total : ∑ i, probability i = 1

/-- PDF p.4, (2.2): pure tangle from squared Schmidt probabilities. -/
def schmidtCost {d : ℕ} (mu : Fin d → ℝ) : ℝ :=
  2 * (1 - ∑ i, mu i ^ 2)

/-- PDF p.6, (3.6): no conjugation is applied to the diagonal of V. -/
def fidelityProfile {d : ℕ} (mu : SchmidtProbabilities d)
    (V : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  Complex.normSq (∑ k, (Real.sqrt (mu.probability k) : ℂ) * V k k) / d

/-- PDF pp.4,6: canonical Schmidt vector before Alice's and Bob's unitaries. -/
def canonicalVector {d : ℕ} (mu : SchmidtProbabilities d) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  WithLp.toLp 2 fun p => if p.1 = p.2 then (Real.sqrt (mu.probability p.1) : ℂ) else 0

/-- PDF pp.7--8, (3.15),(3.18)--(3.19): the constrained cost values.
The nonempty physical domain of this profile is [1/d,1]. -/
def profileValues (d : ℕ) (F : ℝ) : Set ℝ :=
  {v | ∃ mu : SchmidtProbabilities d,
    (∑ k, Real.sqrt (mu.probability k)) = Real.sqrt ((d : ℝ) * F) ∧
    v = schmidtCost mu.probability}

/-- PDF p.7, (3.15): raw squared-concurrence profile. Theorems always
restrict its arguments to the nonempty feasible domain [1/d,1]. -/
def constrainedSchmidtTangle (d : ℕ) (F : ℝ) : ℝ := sInf (profileValues d F)

/-- PDF p.7: raw concurrence profile c_d=sqrt(q_d). -/
def rawC (d : ℕ) (F : ℝ) : ℝ := Real.sqrt (constrainedSchmidtTangle d F)

/-- PDF p.9, (3.31): sqrt(F/d)(1+w sqrt(d-1)), written without w. -/
def minimizingLargeAmplitude (d : ℕ) (F : ℝ) : ℝ :=
  Real.sqrt (F / d) + Real.sqrt (((d : ℝ) - 1) * (1 - F) / d)

/-- PDF p.9, (3.32): sqrt(F/d)(1-w/sqrt(d-1)), written without w. -/
def minimizingSmallAmplitude (d : ℕ) (F : ℝ) : ℝ :=
  Real.sqrt (F / d) - Real.sqrt ((1 - F) / ((d : ℝ) * ((d : ℝ) - 1)))

/-- PDF p.9, (3.30): factor 2 multiplies the entire parenthesis. -/
def explicitQ (d : ℕ) (F : ℝ) : ℝ :=
  2 * (1 - minimizingLargeAmplitude d F ^ 4 - ((d : ℝ) - 1) * minimizingSmallAmplitude d F ^ 4)

/-- PDF p.9, (3.30)--(3.32): one gamma-squared entry, d-1 delta-squared entries. -/
def minimizingProbabilities (d : ℕ) (F : ℝ) : Fin d → ℝ :=
  fun i => if i.val = 0 then minimizingLargeAmplitude d F ^ 2 else minimizingSmallAmplitude d F ^ 2

/-- PDF p.7, (3.14): finite normalized scalar mixtures in a fixed interval. -/
structure ScalarMixture (lo hi : ℝ) where
  count : ℕ
  weight : Fin count → ℝ
  point : Fin count → ℝ
  nonnegative : ∀ k, 0 ≤ weight k
  total : ∑ k, weight k = 1
  domain : ∀ k, point k ∈ Set.Icc lo hi

/-- PDF p.7, (3.14): attainable average costs with mean fidelity F. -/
def hullValues (d : ℕ) (f : ℝ → ℝ) (F : ℝ) : Set ℝ :=
  {v | ∃ m : ScalarMixture (1 / (d : ℝ)) 1,
    (∑ k, m.weight k * m.point k) = F ∧ v = ∑ k, m.weight k * f (m.point k)}

/-- PDF p.7: scalar lower convex hull, only evaluated on [1/d,1]. -/
def scalarConvexRoofAtFidelity (d : ℕ) (f : ℝ → ℝ) (F : ℝ) : ℝ := sInf (hullValues d f F)

/-- PDF p.7: the largest convex minorant, stated as the full universal property. -/
def IsConvexEnvelope (D : Set ℝ) (f g : ℝ → ℝ) : Prop :=
  ConvexOn ℝ D g ∧ (∀ x ∈ D, g x ≤ f x) ∧
    ∀ h : ℝ → ℝ, ConvexOn ℝ D h → (∀ x ∈ D, h x ≤ f x) → ∀ x ∈ D, h x ≤ g x

/-- PDF p.6, (3.9): relaxed pure ensembles constrain only average fidelity,
not the full density. Via Schmidt decomposition these are exactly the source's
(p_j,mu_j,V_j); component fidelities can be anywhere in [0,1]. -/
def relaxedValues (d : ℕ) (cost : EuclideanSpace ℂ (Fin d × Fin d) → ℝ)
    (F : ℝ) : Set ℝ :=
  {v | ∃ e : PureEnsemble (Fin d × Fin d),
    (∑ k, e.weight k * maximallyEntangledOverlap (pureDensity (e.vector k))) = F ∧
    v = ∑ k, e.weight k * cost (e.vector k)}

/-- PDF p.6, (3.9)--(3.10): fidelity-only minimum; attainment is stated below. -/
def relaxedRoof (d : ℕ) (cost : EuclideanSpace ℂ (Fin d × Fin d) → ℝ)
    (F : ℝ) : ℝ := sInf (relaxedValues d cost F)

/-- PDF p.13: supporting tangent breakpoint, with d^2 in the denominator. -/
def tangentPoint (d : ℕ) : ℝ := 4 * ((d : ℝ) - 1) / (d : ℝ)^2

/-- PDF p.13, (3.41): the three branches of isotropic tangle (d>=3). -/
def tangleFormula (d : ℕ) (F : ℝ) : ℝ :=
  if F ≤ 1 / (d : ℝ) then 0
  else if F ≤ tangentPoint d then explicitQ d F
  else 2 * d * (F - 1) / ((d : ℝ) - 1) + 2 * ((d : ℝ) - 1) / d

/-- PDF p.13, (3.42): only 2d/(d-1) is under the radical. -/
def concurrenceFormula (d : ℕ) (F : ℝ) : ℝ :=
  if F ≤ 1 / (d : ℝ) then 0
  else Real.sqrt (2 * d / ((d : ℝ) - 1)) * (F - 1 / d)

/-- PDF p.4, (2.3): real spectral trace for a Hermitian matrix.
Finite spectra allow arbitrary scalar f; no operator-concavity is assumed. -/
def spectralTrace {d : ℕ} (f : ℝ → ℝ) (rho : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  (cfc f rho).trace.re

/-! Sanity examples for the new paper-local substrate. -/

example : isotropicReferenceVector 1 (0, 0) = 1 := by
  simp [isotropicReferenceVector, finiteMaxEntangled]

example : tangentPoint 3 = (8 : ℝ) / 9 := by
  norm_num [tangentPoint]

example : concurrenceFormula 2 1 = 1 := by
  norm_num [concurrenceFormula]

example : tangleFormula 3 1 = (4 : ℝ) / 3 := by
  norm_num [tangleFormula, tangentPoint]

example : schmidtCost (fun _ : Fin 1 => (1 : ℝ)) = 0 := by
  simp [schmidtCost]

example {d : ℕ} (rho : Matrix (Fin d) (Fin d) ℂ) :
    spectralTrace (fun _ => 0) rho = 0 := by
  simp [spectralTrace]

example : pureTangle (ket (ι := Fin 1 × Fin 1) (0, 0)) = 0 := by
  simp [pureTangle, marginalTangle, traceRight, pureDensity, ket, Matrix.mul_apply, Matrix.trace]

example {I J : Type*} [Fintype I] [Fintype J]
    (a : EuclideanSpace ℂ I) (b : EuclideanSpace ℂ J) (ha : IsState a) (hb : IsState b) :
    IsPureProductState (tensorVec a b) := ⟨a, b, ha, hb, rfl⟩

example : (0 : ℝ) ∈ profileValues 1 1 := by
  refine ⟨⟨fun _ => 1, by intro k; norm_num, by simp⟩, ?_, ?_⟩
  · norm_num
  · simp [schmidtCost]

example (d : ℕ) : minimizingLargeAmplitude d 1 = minimizingSmallAmplitude d 1 := by
  simp [minimizingLargeAmplitude, minimizingSmallAmplitude]

example (d : ℕ) (f : ℝ → ℝ) (F : ℝ) (hF : F ∈ Set.Icc (1/(d : ℝ)) 1) :
    f F ∈ hullValues d f F := by
  let m : ScalarMixture (1/(d : ℝ)) 1 :=
    ⟨1, fun _ => 1, fun _ => F, by intro k; norm_num, by simp, fun _ => hF⟩
  refine ⟨m, ?_, ?_⟩ <;> simp [m]

end QAlgorithms.Papers.Independent.Intakethird100.P21


