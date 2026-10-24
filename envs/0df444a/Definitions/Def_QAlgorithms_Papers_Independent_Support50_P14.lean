-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14
-- name    : QAlgorithms_Papers_Independent_Support50_P14
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-23T19:25:54.995038+00:00
-- url     : https://prove2.me/theorems/04a3381a-1416-4d5e-aff6-02c86c5f8da1
-- title:
--   Definitions for Extremality of Gaussian quantum states
-- statement:
--   The objects the formalized statements of *Extremality of Gaussian quantum states* (arXiv:quant-ph/0509154) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `OscillatorKernel`: PDF p.1: coefficients on the completed oscillator Hilbert space.
--   - `InterleavedQuadrature`: PDF p.1: interleaved canonical coordinates, second coordinate 0=Q, 1=P.
--   - `OscillatorCovariance`: PDF p.1: real symmetric covariance matrices are required in CompleteMoments.
--   - `oscillatorWeylKernel`: PDF p.1, (1): bounded Weyl kernel exp(i xi.R), with hbar=1.
--   - `oscillatorCharacteristic`: PDF p.1: trace-class/bounded pairing, multiplication before diagonal trace.
--   - `OscillatorCharacteristicSummable`: Genuine convergence guards for the two iterated sums in the Weyl pairing.
--   - `meanForm`: PDF p.1: xi dot d.
--   - `varianceForm`: PDF p.1: the full covariance quadratic form.
--   - `photonEnergy`: PDF p.1: extended mean photon number, on positive densities. The finite zero-point term does not affect finiteness.
--   - `CompleteMoments`: PDF p.1, moments preceding (1): finite oscillator energy and all directional first/second derivatives of the actual characteristic function. Symmetry is explicit: directional quadratic forms alone cannot determine an antisymmetric part. For a density these derivatives are precisely the finite symmetric quadrature moments, including the subtraction of d d^T from the second moment.
--   - `GaussianAt`: PDF p.1, (1): Gaussianity of this density with these actual moments. The density condition is supplied by State, never by a covariance-only surrogate.
--   - `InDomain`: PDF p.2: no cap means all densities. A finite cap e bounds mean photon number by e times the number of modes. These compatible compact sublevels scale on tensor powers; the centering and passive copy mixers used in the proof and their single-copy marginals remain within the respective sublevels.
--   - `MultipartiteOscillatorFunctional`: PDF pp.1--2: the functional is a family BEFORE choosing any input. Arbitrary finite mode labels and ownership maps support copies and regrouping. Values on arrays outside the specified density domain are unused.
--   - `oscillatorTensor`: PDF p.2: the actual tensor product, regrouped into A+B oscillator modes.
--   - `marginalFirst`: PDF p.2: trace out precisely the B modes, retaining all A coherences.
--   - `marginalSecond`: PDF p.2: trace out precisely the A modes.
--   - `localKernel`: PDF pp.1--3: independent bounded unitaries at all parties, allowing arbitrary mixing of all modes/copies held by that party. A party's Hilbert space is the completed l2 of its entire occupation basis.
--   - `StronglySuperadditive`: PDF p.2, definition of strong super-additivity: BOTH the inequality on correlated inputs and equality on arbitrary product densities. Restricted-domain clauses are used only when all states in the clause belong to that domain.
--   - `LocallyInvariant`: PDF pp.1--2: invariance under independent local bounded unitaries and ownership-preserving mode relabelings. No Gaussification or entropy conclusion is included among these purely algebraic hypotheses.
--   - `OscillatorTraceContinuous`: PDF p.2: epsilon-delta continuity in full TRACE norm, relative to the normalized density domain.
--   - `TraceLowerSemicontinuous`: PDF p.2: lower semicontinuity, with open strict superlevel sets in the relative trace-norm topology. This is distinct from continuity.
--   - `hadamardEntry`: PDF p.2, (5): H=((1,1),(1,-1)) tensor m, in binary tensor order.
--   - `mixedArgument`: PDF p.2, (5)--(7): the contravariant Weyl argument of the real passive mixer.
--   - `copiesKernel`: PDF p.2, (3): actual independent copies of the given density, regrouped by mode.
--   - `copyMixerKernel`: PDF p.2: identical copy mixer at each oscillator site.
--   - `insertCopy`: Reinsert the retained copy and every discarded copy at their actual labels.
--   - `copyMarginal`: PDF p.2: computed marginal, tracing out all copy labels except k.
--   - `positiveEntries`: PDF p.2, (6)--(8): positive entries, either all or half the row.
--   - `counterexampleVector`: PDF p.3, (iv): the explicit normalized Schmidt vector on TWO complete modes.
--   - `counterexampleState`: PDF p.3, (iv): actual rank-one density coefficients, not its covariance.
--   - `negativityExampleCovariance`: PDF p.3: the explicit state's covariance in the p.1 vacuum-I convention.
--   - `transposeFirst`: PDF p.3: partial transpose of the first complete oscillator mode.
--   - `logarithmicNegativity`: PDF p.3: E_N=log_2 ||rho^(T_A)||_1. Every use below concludes finiteness and norm>=1, before converting the extended norm to a real logarithm.
-- source:
--   Extremality of Gaussian quantum states, arXiv:quant-ph/0509154v1, https://arxiv.org/abs/quant-ph/0509154v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P14
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P47
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20

/-!
Wolf--Giedke--Cirac, arXiv:quant-ph/0509154v1, PDF pp.1--4.
Full oscillator Hilbert spaces have countable occupation bases, without a cutoff.
Coordinates (mode,0),(mode,1) are interleaved Q,P; covariance is the full
anticommutator, vacuum I. No Gaussian-limit or entropy identity is an axiom of
any functional. Operational applications not yet represented are in HARD.md.
Compilation is pending the separate batch handoff.
-/

noncomputable section

open Filter
open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Support50.P14

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClass traceSize)
open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)
open QAlgorithms.Papers.Independent.Frontier30.P14
  (unitaryCoeff conjugateKernel boundedUnitaryConjugation)
open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedEntropyNats)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

/-!
Reuse audit (repair): Occupation is the accepted full oscillator label type;
Copies Bool m is the accepted register-power type specialized to binary labels.
No local aliases redeclare either one. The remaining descriptive names below
retain the previous bodies and distinguish incompatible accepted short names:
P32.Kernel is a classical box, P10.Phase uses grouped Fin n indices,
P04.Covariance fixes Fin n, Information100.P34.weyl is a finite clock/shift,
P39.characteristic takes a one-mode bounded operator, P19.CharacteristicSummable
fixes Fin n and one Weyl argument, P30.Functional has finite-dimensional inputs,
Information100.P21.tensor takes two vectors, Next46.P27.TraceContinuous maps INTO
one-mode operators, and Gap48.P13.counterexampleCovariance is a different complex
six-by-six matrix. ASSESSMENT.json records each exact declaration separately.
The defective P47.HasBipartiteMoments is never used.
-/

/-- PDF p.1: coefficients on the completed oscillator Hilbert space. -/
abbrev OscillatorKernel (I : Type) := Matrix (Occupation I) (Occupation I) ℂ

/-- PDF p.1: interleaved canonical coordinates, second coordinate 0=Q, 1=P. -/
abbrev InterleavedQuadrature (I : Type) := I × Fin 2

/-- PDF p.1: real symmetric covariance matrices are required in CompleteMoments. -/
abbrev OscillatorCovariance (I : Type) := Matrix (InterleavedQuadrature I) (InterleavedQuadrature I) ℝ

/-- PDF p.1, (1): bounded Weyl kernel exp(i xi.R), with hbar=1. -/
def oscillatorWeylKernel {I : Type} [Fintype I] (xi : InterleavedQuadrature I → ℝ) : OscillatorKernel I :=
  fun u v => ∏ j, displacementMatrix
    ((-(xi (j, 1) : ℂ) + Complex.I * (xi (j, 0) : ℂ)) / (Real.sqrt 2 : ℂ))
    (u j) (v j)

/-- PDF p.1: trace-class/bounded pairing, multiplication before diagonal trace. -/
def oscillatorCharacteristic {I : Type} [Fintype I] (rho : OscillatorKernel I) (xi : InterleavedQuadrature I → ℝ) : ℂ :=
  ∑' u, ∑' v, rho u v * oscillatorWeylKernel xi v u

/-- Genuine convergence guards for the two iterated sums in the Weyl pairing. -/
def OscillatorCharacteristicSummable {I : Type} [Fintype I] (rho : OscillatorKernel I) : Prop :=
  ∀ xi : InterleavedQuadrature I → ℝ,
    (∀ u, Summable (fun v => rho u v * oscillatorWeylKernel xi v u)) ∧
    Summable (fun u => ∑' v, rho u v * oscillatorWeylKernel xi v u)

/-- PDF p.1: xi dot d. -/
def meanForm {I : Type} [Fintype I] (d xi : InterleavedQuadrature I → ℝ) : ℝ :=
  ∑ a, xi a * d a

/-- PDF p.1: the full covariance quadratic form. -/
def varianceForm {I : Type} [Fintype I] (gamma : OscillatorCovariance I) (xi : InterleavedQuadrature I → ℝ) : ℝ :=
  ∑ a, ∑ b, xi a * gamma a b * xi b

/-- PDF p.1: extended mean photon number, on positive densities.
The finite zero-point term does not affect finiteness. -/
def photonEnergy {I : Type} [Fintype I] (rho : OscillatorKernel I) : ℝ≥0∞ :=
  ∑' u : Occupation I, ENNReal.ofReal (∑ j, (u j : ℝ)) * ENNReal.ofReal (rho u u).re

/-- PDF p.1, moments preceding (1): finite oscillator energy and all directional
first/second derivatives of the actual characteristic function. Symmetry is
explicit: directional quadratic forms alone cannot determine an antisymmetric
part. For a density these derivatives are precisely the finite symmetric
quadrature moments, including the subtraction of d d^T from the second moment. -/
def CompleteMoments {I : Type} [Fintype I] (rho : OscillatorKernel I)
    (d : InterleavedQuadrature I → ℝ) (gamma : OscillatorCovariance I) : Prop :=
  photonEnergy rho < ⊤ ∧ gamma.transpose = gamma ∧ OscillatorCharacteristicSummable rho ∧
  ∀ xi : InterleavedQuadrature I → ℝ,
    HasDerivAt (fun t : ℝ => oscillatorCharacteristic rho (t • xi))
      (Complex.I * (meanForm d xi : ℂ)) 0 ∧
    HasDerivAt (deriv (fun t : ℝ => oscillatorCharacteristic rho (t • xi)))
      (((-varianceForm gamma xi / 2 - (meanForm d xi) ^ 2 : ℝ) : ℂ)) 0

/-- PDF p.1, (1): Gaussianity of this density with these actual moments.
The density condition is supplied by State, never by a covariance-only surrogate. -/
def GaussianAt {I : Type} [Fintype I] (rho : OscillatorKernel I)
    (d : InterleavedQuadrature I → ℝ) (gamma : OscillatorCovariance I) : Prop :=
  CompleteMoments rho d gamma ∧ ∀ xi : InterleavedQuadrature I → ℝ,
    oscillatorCharacteristic rho xi = Complex.exp
      (((-varianceForm gamma xi / 4 : ℝ) : ℂ) + Complex.I * (meanForm d xi : ℂ))

/-- PDF p.2: no cap means all densities. A finite cap e bounds mean photon
number by e times the number of modes. These compatible compact sublevels
scale on tensor powers; the centering and passive copy mixers used in the proof
and their single-copy marginals remain within the respective sublevels. -/
def InDomain {I : Type} [Fintype I] (cap : Option ℝ) (rho : OscillatorKernel I) : Prop :=
  IsDensity rho ∧ match cap with
    | none => True
    | some e => photonEnergy rho ≤ ENNReal.ofReal (e * Fintype.card I)

/-- PDF pp.1--2: the functional is a family BEFORE choosing any input.
Arbitrary finite mode labels and ownership maps support copies and regrouping.
Values on arrays outside the specified density domain are unused. -/
abbrev MultipartiteOscillatorFunctional (M : ℕ) :=
  (I : Type) → [Fintype I] → (I → Fin M) → OscillatorKernel I → ℝ

/-- PDF p.2: the actual tensor product, regrouped into A+B oscillator modes. -/
def oscillatorTensor {A B : Type} (rho : OscillatorKernel A) (sigma : OscillatorKernel B) : OscillatorKernel (A ⊕ B) :=
  fun u v => rho (u ∘ Sum.inl) (v ∘ Sum.inl) * sigma (u ∘ Sum.inr) (v ∘ Sum.inr)

/-- PDF p.2: trace out precisely the B modes, retaining all A coherences. -/
def marginalFirst {A B : Type} (rho : OscillatorKernel (A ⊕ B)) : OscillatorKernel A :=
  fun u v => ∑' w : Occupation B, rho (Sum.elim u w) (Sum.elim v w)

/-- PDF p.2: trace out precisely the A modes. -/
def marginalSecond {A B : Type} (rho : OscillatorKernel (A ⊕ B)) : OscillatorKernel B :=
  fun u v => ∑' w : Occupation A, rho (Sum.elim w u) (Sum.elim w v)

/-- PDF pp.1--3: independent bounded unitaries at all parties, allowing arbitrary
mixing of all modes/copies held by that party. A party's Hilbert space is the
completed l2 of its entire occupation basis. -/
def localKernel {M : ℕ} {I : Type} [Fintype I] (owner : I → Fin M)
    (U : (p : Fin M) → Hilbert (Occupation {j : I // owner j = p}) ≃ₗᵢ[ℂ]
      Hilbert (Occupation {j : I // owner j = p})) : OscillatorKernel I :=
  fun u v => ∏ p, unitaryCoeff (U p) (fun j => u j.val) (fun j => v j.val)

/-- PDF p.2, definition of strong super-additivity: BOTH the inequality on
correlated inputs and equality on arbitrary product densities. Restricted-domain
clauses are used only when all states in the clause belong to that domain. -/
def StronglySuperadditive {M : ℕ} (cap : Option ℝ) (f : MultipartiteOscillatorFunctional M) : Prop :=
  (∀ (A B : Type) [Fintype A] [Fintype B]
    (a : A → Fin M) (b : B → Fin M) (rho : OscillatorKernel (A ⊕ B)),
    InDomain cap rho → InDomain cap (marginalFirst rho) →
    InDomain cap (marginalSecond rho) →
    f A a (marginalFirst rho) + f B b (marginalSecond rho) ≤
      f (A ⊕ B) (Sum.elim a b) rho) ∧
  (∀ (A B : Type) [Fintype A] [Fintype B]
    (a : A → Fin M) (b : B → Fin M) (rho : OscillatorKernel A) (sigma : OscillatorKernel B),
    InDomain cap rho → InDomain cap sigma → InDomain cap (oscillatorTensor rho sigma) →
    f (A ⊕ B) (Sum.elim a b) (oscillatorTensor rho sigma) = f A a rho + f B b sigma)

/-- PDF pp.1--2: invariance under independent local bounded unitaries and
ownership-preserving mode relabelings. No Gaussification or entropy conclusion
is included among these purely algebraic hypotheses. -/
def LocallyInvariant {M : ℕ} (cap : Option ℝ) (f : MultipartiteOscillatorFunctional M) : Prop :=
  (∀ (I : Type) [Fintype I] (owner : I → Fin M) (rho : OscillatorKernel I)
    (U : (p : Fin M) → Hilbert (Occupation {j : I // owner j = p}) ≃ₗᵢ[ℂ]
      Hilbert (Occupation {j : I // owner j = p})),
    InDomain cap rho → InDomain cap (conjugateKernel (localKernel owner U) rho) →
    f I owner (conjugateKernel (localKernel owner U) rho) = f I owner rho) ∧
  (∀ (I J : Type) [Fintype I] [Fintype J] (e : I ≃ J)
    (owner : J → Fin M) (rho : OscillatorKernel I), InDomain cap rho →
    InDomain cap (fun u v => rho (u ∘ e) (v ∘ e)) →
    f J owner (fun u v => rho (u ∘ e) (v ∘ e)) = f I (owner ∘ e) rho)

/-- PDF p.2: epsilon-delta continuity in full TRACE norm, relative to the
normalized density domain. -/
def OscillatorTraceContinuous {M : ℕ} (cap : Option ℝ) (f : MultipartiteOscillatorFunctional M) : Prop :=
  ∀ (I : Type) [Fintype I] (owner : I → Fin M) (rho : OscillatorKernel I),
    InDomain cap rho → ∀ epsilon : ℝ, 0 < epsilon →
    ∃ delta : ℝ, 0 < delta ∧ ∀ sigma : OscillatorKernel I, InDomain cap sigma →
      traceSize (sigma - rho) < ENNReal.ofReal delta →
      |f I owner sigma - f I owner rho| < epsilon

/-- PDF p.2: lower semicontinuity, with open strict superlevel sets in the
relative trace-norm topology. This is distinct from continuity. -/
def TraceLowerSemicontinuous {M : ℕ} (cap : Option ℝ) (f : MultipartiteOscillatorFunctional M) : Prop :=
  ∀ (I : Type) [Fintype I] (owner : I → Fin M) (rho : OscillatorKernel I),
    InDomain cap rho → ∀ a : ℝ, a < f I owner rho →
    ∃ delta : ℝ, 0 < delta ∧ ∀ sigma : OscillatorKernel I, InDomain cap sigma →
      traceSize (sigma - rho) < ENNReal.ofReal delta → a < f I owner sigma

/-- PDF p.2, (5): H=((1,1),(1,-1)) tensor m, in binary tensor order. -/
def hadamardEntry (m : ℕ) (k l : Copies Bool m) : ℝ :=
  (-1 : ℝ) ^ (∑ j : Fin m, if k j = true ∧ l j = true then 1 else 0)

/-- PDF p.2, (5)--(7): the contravariant Weyl argument of the real passive mixer. -/
def mixedArgument (m : ℕ) (xi : InterleavedQuadrature (Copies Bool m) → ℝ) : InterleavedQuadrature (Copies Bool m) → ℝ :=
  fun l => ∑ k : Copies Bool m, hadamardEntry m k l.1 /
    Real.sqrt ((2 : ℝ) ^ m) * xi (k, l.2)

/-- PDF p.2, (3): actual independent copies of the given density, regrouped by mode. -/
def copiesKernel {I : Type} (m : ℕ) (rho : OscillatorKernel I) : OscillatorKernel (I × Copies Bool m) :=
  fun u v => ∏ k : Copies Bool m, rho (fun j => u (j, k)) (fun j => v (j, k))

/-- PDF p.2: identical copy mixer at each oscillator site. -/
def copyMixerKernel {I : Type} [Fintype I] (m : ℕ)
    (U : Hilbert (Occupation (Copies Bool m)) ≃ₗᵢ[ℂ] Hilbert (Occupation (Copies Bool m))) :
    OscillatorKernel (I × Copies Bool m) :=
  fun u v => ∏ j, unitaryCoeff U (fun k => u (j, k)) (fun k => v (j, k))

/-- Reinsert the retained copy and every discarded copy at their actual labels. -/
def insertCopy {I : Type} {m : ℕ} (k : Copies Bool m) (u : Occupation I)
    (rest : Occupation (I × {l : Copies Bool m // l ≠ k})) : Occupation (I × Copies Bool m) :=
  fun p => if h : p.2 = k then u p.1 else rest (p.1, ⟨p.2, h⟩)

/-- PDF p.2: computed marginal, tracing out all copy labels except k. -/
def copyMarginal {I : Type} {m : ℕ} (rho : OscillatorKernel (I × Copies Bool m)) (k : Copies Bool m) : OscillatorKernel I :=
  fun u v => ∑' rest : Occupation (I × {l : Copies Bool m // l ≠ k}),
    rho (insertCopy k u rest) (insertCopy k v rest)

/-- PDF p.2, (6)--(8): positive entries, either all or half the row. -/
def positiveEntries (m : ℕ) (k : Copies Bool m) : ℕ :=
  if k = (fun _ => false) then 2 ^ m else 2 ^ m / 2

/-- PDF p.3, (iv): the explicit normalized Schmidt vector on TWO complete modes. -/
def counterexampleVector (u : Occupation (Fin 2)) : ℂ :=
  if u = (fun _ => 0) then (Real.sqrt 15 / 4 : ℝ)
  else if u = (fun _ => 1) then (1 / 4 : ℝ) else 0

/-- PDF p.3, (iv): actual rank-one density coefficients, not its covariance. -/
def counterexampleState : OscillatorKernel (Fin 2) :=
  fun u v => counterexampleVector u * star (counterexampleVector v)

/-- PDF p.3: the explicit state's covariance in the p.1 vacuum-I convention. -/
def negativityExampleCovariance : OscillatorCovariance (Fin 2) :=
  fun a b => if a.1 = b.1 then (if a.2 = b.2 then 9 / 8 else 0)
    else if a.2 = b.2 then (if a.2 = 0 then Real.sqrt 15 / 8 else -Real.sqrt 15 / 8)
    else 0

/-- PDF p.3: partial transpose of the first complete oscillator mode. -/
def transposeFirst (rho : OscillatorKernel (Fin 2)) : Matrix (ℕ × ℕ) (ℕ × ℕ) ℂ :=
  fun u v => rho ![v.1, u.2] ![u.1, v.2]

/-- PDF p.3: E_N=log_2 ||rho^(T_A)||_1. Every use below concludes finiteness
and norm>=1, before converting the extended norm to a real logarithm. -/
def logarithmicNegativity (rho : OscillatorKernel (Fin 2)) : ℝ :=
  Real.logb 2 (traceSize (transposeFirst rho)).toReal

/-! Sanity examples pin definitions only; source results remain unproved. -/

example {I : Type} [Fintype I] (gamma : OscillatorCovariance I) : varianceForm gamma 0 = 0 := by
  simp [varianceForm]

example {I : Type} [Fintype I] (rho : OscillatorKernel I) :
    InDomain none rho ↔ IsDensity rho := by simp [InDomain]

example {A B : Type} (rho : OscillatorKernel A) (sigma : OscillatorKernel B) (u v : Occupation (A ⊕ B)) :
    oscillatorTensor rho sigma u v = rho (u ∘ Sum.inl) (v ∘ Sum.inl) *
      sigma (u ∘ Sum.inr) (v ∘ Sum.inr) := rfl

example {I : Type} {m : ℕ} (k : Copies Bool m) (u : Occupation I)
    (rest : Occupation (I × {l : Copies Bool m // l ≠ k})) (j : I) :
    insertCopy k u rest (j, k) = u j := by simp [insertCopy]

example : hadamardEntry 0 (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) = 1 := by
  simp [hadamardEntry]

example (m : ℕ) : positiveEntries m (fun _ => false) = 2 ^ m := by
  simp [positiveEntries]

example : negativityExampleCovariance (0, 0) (1, 0) = Real.sqrt 15 / 8 := by
  norm_num [negativityExampleCovariance]

example : negativityExampleCovariance (0, 1) (1, 1) = -Real.sqrt 15 / 8 := by
  norm_num [negativityExampleCovariance]

example (rho : OscillatorKernel (Fin 2)) : transposeFirst rho (0, 1) (1, 0) = rho ![1, 1] ![0, 0] := rfl

end QAlgorithms.Papers.Independent.Support50.P14


