-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P37
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P37
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T05:18:37.175992+00:00
-- url     : https://prove2.me/theorems/f84ab5ab-1990-4c7d-b19d-3e13f827ab50
-- title:
--   Definitions for Low dimensional bound entanglement with one-way distillable cryptographic key
-- statement:
--   The objects the formalized statements of *Low dimensional bound entanglement with one-way distillable cryptographic key* (arXiv:quant-ph/0506203) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `flipAlice`: PDF p.1, Eq.(1): conjugation by the Pauli X on Alice's KEY qubit only.
--   - `privateMixture`: PDF p.1, Eq.(1): biased even/odd private-bit mixture.
--   - `physicalFin`: PDF pp.1--3: same physical AA':BB' matrix, enumerating each party's key/shield pair with the accepted fixed local enumeration.
--   - `measuredSource`: PDF pp.1--2: the actual measured ccq source, reparenthesized A:(B:E). The shield remains unavailable to Eve; it is traced out by associatedCCQ.
--   - `measuredBE`: PDF p.1, Eq.(2): unnormalized conditional BE block for Alice's measured bit.
--   - `measuredAliceLaw`: PDF pp.1--2: Alice's actual measured-bit law.
--   - `HasMeasuredOneWayRate`: PDF pp.1--2: forward public discussion after the specified key measurement. One sequence is chosen before EVERY finite purifying Eve. The accepted protocol includes its public transcript in Eve's output; errors vanish on i.i.d. copies. Zero-mass conditional states use the accepted normalized fallback.
--   - `weightedSwap`: PDF p.2, Eq.(10): the computed weighted swap W_U, with row (i,j), column (j,i).
--   - `entrySum`: PDF p.2: the entrywise l1 sum equals the trace norm of W_U.
--   - `weightOne`: PDF p.2, Eq.(11): the first mixing weight, computed from U.
--   - `weightTwo`: PDF p.2, Eq.(11): the second mixing weight, computed from U.
--   - `rhoUnitary`: PDF p.2, Eqs.(9)--(11): exactly the two X-form blocks of the construction. The two square roots in xForm are kept distinct, as required for complex U. The partial transpose in X2 acts on B' alone. Because flipAlice exchanges 00 with 10 and 11 with 01, its private-bit argument must be xForm (X2 adjoint) to put X2 in the (01,10) block required by Eq.(9).
--   - `nonzeroEntries`: PDF p.2 after Eq.(12): number of nonzero matrix entries in the named basis.
--   - `IsFlatUnitary`: PDF pp.2--3, Observation 1: source's normalized meaning of unimodular.
--   - `rhoHadamard`: PDF p.3, Eqs.(13)--(16): the particular computed 4 by 4 bipartite resource.
--   - `hadamardRate`: PDF p.3, Eq.(16): exact yield in bits per independent input copy. The printed decimal is rounded, not an equality to a terminating decimal.
--   - `pairKet`: PDF p.2, Eqs.(4)--(5): normalized Bell-type vector. For the odd pair the second ket is |10>, correcting the duplicated |01> printed in Eq.(5).
--   - `chiKet`: PDF p.3, Eq.(15): the two normalized chi vectors; true selects chi minus.
--   - `hadamardFlag`: PDF p.3, Eq.(14): shield flags in the four Bell branches.
--   - `hadamardWeight`: PDF p.3, below Eq.(15): the four fixed preparation probabilities.
--   - `pptSet`: PDF p.3, Observation 2: all normalized PPT states, not a mixing line.
--   - `IsPPTWithKey`: PDF p.3, Observation 3: physical PPT states with positive distillable key.
--   - `squaredDistance`: PDF p.3, volume argument: squared Hilbert--Schmidt distance, giving full balls in the real affine space of Hermitian trace-one matrices.
--   - `embeddedHadamard`: PDF p.3, higher-dimensional extension: local isometric embedding of the 4 by 4 example, with zero outside the first four basis labels at each party.
--   - `noisyEmbeddedHadamard`: PDF p.3, Observation 3 proof: add full-dimensional white noise with signal weight q close to one. A ball is centered at this noisy state.
--   - `IsCCQ`: PDF pp.1,3, Eqs.(2),(17): A and B are classical in the named basis.
--   - `dephaseAB`: PDF pp.3--4: computational-basis measurement of both honest key registers.
--   - `bellPinching`: PDF p.4, Eq.(18): actual pinching in the four standard Bell projectors.
--   - `twirledExpression`: PDF p.4, Eq.(18): the experimentally estimated lower-bound expression.
--   - `realCoherence`: PDF p.4, Eq.(19): real-coherence Bell-projector difference.
--   - `imagCoherence`: PDF p.4, Eq.(19): imaginary-coherence difference. We fix the first tilde Bell ket to phase -i and the second to +i; its mean is +2 Im sigma_(first,second).
--   - `keyObservable`: PDF p.4, Eq.(19): all five specified key observables in one finite family.
--   - `physicalObservable`: PDF p.4, Eq.(19): conjugated physical observable on ABA'B'.
-- source:
--   Low dimensional bound entanglement with one-way distillable cryptographic key, arXiv:quant-ph/0506203v1, https://arxiv.org/abs/quant-ph/0506203v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P12
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P42

/-!
Horodecki--Pankowski--Horodecki--Horodecki, quant-ph/0506203v1, PDF pp.1--4.
Coordinates are ABA'B'; physical entanglement always uses AA':BB'.
All operational interfaces are from the pinned accepted library. New definitions
are confined to this module. Twisting is an analytical operation, never a claimed
LOCC implementation. Printed corrections and deferred nodes are in the unit's
MODERATION_NOTES.md and HARD.md. Compilation is pending batch handoff.
-/

noncomputable section

open scoped Matrix BigOperators ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P37

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open QAlgorithms.Papers.Independent.Dependency50.P24
  (Key IsPrivate xForm twist twistingMatrix associatedCCQ transposeSecond transposeBob partyCut)

/-- PDF p.1, Eq.(1): conjugation by the Pauli X on Alice's KEY qubit only. -/
def flipAlice {a b : ℕ} (rho : Op (Key 2 × (Fin a × Fin b))) : Op (Key 2 × (Fin a × Fin b)) :=
  fun x y => rho
    (((if x.1.1 = 0 then 1 else 0), x.1.2), x.2)
    (((if y.1.1 = 0 then 1 else 0), y.1.2), y.2)

/-- PDF p.1, Eq.(1): biased even/odd private-bit mixture. -/
def privateMixture {a b : ℕ} (p1 p2 : ℝ) (gamma1 gamma2 : Op (Key 2 × (Fin a × Fin b))) :
    Op (Key 2 × (Fin a × Fin b)) := (p1 : ℂ) • gamma1 + (p2 : ℂ) • flipAlice gamma2

/-- PDF pp.1--3: same physical AA':BB' matrix, enumerating each party's
key/shield pair with the accepted fixed local enumeration. -/
def physicalFin {a b : ℕ} (rho : Op (Key 2 × (Fin a × Fin b))) : Op (Fin (2*a) × Fin (2*b)) :=
  fun x y => partyCut rho
    ((Gap48.P42.localIndex 2 a).symm x.1, (Gap48.P42.localIndex 2 b).symm x.2)
    ((Gap48.P42.localIndex 2 a).symm y.1, (Gap48.P42.localIndex 2 b).symm y.2)

/-- PDF pp.1--2: the actual measured ccq source, reparenthesized A:(B:E).
The shield remains unavailable to Eve; it is traced out by associatedCCQ. -/
def measuredSource {a b e : ℕ} (psi : EuclideanSpace ℂ ((Key 2 × (Fin a × Fin b)) × Fin e)) :
    Op (Fin 2 × (Fin 2 × Fin e)) :=
  fun x y => associatedCCQ psi ((x.1,x.2.1),x.2.2) ((y.1,y.2.1),y.2.2)

/-- PDF p.1, Eq.(2): unnormalized conditional BE block for Alice's measured bit. -/
def measuredBE {a b e : ℕ} (psi : EuclideanSpace ℂ ((Key 2 × (Fin a × Fin b)) × Fin e))
    (i : Fin 2) : Op (Fin 2 × Fin e) :=
  fun x y => measuredSource psi (i,x) (i,y)

/-- PDF pp.1--2: Alice's actual measured-bit law. -/
def measuredAliceLaw {a b e : ℕ} (psi : EuclideanSpace ℂ ((Key 2 × (Fin a × Fin b)) × Fin e))
    (i : Fin 2) : ℝ := (measuredBE psi i).trace.re

/-- PDF pp.1--2: forward public discussion after the specified key measurement.
One sequence is chosen before EVERY finite purifying Eve. The accepted protocol
includes its public transcript in Eve's output; errors vanish on i.i.d. copies.
Zero-mass conditional states use the accepted normalized fallback. -/
def HasMeasuredOneWayRate {a b : ℕ} (rho : Op (Key 2 × (Fin a × Fin b))) (r : ℝ) : Prop :=
  ∃ P : (n : ℕ) → Frontier30.P12.CqqProtocol (Fin 2) (Fin 2) n,
    ∀ e : ℕ, 0 < e → ∀ psi : EuclideanSpace ℂ ((Key 2 × (Fin a × Fin b)) × Fin e),
      ‖psi‖ = 1 → traceRight (pureDensity psi) = rho →
      Frontier30.P12.CqqAchieves (measuredAliceLaw psi)
        (fun i => Frontier30.P12.normalized (measuredBE psi i)) P r

/-- PDF p.2, Eq.(10): the computed weighted swap W_U, with row (i,j), column (j,i). -/
def weightedSwap {d : ℕ} (U : Op (Fin d)) : Op (Fin d × Fin d) :=
  fun x y => if x.1 = y.2 ∧ x.2 = y.1 then U x.1 x.2 else 0

/-- PDF p.2: the entrywise l1 sum equals the trace norm of W_U. -/
def entrySum {d : ℕ} (U : Op (Fin d)) : ℝ := ∑ i, ∑ j, ‖U i j‖

/-- PDF p.2, Eq.(11): the first mixing weight, computed from U. -/
def weightOne {d : ℕ} (U : Op (Fin d)) : ℝ := entrySum U / (entrySum U + d)

/-- PDF p.2, Eq.(11): the second mixing weight, computed from U. -/
def weightTwo {d : ℕ} (U : Op (Fin d)) : ℝ := (d : ℝ) / (entrySum U + d)

/-- PDF p.2, Eqs.(9)--(11): exactly the two X-form blocks of the construction.
The two square roots in xForm are kept distinct, as required for complex U.
The partial transpose in X2 acts on B' alone. Because flipAlice exchanges
00 with 10 and 11 with 01, its private-bit argument must be xForm (X2 adjoint)
to put X2 in the (01,10) block required by Eq.(9). -/
def rhoUnitary {d : ℕ} (U : Op (Fin d)) : Op (Key 2 × (Fin d × Fin d)) :=
  privateMixture (weightOne U) (weightTwo U)
    (xForm (((entrySum U)⁻¹ : ℂ) • weightedSwap U))
    (xForm ((((d : ℝ)⁻¹ : ℂ) • transposeSecond (weightedSwap U))ᴴ))

/-- PDF p.2 after Eq.(12): number of nonzero matrix entries in the named basis. -/
def nonzeroEntries {d : ℕ} (U : Op (Fin d)) : ℕ :=
  (Finset.univ.filter fun ij : Fin d × Fin d => U ij.1 ij.2 ≠ 0).card

/-- PDF pp.2--3, Observation 1: source's normalized meaning of unimodular. -/
def IsFlatUnitary {d : ℕ} (U : Op (Fin d)) : Prop :=
  ∀ i j, ‖U i j‖ = 1 / Real.sqrt d

/-- PDF p.3, Eqs.(13)--(16): the particular computed 4 by 4 bipartite resource. -/
def rhoHadamard : Op (Key 2 × (Fin 2 × Fin 2)) :=
  rhoUnitary (fun i j : Fin 2 => QAlgorithms.hadamard (decide (i = 1)) (decide (j = 1)))

/-- PDF p.3, Eq.(16): exact yield in bits per independent input copy.
The printed decimal is rounded, not an equality to a terminating decimal. -/
def hadamardRate : ℝ := 1 - binEntropy2 (Real.sqrt 2 / (1 + Real.sqrt 2))

/-- PDF p.2, Eqs.(4)--(5): normalized Bell-type vector. For the odd pair the
second ket is |10>, correcting the duplicated |01> printed in Eq.(5). -/
def pairKet (odd : Bool) (phase : ℂ) : EuclideanSpace ℂ (Key 2) :=
  WithLp.toLp 2 fun x => ((Real.sqrt 2)⁻¹ : ℂ) *
    ((if x = (0, if odd then 1 else 0) then 1 else 0) +
      (if x = (1, if odd then 0 else 1) then phase else 0))

/-- PDF p.3, Eq.(15): the two normalized chi vectors; true selects chi minus. -/
def chiKet (minus : Bool) : EuclideanSpace ℂ (Key 2) :=
  WithLp.toLp 2 fun x =>
    if x = (0,0) then
      ((Real.sqrt (2 + (if minus then -Real.sqrt 2 else Real.sqrt 2)) / 2 : ℝ) : ℂ)
    else if x = (1,1) then
      (((if minus then -1 else 1) *
        Real.sqrt (2 - (if minus then -Real.sqrt 2 else Real.sqrt 2)) / 2 : ℝ) : ℂ)
    else 0

/-- PDF p.3, Eq.(14): shield flags in the four Bell branches. -/
def hadamardFlag (i : Fin 4) : Op (Key 2) :=
  ![(1/2 : ℂ) • (pureDensity (ket (0,0)) + pureDensity ((pairKet true 1))),
    (1/2 : ℂ) • (pureDensity (ket (1,1)) + pureDensity ((pairKet true (-1)))),
    pureDensity (chiKet false), pureDensity (chiKet true)] i

/-- PDF p.3, below Eq.(15): the four fixed preparation probabilities. -/
def hadamardWeight (i : Fin 4) : ℝ :=
  ![weightOne (fun i j : Fin 2 => QAlgorithms.hadamard (decide (i = 1)) (decide (j = 1))) / 2, weightOne (fun i j : Fin 2 => QAlgorithms.hadamard (decide (i = 1)) (decide (j = 1))) / 2,
    weightTwo (fun i j : Fin 2 => QAlgorithms.hadamard (decide (i = 1)) (decide (j = 1))) / 2, weightTwo (fun i j : Fin 2 => QAlgorithms.hadamard (decide (i = 1)) (decide (j = 1))) / 2] i

/-- PDF p.3, Observation 2: all normalized PPT states, not a mixing line. -/
def pptSet {a b : ℕ} : Set (Op (Key 2 × (Fin a × Fin b))) :=
  {rho | IsDensityMatrix rho ∧ (transposeBob rho).PosSemidef}

/-- PDF p.3, Observation 3: physical PPT states with positive distillable key. -/
def IsPPTWithKey {m n : ℕ} (rho : Op (Fin m × Fin n)) : Prop :=
  IsDensityMatrix rho ∧ (Information100.P21.pt rho).PosSemidef ∧
    0 < Gap48.P42.distillableKey rho

/-- PDF p.3, volume argument: squared Hilbert--Schmidt distance, giving full
balls in the real affine space of Hermitian trace-one matrices. -/
def squaredDistance {I : Type} [Fintype I] (rho sigma : Op I) : ℝ :=
  ∑ i, ∑ j, ‖rho i j - sigma i j‖ ^ 2

/-- PDF p.3, higher-dimensional extension: local isometric embedding of the
4 by 4 example, with zero outside the first four basis labels at each party. -/
def embeddedHadamard (m n : ℕ) : Op (Fin m × Fin n) :=
  fun x y => if h : x.1.val < 4 ∧ x.2.val < 4 ∧ y.1.val < 4 ∧ y.2.val < 4 then
    physicalFin rhoHadamard
      (⟨x.1.val,h.1⟩,⟨x.2.val,h.2.1⟩) (⟨y.1.val,h.2.2.1⟩,⟨y.2.val,h.2.2.2⟩)
    else 0

/-- PDF p.3, Observation 3 proof: add full-dimensional white noise with signal
weight q close to one. A ball is centered at this noisy state. -/
def noisyEmbeddedHadamard (m n : ℕ) (q : ℝ) : Op (Fin m × Fin n) :=
  (q : ℂ) • embeddedHadamard m n + (((1-q) / (m*n) : ℝ) : ℂ) • 1

/-- PDF pp.1,3, Eqs.(2),(17): A and B are classical in the named basis. -/
def IsCCQ {a b e : ℕ} (rho : Op (Fin a × (Fin b × Fin e))) : Prop :=
  ∀ x y, x.1 ≠ y.1 ∨ x.2.1 ≠ y.2.1 → rho x y = 0

/-- PDF pp.3--4: computational-basis measurement of both honest key registers. -/
def dephaseAB {a b e : ℕ} (rho : Op (Fin a × (Fin b × Fin e))) :
    Op (Fin a × (Fin b × Fin e)) :=
  fun x y => if x.1 = y.1 ∧ x.2.1 = y.2.1 then rho x y else 0

/-- PDF p.4, Eq.(18): actual pinching in the four standard Bell projectors. -/
def bellPinching (sigma : Op (Key 2)) : Op (Key 2) :=
  ∑ i : Fin 4, pureDensity (((![pairKet false 1, pairKet false (-1), pairKet true 1, pairKet true (-1)]) i)) * sigma * pureDensity (((![pairKet false 1, pairKet false (-1), pairKet true 1, pairKet true (-1)]) i))

/-- PDF p.4, Eq.(18): the experimentally estimated lower-bound expression. -/
def twirledExpression (sigma : Op (Key 2)) : ℝ :=
  mutualInfoBits (fun k => (sigma k k).re) - vnEntropy (bellPinching sigma)

/-- PDF p.4, Eq.(19): real-coherence Bell-projector difference. -/
def realCoherence (odd : Bool) : Op (Key 2) :=
  pureDensity (pairKet odd 1) - pureDensity (pairKet odd (-1))

/-- PDF p.4, Eq.(19): imaginary-coherence difference. We fix the first tilde
Bell ket to phase -i and the second to +i; its mean is +2 Im sigma_(first,second). -/
def imagCoherence (odd : Bool) : Op (Key 2) :=
  pureDensity (pairKet odd (-Complex.I)) - pureDensity (pairKet odd Complex.I)

/-- PDF p.4, Eq.(19): all five specified key observables in one finite family. -/
def keyObservable (i : Fin 5) : Op (Key 2) :=
  ![(Matrix.diagonal (fun k : Key 2 => if k.1 = k.2 then (1 : ℂ) else -1)), realCoherence false, imagCoherence false,
    realCoherence true, imagCoherence true] i

/-- PDF p.4, Eq.(19): conjugated physical observable on ABA'B'. -/
def physicalObservable {a b : ℕ}
    (U : Key 2 → Matrix.unitaryGroup (Fin a × Fin b) ℂ) (O : Op (Key 2)) :
    Op (Key 2 × (Fin a × Fin b)) :=
  (twistingMatrix U)ᴴ * Matrix.kronecker O (1 : Op (Fin a × Fin b)) * twistingMatrix U

/-- Sanity: W_I has unit (00,00) entry, pinning the row/column convention. -/
example : weightedSwap (1 : Op (Fin 2)) (0,0) (0,0) = 1 := by
  simp [weightedSwap]

/-- Sanity: the flip acts on Alice's key and leaves Bob and both shields fixed. -/
example {a b : ℕ} (rho : Op (Key 2 × (Fin a × Fin b))) (s t : Fin a × Fin b) :
    flipAlice rho ((0,0),s) ((1,1),t) = rho ((1,0),s) ((0,1),t) := by rfl

/-- Sanity: chi has no odd-parity shield amplitude. -/
example (minus : Bool) : chiKet minus (0,1) = 0 := by
  simp [chiKet]

/-- Sanity: an identical matrix has zero squared Hilbert--Schmidt distance. -/
example {I : Type} [Fintype I] (rho : Op I) : squaredDistance rho rho = 0 := by
  simp [squaredDistance]

end QAlgorithms.Papers.Independent.Intakenext100.P37


