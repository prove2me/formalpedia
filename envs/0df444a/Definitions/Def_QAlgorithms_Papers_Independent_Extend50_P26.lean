-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P26
-- name    : QAlgorithms_Papers_Independent_Extend50_P26
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T20:26:28.02957+00:00
-- url     : https://prove2.me/theorems/ab22b1d9-ac22-4da2-99e7-023afa536509
-- title:
--   Definitions for Reversing Unknown Quantum Transformations: Universal Quantum Circuit for Inverting General Unitary Operations
-- statement:
--   The objects the formalized statements of *Reversing Unknown Quantum Transformations: Universal Quantum Circuit for Inverting General Unitary Operations* (arXiv:1810.06944) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `InversionBasis`: PDF p.4, Eq.(4): n teeth ordered newest output/input first; order zero is scalar.
--   - `unitaryChoi`: PDF p.4, Choi definition: unnormalized |A>> <<A| in output-first coordinates.
--   - `inverseChoi`: PDF p.4, Eq.(4): Choi operator of the inverse channel, never inverse of a Choi matrix.
--   - `slotTensor`: PDF p.4, Eq.(4): tensor of k independently specified slot Choi operators. Slot zero is the newest slot; identical forward calls are obtained by a constant family.
--   - `endpoints`: PDF p.4: insert external output/input endpoints around the k open channel slots.
--   - `inversionLink`: PDF p.4, link product: contract slot indices with the slot Choi operator. The two identical index orders implement the partial transpose in the link product.
--   - `InversionComb`: PDF p.4, quantum-comb constraints: positive recursive prefixes and causal traces. The k-use circuit is a (k+1)-comb; its fixed channels may retain finite memory.
--   - `groupSlotPairs`: PDF p.3, Fig.4: regroup the k slot outputs and inputs into two collective wires.
--   - `CollectiveChannel`: PDF p.3, Fig.4: a CPTP channel on the collective k-qudit slot.
--   - `Parallel`: PDF pp.3–4: parallel superchannel, with arbitrary memory and pre/postprocessing. Positivity and normalization on every collective CPTP slot describe a single channel supermap; splitting that collective slot into k tensor factors leaves no intervening gates.
--   - `GeneralProcess`: PDF pp.3–4: the general process-matrix class, including indefinite causal order. Normalization is tested on arbitrary independent CPTP channels in all k slots. Positivity is the complete-positivity requirement, also with ancillary extensions.
--   - `CircuitClass`: PDF p.4, Table I: the three classes of deterministic completions.
--   - `InversionCompletion`: PDF p.4: deterministic admissibility in the specified circuit class.
--   - `HeraldedInversionBranch`: PDF p.4, Eq.(4): a heralded positive branch dominated by a deterministic completion. The complementary branch C-S is positive; no success or invertibility is assumed.
--   - `UniversalInverseBranch`: PDF pp.1–4: a fixed branch inverts every SU(d) oracle with the same input-independent p. Choi equality includes arbitrary reference-entangled inputs. Only forward U is inserted.
--   - `Attainable`: PDF p.4: the attainable success probabilities. The protocol is chosen before U. The budget counts k open forward-call slots; unused calls can be discarded.
--   - `FiniteFeasible`: PDF p.4, Eq.(4): success constraints at an explicitly specified finite family.
--   - `adaptiveInversionProbability`: PDF p.3, Theorem 1: number of complete attempts, with d-1 calls in the last attempt.
-- source:
--   Reversing Unknown Quantum Transformations: Universal Quantum Circuit for Inverting General Unitary Operations, arXiv:1810.06944v3, https://arxiv.org/abs/1810.06944v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26

/-!
Exact heralded universal inversion, arXiv:1810.06944v3, PDF pp.1–5.
The paper-local Choi coordinates are output first. Recursive comb coordinates are
newest output/input first. A k-query protocol has k+1 teeth; its k open slots
are filled only with forward channels. The general-process class is normalized
on arbitrary independent CPTP slot channels, not just on repeated unitaries.
No numerical Table I cell is promoted to an exact value.
-/

noncomputable section

open QAlgorithms
open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Extend50.P26

-- Reuse the accepted unnormalized output-first CPTP predicate, without an alias.
open QAlgorithms.Papers.Independent.Dependency50.P26 (ChannelChoi)

/-- PDF p.4, Eq.(4): n teeth ordered newest output/input first; order zero is scalar. -/
def InversionBasis (d : ℕ) : ℕ → Type
  | 0 => Unit
  | n + 1 => Fin d × (Fin d × InversionBasis d n)

/-- Finite coordinate bases, including the scalar empty prefix. -/
instance inversionBasisFintype (d : ℕ) : (n : ℕ) → Fintype (InversionBasis d n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => letI := inversionBasisFintype d n
             inferInstanceAs (Fintype (Fin d × (Fin d × InversionBasis d n)))

/-- PDF p.4, Choi definition: unnormalized |A>> <<A| in output-first coordinates. -/
def unitaryChoi {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : (Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :=
  fun a b => A a.1 a.2 * conj (A b.1 b.2)

/-- PDF p.4, Eq.(4): Choi operator of the inverse channel, never inverse of a Choi matrix. -/
def inverseChoi {d : ℕ} (U : (Matrix.specialUnitaryGroup (Fin d) ℂ)) : (Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) := unitaryChoi U.valᴴ

/-- PDF p.4, Eq.(4): tensor of k independently specified slot Choi operators.
Slot zero is the newest slot; identical forward calls are obtained by a constant family. -/
def slotTensor (d : ℕ) : (k : ℕ) → (Fin k → (Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)) → (Matrix (InversionBasis d k) (InversionBasis d k) ℂ)
  | 0, _ => 1
  | n + 1, J => fun a b =>
      J 0 (a.1, a.2.1) (b.1, b.2.1) *
        slotTensor d n (fun j => J j.succ) a.2.2 b.2.2

/-- PDF p.4: insert external output/input endpoints around the k open channel slots. -/
def endpoints (d : ℕ) : (k : ℕ) → Fin d → Fin d → InversionBasis d k → InversionBasis d (k+1)
  | 0, o, i, _ => (o, i, ())
  | n + 1, o, i, x => (o, x.1, endpoints d n x.2.1 i x.2.2)

/-- PDF p.4, link product: contract slot indices with the slot Choi operator.
The two identical index orders implement the partial transpose in the link product. -/
def inversionLink {d k : ℕ} (S : (Matrix (InversionBasis d (k+1)) (InversionBasis d (k+1)) ℂ)) (J : (Matrix (InversionBasis d k) (InversionBasis d k) ℂ)) : (Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :=
  fun a b => ∑ u, ∑ v,
    S (endpoints d k a.1 a.2 u) (endpoints d k b.1 b.2 v) * J u v

/-- PDF p.4, quantum-comb constraints: positive recursive prefixes and causal traces.
The k-use circuit is a (k+1)-comb; its fixed channels may retain finite memory. -/
def InversionComb (d : ℕ) : (n : ℕ) → (Matrix (InversionBasis d n) (InversionBasis d n) ℂ) → Prop
  | 0, C => C = 1
  | n + 1, C => C.PosSemidef ∧ ∃ B : (Matrix (InversionBasis d n) (InversionBasis d n) ℂ),
      InversionComb d n B ∧ traceLeft C = Matrix.kronecker (1 : Matrix (Fin d) _ ℂ) B

/-- PDF p.3, Fig.4: regroup the k slot outputs and inputs into two collective wires. -/
def groupSlotPairs (d : ℕ) : (k : ℕ) → (Fin k → Fin d) → (Fin k → Fin d) → InversionBasis d k
  | 0, _, _ => ()
  | n + 1, o, i => (o 0, i 0, groupSlotPairs d n (fun j => o j.succ) (fun j => i j.succ))

/-- PDF p.3, Fig.4: a CPTP channel on the collective k-qudit slot. -/
def CollectiveChannel {d k : ℕ} (J : (Matrix (InversionBasis d k) (InversionBasis d k) ℂ)) : Prop :=
  J.PosSemidef ∧ ∀ a b : Fin k → Fin d,
    (∑ o : Fin k → Fin d, J (groupSlotPairs d k o a) (groupSlotPairs d k o b)) =
      if a = b then 1 else 0

/-- PDF pp.3–4: parallel superchannel, with arbitrary memory and pre/postprocessing.
Positivity and normalization on every collective CPTP slot describe a single channel
supermap; splitting that collective slot into k tensor factors leaves no intervening gates. -/
def Parallel {d k : ℕ} (C : (Matrix (InversionBasis d (k+1)) (InversionBasis d (k+1)) ℂ)) : Prop :=
  C.PosSemidef ∧ ∀ J : (Matrix (InversionBasis d k) (InversionBasis d k) ℂ), CollectiveChannel J → ChannelChoi (inversionLink C J)

/-- PDF pp.3–4: the general process-matrix class, including indefinite causal order.
Normalization is tested on arbitrary independent CPTP channels in all k slots.
Positivity is the complete-positivity requirement, also with ancillary extensions. -/
def GeneralProcess {d k : ℕ} (C : (Matrix (InversionBasis d (k+1)) (InversionBasis d (k+1)) ℂ)) : Prop :=
  C.PosSemidef ∧ ∀ J : Fin k → (Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ),
    (∀ j, ChannelChoi (J j)) → ChannelChoi (inversionLink C (slotTensor d k J))

/-- PDF p.4, Table I: the three classes of deterministic completions. -/
inductive CircuitClass where
  | parallel
  | adaptive
  | indefinite

/-- PDF p.4: deterministic admissibility in the specified circuit class. -/
def InversionCompletion (c : CircuitClass) (d k : ℕ) (C : (Matrix (InversionBasis d (k+1)) (InversionBasis d (k+1)) ℂ)) : Prop :=
  match c with
  | .parallel => Parallel C
  | .adaptive => InversionComb d (k+1) C
  | .indefinite => GeneralProcess C

/-- PDF p.4, Eq.(4): a heralded positive branch dominated by a deterministic completion.
The complementary branch C-S is positive; no success or invertibility is assumed. -/
def HeraldedInversionBranch (c : CircuitClass) (d k : ℕ) (S : (Matrix (InversionBasis d (k+1)) (InversionBasis d (k+1)) ℂ)) : Prop :=
  S.PosSemidef ∧ ∃ C, InversionCompletion c d k C ∧ (C-S).PosSemidef

/-- PDF pp.1–4: a fixed branch inverts every SU(d) oracle with the same input-independent p.
Choi equality includes arbitrary reference-entangled inputs. Only forward U is inserted. -/
def UniversalInverseBranch {d k : ℕ} (S : (Matrix (InversionBasis d (k+1)) (InversionBasis d (k+1)) ℂ)) (p : ℝ) : Prop :=
  ∀ U : (Matrix.specialUnitaryGroup (Fin d) ℂ),
    inversionLink S (slotTensor d k (fun _ => unitaryChoi U.val)) = (p : ℂ) • inverseChoi U

/-- PDF p.4: the attainable success probabilities. The protocol is chosen before U.
The budget counts k open forward-call slots; unused calls can be discarded. -/
def Attainable (c : CircuitClass) (d k : ℕ) (p : ℝ) : Prop :=
  0 ≤ p ∧ p ≤ 1 ∧ ∃ S : (Matrix (InversionBasis d (k+1)) (InversionBasis d (k+1)) ℂ), HeraldedInversionBranch c d k S ∧ UniversalInverseBranch S p

/-- PDF p.4, Eq.(4): success constraints at an explicitly specified finite family. -/
def FiniteFeasible (c : CircuitClass) (d k m : ℕ) (U : Fin m → (Matrix.specialUnitaryGroup (Fin d) ℂ)) (p : ℝ) : Prop :=
  0 ≤ p ∧ p ≤ 1 ∧ ∃ S : (Matrix (InversionBasis d (k+1)) (InversionBasis d (k+1)) ℂ), HeraldedInversionBranch c d k S ∧
    ∀ j, inversionLink S (slotTensor d k (fun _ => unitaryChoi (U j).val)) =
      (p : ℂ) • inverseChoi (U j)

/-- PDF p.3, Theorem 1: number of complete attempts, with d-1 calls in the last attempt. -/
def adaptiveInversionProbability (d k : ℕ) : ℝ :=
  1 - (1 - 1 / (d : ℝ)^2)^((k+1)/d)

/-! Sanity examples pin the scalar prefix, tensor convention, inversionLink, and query accounting. -/

example (d : ℕ) : InversionComb d 0 (1 : (Matrix (InversionBasis d 0) (InversionBasis d 0) ℂ)) := rfl

example (d : ℕ) : slotTensor d 0 (fun j => Fin.elim0 j) = 1 := rfl

example {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (a b : (Fin d × Fin d)) :
    unitaryChoi A a b = A a.1 a.2 * conj (A b.1 b.2) := rfl

example {d : ℕ} (C : (Matrix (InversionBasis d 1) (InversionBasis d 1) ℂ)) (a b : (Fin d × Fin d)) :
    inversionLink C (1 : (Matrix (InversionBasis d 0) (InversionBasis d 0) ℂ)) a b = C (a.1,a.2,()) (b.1,b.2,()) := by
  letI : Unique (InversionBasis d 0) := inferInstanceAs (Unique Unit)
  simp only [inversionLink, Fintype.sum_unique]
  simp [endpoints, Matrix.one_apply]

example : adaptiveInversionProbability 2 0 = 0 ∧ adaptiveInversionProbability 2 1 = 1/4 ∧
    adaptiveInversionProbability 2 2 = 1/4 ∧ adaptiveInversionProbability 2 3 = 7/16 := by
  norm_num [adaptiveInversionProbability]

example {d : ℕ} (U : (Matrix.specialUnitaryGroup (Fin d) ℂ)) (a b : (Fin d × Fin d)) :
    inverseChoi U a b = conj (U.val a.2 a.1) * U.val b.2 b.1 := by
  simp [inverseChoi, unitaryChoi, Matrix.conjTranspose_apply]

end QAlgorithms.Papers.Independent.Extend50.P26


