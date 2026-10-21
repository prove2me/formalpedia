-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P25
-- name    : QAlgorithms_Papers_Independent_Claimed50_P25
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T10:14:09.753441+00:00
-- url     : https://prove2.me/theorems/1e6510e2-d43e-42a9-946e-fb8838cc0044
-- title:
--   Definitions for Optimal quantum learning of a unitary transformation
-- statement:
--   The objects the formalized statements of *Optimal quantum learning of a unitary transformation* (arXiv:0903.0543) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `learningSignature`: PDF p.3, Eq.(6), Fig.1: tooth j has input H_(2j), output H_(2j+1). The scalar output at tooth N precedes the late input at tooth N+1.
--   - `LearningBasis`: PDF p.3: newest tooth first, retaining the scalar dummy wires.
--   - `outputIndex`: PDF pp.2-3: read an output coordinate. Outside the prefix return zero; all physical uses below are inside the prefix.
--   - `inputIndex`: PDF pp.2-3: read an input coordinate, with the same padding convention.
--   - `entryAt`: PDF p.2: total extension of a fixed-basis matrix entry; zero outside its bounds. The wire dimensions ensure all physical calls are within bounds.
--   - `outputFirstVector`: PDF p.2, Eq.(1): unnormalized output-first vectorization.
--   - `learningProbe`: PDF p.3, Eq.(8): |U>> on the target, |U*>> on exactly N examples, in the recursive comb basis. This unnormalized Choi test vector is not a state.
--   - `combFidelity`: PDF p.3, Eq.(8): Haar-averaged channel fidelity divided by d^2. Continuity and compactness in the theorems guarantee an integrable integrand.
--   - `wireAction`: PDF p.3, Eq.(9): tensor the specified actions on every labelled wire.
--   - `learningOutOp`: PDF p.3, Eq.(9): U on target output, V on example inputs, scalar identities.
--   - `learningInOp`: PDF p.3, Eq.(9): entrywise conjugate V on target input, conjugate U on example outputs. Neither star here is a transpose or adjoint.
--   - `learningAction`: PDF p.3, Eqs.(9)-(10): n=N+2 gives the whole action and n=N+1 its storage restriction. Regrouping yields U tensor V* tensor U_out*^N tensor V_in^N.
--   - `parallelOrbit`: PDF pp.3-4, Lemma 1: (U^N tensor I)phi; phi is fixed before the unknown parameter. Its auxiliary factor is an entire N-register copy.
--   - `parallelChannel`: PDF p.4, Eq.(11): fixed retrieval on the late input and stored memory, defined on all input matrices (including off-diagonal matrix units).
--   - `channelChoi`: PDF p.2, Eq.(3): unnormalized output-first Choi entries. In physical uses IsChannel supplies complete positivity, trace preservation and linearity.
--   - `parallelFidelity`: PDF pp.3-4, Eqs.(8),(11): actual fidelity of parallel preparation/retrieval.
-- source:
--   Optimal quantum learning of a unitary transformation, arXiv:0903.0543v2, https://arxiv.org/abs/0903.0543v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_ContinuousPOVMDensities
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26

/-!
Bisio et al., arXiv:0903.0543v2. The remaining planned nodes are explicitly
 deferred in HARD.md and GAPS.json. Compilation awaits the mechanical handoff.
-/

noncomputable section

open MeasureTheory QAlgorithms
open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Claimed50.P25

open QAlgorithms.Papers.Independent.Dependency50.P26 (Signature Basis Normalized)
open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

attribute [local instance] Classical.decEq Classical.propDecidable

/-- PDF p.3, Eq.(6), Fig.1: tooth j has input H_(2j), output H_(2j+1).
The scalar output at tooth N precedes the late input at tooth N+1. -/
def learningSignature (N d : ℕ) [NeZero d] : Signature where
  input j := if j = 0 then 1 else if j ≤ N + 1 then d else 1
  output j := if j < N ∨ j = N + 1 then d else 1
  input_pos j := by
    split_ifs <;> first | exact Nat.pos_of_ne_zero (NeZero.ne d) | decide
  output_pos j := by
    split_ifs <;> first | exact Nat.pos_of_ne_zero (NeZero.ne d) | decide

/-- PDF p.3: newest tooth first, retaining the scalar dummy wires. -/
abbrev LearningBasis (N d : ℕ) [NeZero d] := Basis (learningSignature N d) (N + 2)

/-- PDF pp.2-3: read an output coordinate. Outside the prefix return zero;
all physical uses below are inside the prefix. -/
def outputIndex (s : Signature) : (n : ℕ) → Basis s n → ℕ → ℕ
  | 0, _, _ => 0
  | n + 1, x, j => if j = n then x.1.val else outputIndex s n x.2.2 j

/-- PDF pp.2-3: read an input coordinate, with the same padding convention. -/
def inputIndex (s : Signature) : (n : ℕ) → Basis s n → ℕ → ℕ
  | 0, _, _ => 0
  | n + 1, x, j => if j = n then x.2.1.val else inputIndex s n x.2.2 j

/-- PDF p.2: total extension of a fixed-basis matrix entry; zero outside its
bounds. The wire dimensions ensure all physical calls are within bounds. -/
def entryAt {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (a b : ℕ) : ℂ :=
  if ha : a < d then if hb : b < d then A ⟨a, ha⟩ ⟨b, hb⟩ else 0 else 0

/-- PDF p.2, Eq.(1): unnormalized output-first vectorization. -/
def outputFirstVector {I O : Type*} (A : Matrix O I ℂ) : EuclideanSpace ℂ (O × I) :=
  WithLp.toLp 2 (fun x => A x.1 x.2)

/-- PDF p.3, Eq.(8): |U>> on the target, |U*>> on exactly N examples,
in the recursive comb basis. This unnormalized Choi test vector is not a state. -/
def learningProbe (N d : ℕ) [NeZero d] (A : Matrix (Fin d) (Fin d) ℂ)
    (x : LearningBasis N d) : ℂ :=
  let s := learningSignature N d
  entryAt A (outputIndex s (N + 2) x (N + 1)) (inputIndex s (N + 2) x (N + 1)) *
    ∏ j : Fin N, conj (entryAt A (inputIndex s (N + 2) x (j.val + 1))
      (outputIndex s (N + 2) x j.val))

/-- PDF p.3, Eq.(8): Haar-averaged channel fidelity divided by d^2.
Continuity and compactness in the theorems guarantee an integrable integrand. -/
def combFidelity {G : Type*} [MeasurableSpace G] (mu : Measure G)
    (N d : ℕ) [NeZero d] (U : G → Matrix (Fin d) (Fin d) ℂ)
    (L : Matrix (LearningBasis N d) (LearningBasis N d) ℂ) : ℝ :=
  (∫ g, (Measurements.quadraticFunctional (learningProbe N d (U g)) L).re ∂mu) / (d : ℝ) ^ 2

/-- PDF p.3, Eq.(9): tensor the specified actions on every labelled wire. -/
def wireAction (s : Signature) (outOp inOp : ℕ → ℕ → ℕ → ℂ) :
    (n : ℕ) → Matrix (Basis s n) (Basis s n) ℂ
  | 0 => 1
  | n + 1 => fun x y => outOp n x.1.val y.1.val * inOp n x.2.1.val y.2.1.val *
      wireAction s outOp inOp n x.2.2 y.2.2

/-- PDF p.3, Eq.(9): U on target output, V on example inputs, scalar identities. -/
def learningOutOp {d : ℕ} (N : ℕ) (A B : Matrix (Fin d) (Fin d) ℂ)
    (j a b : ℕ) : ℂ :=
  if j = N + 1 then entryAt A a b
  else if j < N then entryAt B a b else if a = b then 1 else 0

/-- PDF p.3, Eq.(9): entrywise conjugate V on target input, conjugate U on
example outputs. Neither star here is a transpose or adjoint. -/
def learningInOp {d : ℕ} (N : ℕ) (A B : Matrix (Fin d) (Fin d) ℂ)
    (j a b : ℕ) : ℂ :=
  if j = N + 1 then conj (entryAt B a b)
  else if 0 < j ∧ j ≤ N then conj (entryAt A a b) else if a = b then 1 else 0

/-- PDF p.3, Eqs.(9)-(10): n=N+2 gives the whole action and n=N+1 its
storage restriction. Regrouping yields U tensor V* tensor U_out*^N tensor V_in^N. -/
def learningAction (N d : ℕ) [NeZero d] (A B : Matrix (Fin d) (Fin d) ℂ) (n : ℕ) :=
  wireAction (learningSignature N d) (learningOutOp N A B) (learningInOp N A B) n

/-- PDF pp.3-4, Lemma 1: (U^N tensor I)phi; phi is fixed before the unknown
parameter. Its auxiliary factor is an entire N-register copy. -/
def parallelOrbit (N d : ℕ) (A : Matrix (Fin d) (Fin d) ℂ)
    (phi : EuclideanSpace ℂ ((Fin N → Fin d) × (Fin N → Fin d))) :=
  act (Matrix.kronecker (tensorPower N A)
    (1 : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)) phi

/-- PDF p.4, Eq.(11): fixed retrieval on the late input and stored memory,
defined on all input matrices (including off-diagonal matrix units). -/
def parallelChannel (N d : ℕ)
    (R : Superop (Fin d × ((Fin N → Fin d) × (Fin N → Fin d))) (Fin d))
    (phi : EuclideanSpace ℂ ((Fin N → Fin d) × (Fin N → Fin d)))
    (A : Matrix (Fin d) (Fin d) ℂ) : Superop (Fin d) (Fin d) :=
  fun X => R (Matrix.kronecker X (pureDensity (parallelOrbit N d A phi)))

/-- PDF p.2, Eq.(3): unnormalized output-first Choi entries. In physical uses
IsChannel supplies complete positivity, trace preservation and linearity. -/
def channelChoi {I O : Type*} [DecidableEq I] (C : Superop I O) :
    Matrix (O × I) (O × I) ℂ :=
  fun x y => C (Matrix.single x.2 y.2 1) x.1 y.1

/-- PDF pp.3-4, Eqs.(8),(11): actual fidelity of parallel preparation/retrieval. -/
def parallelFidelity {G : Type*} [MeasurableSpace G] (mu : Measure G)
    (N d : ℕ) (U : G → Matrix (Fin d) (Fin d) ℂ)
    (phi : EuclideanSpace ℂ ((Fin N → Fin d) × (Fin N → Fin d)))
    (R : Superop (Fin d × ((Fin N → Fin d) × (Fin N → Fin d))) (Fin d)) : ℝ :=
  (∫ g, (Measurements.quadraticFunctional (fun x => U g x.1 x.2)
    (channelChoi (parallelChannel N d R phi (U g)))).re ∂mu) / (d : ℝ) ^ 2

/-! Small coordinate sanity checks; no theorem proofs are attempted. -/

example : (learningSignature 1 2).input 0 = 1 ∧
    (learningSignature 1 2).output 0 = 2 ∧
    (learningSignature 1 2).input 1 = 2 ∧
    (learningSignature 1 2).output 1 = 1 ∧
    (learningSignature 1 2).input 2 = 2 ∧
    (learningSignature 1 2).output 2 = 2 := by
  norm_num [learningSignature]

example : outputFirstVector (1 : Matrix (Fin 2) (Fin 2) ℂ) (0, 1) = 0 := by
  simp [outputFirstVector]

example : outputFirstVector (1 : Matrix (Fin 2) (Fin 2) ℂ) (1, 1) = 1 := by
  simp [outputFirstVector]

example (A : Matrix (Fin 2) (Fin 2) ℂ) : entryAt A 0 1 = A 0 1 := by
  simp [entryAt]

example (A : Matrix (Fin 2) (Fin 2) ℂ) : entryAt A 2 0 = 0 := by
  simp [entryAt]

example (s : Signature) : outputIndex s 0 () 0 = 0 ∧ inputIndex s 0 () 0 = 0 :=
  ⟨rfl, rfl⟩

example (s : Signature) (O I : ℕ → ℕ → ℕ → ℂ) : wireAction s O I 0 = 1 := rfl

example {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) (N a b : ℕ) :
    learningOutOp N A B (N + 1) a b = entryAt A a b ∧
    learningInOp N A B (N + 1) a b = conj (entryAt B a b) := by
  simp [learningOutOp, learningInOp]

example (A : Matrix (Fin 2) (Fin 2) ℂ) :
    tensorPower 0 A (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) = 1 := by
  simp [tensorPower]

example {I : Type*} [Fintype I] (v : I → ℂ) :
    (Measurements.quadraticFunctional v (0 : Matrix I I ℂ)).re = 0 := by
  simp

example (a b c e : Fin 2) :
    channelChoi (fun X : Matrix (Fin 2) (Fin 2) ℂ => X) (a,b) (c,e) =
      Matrix.single b e 1 a c := rfl

section MainStatements

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

end MainStatements

end QAlgorithms.Papers.Independent.Claimed50.P25


