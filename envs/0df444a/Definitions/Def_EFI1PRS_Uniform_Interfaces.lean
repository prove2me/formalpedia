-- Prove2me | Definitions.Def_EFI1PRS_Uniform_Interfaces
-- name    : EFI1PRS_Uniform_Interfaces
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:58:59.645505+00:00
-- url     : https://prove2.me/theorems/448f672b-d4c6-465f-8386-009ea6496a1d
-- title:
--   Indexed preparations, conditional register permutations and sampler observables
-- statement:
--   Indexed efficient preparation uses one polynomial-time Turing machine on the length-delimited unary pair $(\lambda,j)$ to return a complete zero-input preparation for the specified state. It is uniform in both arguments and makes no promise that an arbitrary index sequence is computable. The security theorems therefore quantify separately over every admissible index sequence.
--
--   The final window qubit is explicitly permuted before its past for conditional entropy, and tensor samples retain their full quantum registers. Sampler probabilities are computed from the concrete seed circuit's label in the projective Clifford quotient. The invalid-matrix label has an explicit identity default; the sampling theorem must prove its circuits are exact Cliffords, so valid applications never use that default.
-- source:
--   Rishabh Batra, STOC 2027 submission #273 (October 2026), EFI ⇔ 1PRS, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/273.pdf, Definitions 2.1–2.3, Lemmas 2.17, 3.1 and 4.1, pp.7,10–12

import Definitions.Def_EFI1PRS_Uniform_Hybrids

/-! Explicit operational interfaces for the source's indexed preparation and
one-bit conditional entropy clauses. These contain no claimed estimates. -/
noncomputable section
namespace EFI1PRS.Uniform
open QAlgorithms
open scoped BigOperators Matrix ComplexConjugate
attribute [local instance] Classical.propDecidable Classical.decEq

def IndexedEfficient (bound : ℕ → ℕ) (w : ℕ → ℕ → ℕ)
    (ρ : (sec j : ℕ) → Matrix (Qubits (w sec j)) (Qubits (w sec j)) ℂ) : Prop :=
  ∃ programs : (sec j : ℕ) → Preparation 0 (w sec j),
  ∃ machine : List Bool → List Bool, QAlgorithms.Complexity.PolyTimeComputable machine ∧
    ∀ sec j, 1 ≤ sec → 1 ≤ j → j ≤ bound sec →
      machine (QAlgorithms.Complexity.encNat sec ++ QAlgorithms.Complexity.encNat j) =
        (programs sec j).description ∧
      (programs sec j).onKey (fun _ => false) = ρ sec j

def lastQubitPast (q i : ℕ)
    (ζ : Matrix (Qubits (q+i)) (Qubits (q+i)) ℂ) :
    Matrix (Qubits 1 × Qubits (q+(i-1))) (Qubits 1 × Qubits (q+(i-1))) ℂ :=
  fun x y => ζ
    (fun j => if j.val < q+(i-1) then bitAt x.2 j.val else x.1 0)
    (fun j => if j.val < q+(i-1) then bitAt y.2 j.val else y.1 0)

def tensorSamples {w : ℕ} (ρ : Matrix (Qubits w) (Qubits w) ℂ) (count : ℕ) :
    Matrix (Qubits (w*count)) (Qubits (w*count)) ℂ :=
  fun x y => ∏ r : Fin count,
    ρ (fun j => bitAt x (r.val*w+j.val)) (fun j => bitAt y (r.val*w+j.val))

/-- Invalid matrices map to the identity label. Lemma 2.17 must prove that its
actual circuit matrices always take the valid branch, so this default is never used. -/
def projectiveLabel (m : ℕ) (U : Matrix (Qubits m) (Qubits m) ℂ) :
    QAlgorithms.Clifford.ProjectiveGroup m :=
  if h : U ∈ Matrix.unitaryGroup (Qubits m) ℂ then
    if hn : (⟨U,h⟩ : Matrix.unitaryGroup (Qubits m) ℂ) ∈ QAlgorithms.Clifford.normalizer m then
      Quotient.mk _ ⟨⟨U,h⟩,hn⟩
    else Quotient.mk _ 1
  else Quotient.mk _ 1

def IsExactClifford (m : ℕ) (U : Matrix (Qubits m) (Qubits m) ℂ) : Prop :=
  ∃ h : U ∈ Matrix.unitaryGroup (Qubits m) ℂ,
    (⟨U,h⟩ : Matrix.unitaryGroup (Qubits m) ℂ) ∈ QAlgorithms.Clifford.normalizer m

def samplerProbability (m sec : ℕ) (U : QAlgorithms.Clifford.ProjectiveGroup m) : ℝ :=
  ((2 : ℝ)^(seedLength m sec))⁻¹ *
    ∑ s : Qubits (seedLength m sec),
      if projectiveLabel m (sampledCircuit m sec s).unitary = U then 1 else 0

def samplerCode (m sec : ℕ) (s : Qubits (seedLength m sec)) : List Bool :=
  (cliffordIndex m (bitsInteger s % cliffordCount m)).flatMap fun g => encodeNaturals g.description

end EFI1PRS.Uniform


