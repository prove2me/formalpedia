-- Prove2me | Definitions.Def_QEC_Coding_QLDPC_Core
-- name    : QEC_Coding_QLDPC_Core
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:19:02.453614+00:00
-- url     : https://prove2.me/theorems/ce3112f6-8ac3-43f6-85d1-875880eb89a8
-- title:
--   Core
-- statement:
--   Definitions and structural lemmas for Core, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/Core.lean

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
set_option autoImplicit false
namespace QEC
universe u v w x
open scoped Classical
namespace Coding.ChainComplexData
noncomputable def binaryChainComplexCode
    {ι κ lambda : Type u} [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype lambda]
    (K : ChainComplexData
      (ZMod 2) (Word (ZMod 2) κ) (Word (ZMod 2) ι)
      (Word (ZMod 2) lambda)) :
    ChainComplexCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι)
      (Word (ZMod 2) κ) (Word (ZMod 2) ι)
      (Word (ZMod 2) lambda) where
  complex := K
  css := K.binaryCSSCode
  cycles := K.middleCycleCode
  boundaries := K.middleBoundaryCode
  boundary_subset_cycles := K.middleBoundaryCode_le_middleCycleCode
end Coding.ChainComplexData
namespace Coding.StabilizerCode
open PauliSymplectic
noncomputable def generatedGroup
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι)) :
    Set (Binary ι) := by
  classical
  letI : Fintype {P : Binary ι // P ∈ Q.stabilizers} := Fintype.ofFinite _
  exact {P |
    GeneratedStabilizer
      (fun check : {P : Binary ι // P ∈ Q.stabilizers} => check.1) P}
def IsSourceValidBinary
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι)) : Prop :=
  binarySign (ι := ι) 1 ∉ Q.generatedGroup ∧
    ∀ ψ, ψ ∈ Q.code.carrier ↔
      ∀ P, P ∈ Q.generatedGroup → toQubitOperator P ψ = ψ
abbrev SourceValidBinary
    (ι : Type u) [Fintype ι] [DecidableEq ι] :=
  {Q : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι) //
    Q.IsSourceValidBinary}
end Coding.StabilizerCode
namespace QLDPC
def FinsetGenerates
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : Finset (Coding.PauliSymplectic.Binary ι))
    (S : Set (Coding.PauliSymplectic.Binary ι)) : Prop :=
  Coding.PauliSymplectic.generatedStabilizerSet (fun g : {P // P ∈ G} => g.1) = S
def qubitCheckDegree
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : Finset (Coding.PauliSymplectic.Binary ι)) (q : ι) : Nat :=
  (G.filter fun g => q ∈ Coding.PauliSymplectic.support g).card
def IsLDPCStabilizerFamily
    {A : Type u} {ι : A → Type v}
    [∀ a, Fintype (ι a)] [∀ a, DecidableEq (ι a)]
    (Q : ∀ a, Coding.StabilizerCode.SourceValidBinary (ι a)) : Prop :=
  ∃ w : Nat, ∀ a, ∃ G : Finset (Coding.PauliSymplectic.Binary (ι a)),
    FinsetGenerates G (Q a).1.generatedGroup ∧
      (∀ g ∈ G, Coding.PauliSymplectic.weight g ≤ w) ∧
      ∀ q, qubitCheckDegree G q ≤ w
structure CheckIncidence (χ ι : Type*) [Fintype χ] [Fintype ι] where
  incident : χ → ι → Prop
namespace CheckIncidence
variable {χ ι : Type*} [Fintype χ] [Fintype ι]
noncomputable def checkSupport (I : CheckIncidence χ ι) (c : χ) : Finset ι := by
  classical
  exact Finset.univ.filter fun q => I.incident c q
noncomputable def variableSupport (I : CheckIncidence χ ι) (q : ι) : Finset χ := by
  classical
  exact Finset.univ.filter fun c => I.incident c q
noncomputable def localityProfile (I : CheckIncidence χ ι) : Coding.LocalityProfile :=
  { maxCheckWeight := Finset.univ.sup fun c => (I.checkSupport c).card
    maxVariableDegree := Finset.univ.sup fun q => (I.variableSupport q).card }
theorem boundedLocality_of_row_col_bounds
    (I : CheckIncidence χ ι) {B : Nat}
    (hrow : ∀ c, (I.checkSupport c).card ≤ B)
    (hcol : ∀ q, (I.variableSupport q).card ≤ B) :
    Coding.BoundedLocality I.localityProfile B := by
  constructor
  · change (Finset.univ.sup fun c => (I.checkSupport c).card) ≤ B
    exact Finset.sup_le fun c _hc => hrow c
  · change (Finset.univ.sup fun q => (I.variableSupport q).card) ≤ B
    exact Finset.sup_le fun q _hq => hcol q
end CheckIncidence
noncomputable def QLDPCProperty.ofCheckIncidenceBounds
    {F : Type u} {ι : Type v} {H : Type w} {C0 C1 C2 : Type x}
    [Field F] [Fintype F] [DecidableEq F] [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [AddCommGroup C0] [Module F C0] [AddCommGroup C1] [Module F C1]
    [AddCommGroup C2] [Module F C2]
    {χ : Type*} [Fintype χ]
    (chainCode : Coding.ChainComplexCode F ι H C0 C1 C2)
    (parameters : Coding.CodeParameters F ι)
    (I : CheckIncidence χ ι) {B : Nat}
    (hrow : ∀ c, (I.checkSupport c).card ≤ B)
    (hcol : ∀ q, (I.variableSupport q).card ≤ B) :
    Coding.QLDPCProperty F ι H C0 C1 C2 :=
  { chainCode := chainCode
    parameters := parameters
    locality := I.localityProfile
    localityBound := B
    bounded_locality := I.boundedLocality_of_row_col_bounds hrow hcol }
noncomputable def chainComplexBoundaryIncidence
    {F : Type u} {ι κ lambda : Type v} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Fintype κ] [Fintype lambda]
    (K : Coding.ChainComplexData F (Coding.Word F κ) (Coding.Word F ι)
      (Coding.Word F lambda)) :
    CheckIncidence (Sum κ lambda) ι where
  incident c q :=
    match c with
    | Sum.inl k => (Coding.wordLinearMapTranspose K.boundary1
        (Coding.canonicalBasisWord (F := F) k)) q ≠ 0
    | Sum.inr l => (K.boundary2
        (Coding.canonicalBasisWord (F := F) l)) q ≠ 0
noncomputable def chainComplexCSSRowCheck
    {ι κ lambda : Type v} [Fintype ι] [Fintype κ] [Fintype lambda]
    (K : Coding.ChainComplexData
      (ZMod 2) (Coding.Word (ZMod 2) κ) (Coding.Word (ZMod 2) ι)
      (Coding.Word (ZMod 2) lambda)) :
    Sum κ lambda → Coding.PauliSymplectic.Binary ι
  | Sum.inl k => Coding.PauliSymplectic.cssXCheck
      (Coding.wordLinearMapTranspose K.boundary1
        (Coding.canonicalBasisWord (F := ZMod 2) k))
  | Sum.inr l => Coding.PauliSymplectic.cssZCheck
      (K.boundary2 (Coding.canonicalBasisWord (F := ZMod 2) l))
noncomputable def chainComplexCSSRowChecks
    {ι κ lambda : Type v} [Fintype ι] [Fintype κ] [Fintype lambda]
    (K : Coding.ChainComplexData
      (ZMod 2) (Coding.Word (ZMod 2) κ) (Coding.Word (ZMod 2) ι)
      (Coding.Word (ZMod 2) lambda)) :
    Finset (Coding.PauliSymplectic.Binary ι) := by
  classical
  exact Finset.univ.image (chainComplexCSSRowCheck K)
end QLDPC
end QEC


