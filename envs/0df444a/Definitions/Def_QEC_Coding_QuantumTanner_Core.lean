-- Prove2me | Definitions.Def_QEC_Coding_QuantumTanner_Core
-- name    : QEC_Coding_QuantumTanner_Core
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T11:06:17.990531+00:00
-- url     : https://prove2.me/theorems/fabd8bde-53d0-433e-9a58-379c7e57cbb9
-- title:
--   Core
-- statement:
--   Definitions and structural lemmas for Core, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Core.lean

import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Mathlib.LinearAlgebra.Matrix.ToLin
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inr
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_eq_checkSupport
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inr
import Theorems.Thm_QEC_QLDPC_mem_chainComplexCSSRowChecks
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inr
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_eq_checkSupport
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inr
attribute [local simp] QEC.QLDPC.mem_chainComplexCSSRowChecks
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
noncomputable section
namespace QEC.Coding.QuantumTanner
open Classical
universe u v
def columnRestriction {F : Type u} {A B : Type v} [Field F] [Fintype A] [Fintype B]
    (b : B) : Word F (A × B) →ₗ[F] Word F A where
  toFun x a := x (a, b)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def rowRestriction {F : Type u} {A B : Type v} [Field F] [Fintype A] [Fintype B]
    (a : A) : Word F (A × B) →ₗ[F] Word F B where
  toFun x b := x (a, b)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def columnCode {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]
    (C : LinearCode F A) : LinearCode F (A × B) where
  carrier := {
    carrier := {x | ∀ b, columnRestriction b x ∈ C.carrier}
    zero_mem' := fun _ => C.carrier.zero_mem
    add_mem' := fun hx hy b => C.carrier.add_mem (hx b) (hy b)
    smul_mem' := fun c _ hx b => C.carrier.smul_mem c (hx b) }
def rowCode {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]
    (C : LinearCode F B) : LinearCode F (A × B) where
  carrier := {
    carrier := {x | ∀ a, rowRestriction a x ∈ C.carrier}
    zero_mem' := fun _ => C.carrier.zero_mem
    add_mem' := fun hx hy a => C.carrier.add_mem (hx a) (hy a)
    smul_mem' := fun c _ hx a => C.carrier.smul_mem c (hx a) }
def tensorCode {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]
    (CA : LinearCode F A) (CB : LinearCode F B) : LinearCode F (A × B) where
  carrier := (columnCode (B := B) CA).carrier ⊓ (rowCode (A := A) CB).carrier
def dualTensorCode {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]
    (CA : LinearCode F A) (CB : LinearCode F B) : LinearCode F (A × B) where
  carrier := (columnCode (B := B) CA).carrier ⊔ (rowCode (A := A) CB).carrier
@[simp]
theorem mem_tensorCode {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A]
    [Fintype B] (CA : LinearCode F A) (CB : LinearCode F B) (x : Word F (A × B)) :
    x ∈ (tensorCode CA CB).carrier ↔
      (∀ b, columnRestriction b x ∈ CA.carrier) ∧
      ∀ a, rowRestriction a x ∈ CB.carrier := by
  rfl
abbrev KeptCoordinate {ι : Type v} [Fintype ι] (removed : Finset ι) :=
  {i : ι // i ∉ removed}
def punctureMap {F : Type u} {ι : Type v} [Field F] [Fintype ι] (removed : Finset ι) :
    Word F ι →ₗ[F] Word F (KeptCoordinate removed) where
  toFun x i := x i.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def puncturedCode {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]
    (C : LinearCode F ι) (removed : Finset ι) :
    LinearCode F (KeptCoordinate removed) where
  carrier := C.carrier.map (punctureMap removed)
@[simp]
theorem mem_puncturedCode {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]
    (C : LinearCode F ι) (removed : Finset ι)
    (x : Word F (KeptCoordinate removed)) :
    x ∈ (puncturedCode C removed).carrier ↔
      ∃ y, y ∈ C.carrier ∧ punctureMap removed y = x := by
  exact Submodule.mem_map
def SupportCovered {A B : Type v} [Fintype A] [Fintype B]
    (x : Word (ZMod 2) (A × B)) (rows : Finset A) (columns : Finset B) : Prop :=
  hammingSupport x ⊆
    (rows.product (Finset.univ : Finset B)) ∪
      ((Finset.univ : Finset A).product columns)
def IsRobust {A B : Type v} [Fintype A] [Fintype B]
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B) (w : Nat) : Prop :=
  ∀ dA dB, MinimumDistance CA dA → MinimumDistance CB dB →
    ∀ x, x ∈ (dualTensorCode CA CB).carrier → HammingWeight x ≤ w →
      ∃ rows : Finset A, ∃ columns : Finset B,
        SupportCovered x rows columns ∧
          rows.card ≤ HammingWeight x / dB ∧
          columns.card ≤ HammingWeight x / dA
def IsRobustWithPunctureResistance {A B : Type v} [Fintype A] [Fintype B]
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (w p : Nat) : Prop :=
  ∀ removedA : Finset A, ∀ removedB : Finset B,
    removedA.card = removedB.card → removedA.card ≤ p →
      IsRobust (puncturedCode CA removedA) (puncturedCode CB removedB) w
abbrev RandomLocalCodeSample (r : Nat) (A B : Type v) :=
  Matrix (ULift.{v} (Fin r)) A (ZMod 2) × Matrix (ULift.{v} (Fin r)) B (ZMod 2)
def RandomLocalCodeSample.codeA {r : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (sample : RandomLocalCodeSample r A B) : LinearCode (ZMod 2) A :=
  parityCheckRowCode (Matrix.toLin' sample.1)
def RandomLocalCodeSample.codeB {r : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (sample : RandomLocalCodeSample r A B) : LinearCode (ZMod 2) B :=
  parityCheckKernelCode (Matrix.toLin' sample.2)
def LocalCodeEvent {r : Nat} {A B : Type v} [Fintype A] [Fintype B]
    (dimensionA dimensionB dA dB w p : Nat)
    (sample : RandomLocalCodeSample r A B) : Prop :=
  Dimension sample.codeA = dimensionA ∧
    Dimension sample.codeB = dimensionB ∧
    MinimumDistance sample.codeA dA ∧
    MinimumDistance sample.codeB dB ∧
    IsRobustWithPunctureResistance sample.codeA sample.codeB w p
def eventFinset {Ω : Type u} [Fintype Ω] (event : Ω → Prop) [DecidablePred event] :
    Finset Ω :=
  Finset.univ.filter event
@[simp]
theorem mem_eventFinset {Ω : Type u} [Fintype Ω] (event : Ω → Prop)
    [DecidablePred event] (sample : Ω) :
    sample ∈ eventFinset event ↔ event sample := by
  simp [eventFinset]
structure LeftRightCayleySquareComplex
    (G A B Square : Type v) [Group G] [Fintype G] [Fintype A] [Fintype B]
    [Fintype Square] where
  leftGenerator : A → G
  rightGenerator : B → G
  leftInverse : Equiv.Perm A
  rightInverse : Equiv.Perm B
  leftGenerator_inverse : ∀ a, leftGenerator (leftInverse a) = (leftGenerator a)⁻¹
  rightGenerator_inverse : ∀ b, rightGenerator (rightInverse b) = (rightGenerator b)⁻¹
  noConjugacy : ∀ g a b, leftGenerator a * g ≠ g * rightGenerator b
  link : G × Bool → A × B → Square
  link_injective : ∀ vertex, Function.Injective (link vertex)
  square_side_degree : ∀ square side,
    (Finset.univ.filter fun g => ∃ ab, link (g, side) ab = square).card = 2
namespace LeftRightCayleySquareComplex
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]
def Incident (X : LeftRightCayleySquareComplex G A B Square)
    (vertex : G × Bool) (square : Square) : Prop :=
  ∃ ab, X.link vertex ab = square
def localExtension (X : LeftRightCayleySquareComplex G A B Square)
    (vertex : G × Bool) :
    Word (ZMod 2) (A × B) →ₗ[ZMod 2] Word (ZMod 2) Square where
  toFun x := ∑ ab : A × B, x ab • Pi.single (X.link vertex ab) 1
  map_add' x y := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, Finset.smul_sum, smul_smul, RingHom.id_apply, smul_eq_mul]
end LeftRightCayleySquareComplex
def linearMapOfGenerators {F : Type u} {ι κ : Type v} [Field F] [Fintype ι] [Fintype κ]
    (generator : κ → Word F ι) : Word F κ →ₗ[F] Word F ι where
  toFun coefficient := ∑ k : κ, coefficient k • generator k
  map_add' x y := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, Finset.smul_sum, smul_smul, RingHom.id_apply, smul_eq_mul]
structure RawData
    (G A B Square XBasis ZBasis : Type v)
    [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
    [Fintype XBasis] [Fintype ZBasis] where
  complex : LeftRightCayleySquareComplex G A B Square
  codeA : LinearCode (ZMod 2) A
  codeB : LinearCode (ZMod 2) B
  xBasis : Module.Basis XBasis (ZMod 2) (tensorCode codeA.dual codeB.dual).carrier
  zBasis : Module.Basis ZBasis (ZMod 2) (tensorCode codeA codeB).carrier
namespace RawData
variable {G A B Square XBasis ZBasis : Type v}
  [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
  [Fintype XBasis] [Fintype ZBasis]
def xGenerator (D : RawData G A B Square XBasis ZBasis) (check : G × XBasis) :
    Word (ZMod 2) Square :=
  D.complex.localExtension (check.1, true) (D.xBasis check.2).1
def zGenerator (D : RawData G A B Square XBasis ZBasis) (check : G × ZBasis) :
    Word (ZMod 2) Square :=
  D.complex.localExtension (check.1, false) (D.zBasis check.2).1
def xGeneratorMap (D : RawData G A B Square XBasis ZBasis) :
    Word (ZMod 2) (G × XBasis) →ₗ[ZMod 2] Word (ZMod 2) Square :=
  linearMapOfGenerators D.xGenerator
def zGeneratorMap (D : RawData G A B Square XBasis ZBasis) :
    Word (ZMod 2) (G × ZBasis) →ₗ[ZMod 2] Word (ZMod 2) Square :=
  linearMapOfGenerators D.zGenerator
def boundary1 (D : RawData G A B Square XBasis ZBasis) :
    Word (ZMod 2) Square →ₗ[ZMod 2] Word (ZMod 2) (G × XBasis) :=
  wordLinearMapTranspose D.xGeneratorMap
def boundary2 (D : RawData G A B Square XBasis ZBasis) :
    Word (ZMod 2) (G × ZBasis) →ₗ[ZMod 2] Word (ZMod 2) Square :=
  D.zGeneratorMap
end RawData
structure Data
    (G A B Square XBasis ZBasis : Type v)
    [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
    [Fintype XBasis] [Fintype ZBasis] extends
    RawData G A B Square XBasis ZBasis where
  boundary_squared : toRawData.boundary1.comp toRawData.boundary2 = 0
namespace Data
variable {G A B Square XBasis ZBasis : Type v}
  [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
  [Fintype XBasis] [Fintype ZBasis]
def chainComplex (D : Data G A B Square XBasis ZBasis) :
    ChainComplexData (ZMod 2)
      (Word (ZMod 2) (G × XBasis))
      (Word (ZMod 2) Square)
      (Word (ZMod 2) (G × ZBasis)) where
  boundary1 := D.toRawData.boundary1
  boundary2 := D.toRawData.boundary2
  boundary_squared := D.boundary_squared
def cssCode (D : Data G A B Square XBasis ZBasis) :=
  D.chainComplex.binaryCSSCode
def blockLength (_D : Data G A B Square XBasis ZBasis) : Nat :=
  Fintype.card Square
def encodedDimension (D : Data G A B Square XBasis ZBasis) : Nat :=
  Module.finrank (ZMod 2) D.chainComplex.middleHomology
def HasParameters (D : Data G A B Square XBasis ZBasis) (n k d : Nat) : Prop :=
  n = D.blockLength ∧
    k = D.encodedDimension ∧
    AlgebraicCSSMinimumDistance
      D.chainComplex.firstCoboundaryCheckCode
      D.chainComplex.middleBoundaryCode d
end Data
end QEC.Coding.QuantumTanner


