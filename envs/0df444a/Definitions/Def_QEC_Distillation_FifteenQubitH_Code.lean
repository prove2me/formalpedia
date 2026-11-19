-- Prove2me | Definitions.Def_QEC_Distillation_FifteenQubitH_Code
-- name    : QEC_Distillation_FifteenQubitH_Code
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T00:51:33.460452+00:00
-- url     : https://prove2.me/theorems/216dc4f8-32ca-4216-ad40-7dd19c3dd5a9
-- title:
--   Code
-- statement:
--   Definitions and structural lemmas for Code, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean

import Definitions.Def_QEC_Coding_Core_Definitions
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


set_option autoImplicit false
namespace QEC.Distillation.BK15
open QEC Coding
abbrev Bit := ZMod 2
abbrev Word := Coding.Word Bit (Fin 15)
abbrev QuadraticIndex := { ij : Fin 4 × Fin 4 // ij.1 < ij.2 }
def pointBit (j : Fin 4) (i : Fin 15) : Bit :=
  (((i.val + 1) / 2 ^ (3 - j.val)) % 2 : Nat)
def linearGenerator (j : Fin 4) : Word := fun i => pointBit j i
def quadraticGenerator (ij : QuadraticIndex) : Word := fun i =>
  pointBit ij.1.1 i * pointBit ij.1.2 i
def l1CoefficientMap : (Fin 4 → Bit) →ₗ[Bit] Word where
  toFun a := fun i => ∑ j : Fin 4, a j * linearGenerator j i
  map_add' := by
    intro a b
    ext i
    simp [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro c a
    ext i
    simp [Pi.smul_apply, Finset.mul_sum, mul_assoc]
def l2Generator : Sum (Fin 4) QuadraticIndex → Word
  | Sum.inl j => linearGenerator j
  | Sum.inr ij => quadraticGenerator ij
def l2CoefficientMap : (Sum (Fin 4) QuadraticIndex → Bit) →ₗ[Bit] Word where
  toFun a := fun i => ∑ g : Sum (Fin 4) QuadraticIndex, a g * l2Generator g i
  map_add' := by
    intro a b
    ext i
    simp [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro c a
    ext i
    change
      (∑ g : Sum (Fin 4) QuadraticIndex,
        (c * a g) * l2Generator g i) =
        c * ∑ g : Sum (Fin 4) QuadraticIndex,
          a g * l2Generator g i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _
    ring
def L1 : LinearCode Bit (Fin 15) where
  carrier := LinearMap.range l1CoefficientMap
def L2 : LinearCode Bit (Fin 15) where
  carrier := LinearMap.range l2CoefficientMap
def allOnes : Word := fun _ => 1
def pointwiseProduct (u v : Word) : Word := fun i => u i * v i
def l1DualCoefficientMap :
    ((Sum (Fin 4) QuadraticIndex → Bit) × Bit) →ₗ[Bit] Word where
  toFun bc := l2CoefficientMap bc.1 + bc.2 • allOnes
  map_add' := by
    intro a b
    simp only [Prod.fst_add, Prod.snd_add, map_add, add_smul]
    module
  map_smul' := by
    intro c a
    ext i
    simp [Prod.smul_fst, Prod.smul_snd, map_smul,
      smul_eq_mul, mul_add, mul_assoc]
def l2DualCoefficientMap : ((Fin 4 → Bit) × Bit) →ₗ[Bit] Word where
  toFun ac := l1CoefficientMap ac.1 + ac.2 • allOnes
  map_add' := by
    intro a b
    simp only [Prod.fst_add, Prod.snd_add, map_add, add_smul]
    module
  map_smul' := by
    intro c a
    ext i
    simp [Prod.smul_fst, Prod.smul_snd, map_smul,
      smul_eq_mul, mul_add, mul_assoc]
def L1DualModel : LinearCode Bit (Fin 15) where
  carrier := LinearMap.range l1DualCoefficientMap
def L2DualModel : LinearCode Bit (Fin 15) where
  carrier := LinearMap.range l2DualCoefficientMap
def l1Syndrome : Word →ₗ[Bit] (Fin 4 → Bit) where
  toFun w := fun j => wordPairing w (linearGenerator j)
  map_add' := by
    intro u v
    ext j
    simpa [wordPairing_apply] using add_dotProduct u v (linearGenerator j)
  map_smul' := by
    intro c u
    ext j
    simpa [wordPairing_apply] using smul_dotProduct c u (linearGenerator j)
def l2Syndrome : Word →ₗ[Bit] (Sum (Fin 4) QuadraticIndex → Bit) where
  toFun w := fun g => wordPairing w (l2Generator g)
  map_add' := by
    intro u v
    ext g
    simpa [wordPairing_apply] using add_dotProduct u v (l2Generator g)
  map_smul' := by
    intro c u
    ext g
    simpa [wordPairing_apply] using smul_dotProduct c u (l2Generator g)
def l1Words : Finset Word := Finset.univ.image l1CoefficientMap
def l2Words : Finset Word := Finset.univ.image l2CoefficientMap
def l2LogicalCosetWords : Finset Word := l2Words.image fun w => w + allOnes
def l1LogicalCosetWords : Finset Word := l1Words.image fun w => w + allOnes
def l1DualWords : Finset Word := Finset.univ.image l1DualCoefficientMap
def l2DualWords : Finset Word := Finset.univ.image l2DualCoefficientMap
def weightCount (words : Finset Word) (weight : Nat) : Nat :=
  (words.filter fun w => HammingWeight w = weight).card
end QEC.Distillation.BK15


