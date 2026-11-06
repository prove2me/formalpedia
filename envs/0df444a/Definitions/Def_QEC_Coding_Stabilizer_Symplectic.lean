-- Prove2me | Definitions.Def_QEC_Coding_Stabilizer_Symplectic
-- name    : QEC_Coding_Stabilizer_Symplectic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T09:28:54.841237+00:00
-- url     : https://prove2.me/theorems/3734dc81-fa82-433b-9a42-40c9a743a746
-- title:
--   Symplectic
-- statement:
--   Definitions and structural lemmas for Symplectic, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Symplectic.lean

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


set_option autoImplicit false
noncomputable section
namespace QEC
namespace Coding
universe u v
namespace SymplecticVector
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]
def toProdEquiv : SymplecticVector F ι ≃ Word F ι × Word F ι where
  toFun v := (v.xPart, v.zPart)
  invFun p := { xPart := p.1, zPart := p.2 }
  left_inv v := by cases v; rfl
  right_inv p := by cases p; rfl
instance instAddCommGroup : AddCommGroup (SymplecticVector F ι) :=
  (toProdEquiv (F := F) (ι := ι)).addCommGroup
instance instModule : Module F (SymplecticVector F ι) :=
  (toProdEquiv (F := F) (ι := ι)).module F
@[simp] theorem xPart_zero : (0 : SymplecticVector F ι).xPart = 0 := rfl
@[simp] theorem zPart_zero : (0 : SymplecticVector F ι).zPart = 0 := rfl
@[simp] theorem xPart_add (a b : SymplecticVector F ι) :
    (a + b).xPart = a.xPart + b.xPart := rfl
@[simp] theorem zPart_add (a b : SymplecticVector F ι) :
    (a + b).zPart = a.zPart + b.zPart := rfl
@[simp] theorem xPart_smul (c : F) (a : SymplecticVector F ι) :
    (c • a).xPart = c • a.xPart := rfl
@[simp] theorem zPart_smul (c : F) (a : SymplecticVector F ι) :
    (c • a).zPart = c • a.zPart := rfl
def toProdLinearEquiv :
    SymplecticVector F ι ≃ₗ[F] Word F ι × Word F ι where
  toEquiv := toProdEquiv
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
instance instFiniteDimensional : FiniteDimensional F (SymplecticVector F ι) :=
  LinearEquiv.finiteDimensional (toProdLinearEquiv (F := F) (ι := ι)).symm
end SymplecticVector
namespace FiniteSymplectic
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]
def form : LinearMap.BilinForm F (SymplecticVector F ι) where
  toFun a :=
    { toFun := fun b => symplecticForm a b
      map_add' := by
        intro b c
        change
          (∑ i, (a.xPart i * (b.zPart i + c.zPart i) -
            a.zPart i * (b.xPart i + c.xPart i))) =
          (∑ i, (a.xPart i * b.zPart i - a.zPart i * b.xPart i)) +
            ∑ i, (a.xPart i * c.zPart i - a.zPart i * c.xPart i)
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      map_smul' := by
        intro c b
        change
          (∑ i, (a.xPart i * (c * b.zPart i) - a.zPart i * (c * b.xPart i))) =
            c * ∑ i, (a.xPart i * b.zPart i - a.zPart i * b.xPart i)
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        ring }
  map_add' := by
    intro a b
    ext c
    change
      (∑ i, ((a.xPart i + b.xPart i) * c.zPart i -
        (a.zPart i + b.zPart i) * c.xPart i)) =
      (∑ i, (a.xPart i * c.zPart i - a.zPart i * c.xPart i)) +
        ∑ i, (b.xPart i * c.zPart i - b.zPart i * c.xPart i)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  map_smul' := by
    intro c a
    ext b
    change
      (∑ i, ((c * a.xPart i) * b.zPart i - (c * a.zPart i) * b.xPart i)) =
        c * ∑ i, (a.xPart i * b.zPart i - a.zPart i * b.xPart i)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
end FiniteSymplectic
end Coding
end QEC


