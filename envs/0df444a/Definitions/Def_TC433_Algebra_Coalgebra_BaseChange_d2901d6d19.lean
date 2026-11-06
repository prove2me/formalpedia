-- Prove2me | Definitions.Def_TC433_Algebra_Coalgebra_BaseChange_d2901d6d19
-- name    : TC433_Algebra_Coalgebra_BaseChange_d2901d6d19
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:11:55.003573+00:00
-- url     : https://prove2.me/theorems/74e137d6-d260-45e1-b39d-12b591f2aae1
-- title:
--   TauCeti: Algebra / Coalgebra / BaseChange
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.Algebra.Coalgebra.BaseChange for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/Algebra/Coalgebra/BaseChange.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Definitions.Def_TC433_Compat4331_Tensor_6326550516

public import Mathlib.RingTheory.Coalgebra.TensorProduct
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Basic
public import Definitions.Def_TC433_Algebra_Bialgebra_TensorProduct_078f582805

/-!
# Base change of coalgebras

This file records formulas for the coalgebra structure on a scalar extension `A ⊗[R] H`.

## Main declarations

* `TauCeti.Coalgebra.baseChange_comul_tmul`: the comultiplication of a scalar extension on
  pure tensors.
* `TauCeti.Coalgebra.IsCocomm.of_baseChange`: cocommutativity descends from a field extension.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

namespace TauCeti.Coalgebra

universe u v w

variable {R : Type u} (A : Type v) {H : Type w}
variable [CommSemiring R] [CommSemiring A] [Algebra R A]
variable [AddCommMonoid H] [Module R H] [CoalgebraStruct R H]

/-- The comultiplication of a base-changed coalgebra on a pure tensor. -/
theorem baseChange_comul_tmul (a : A) (h : H) :
    Coalgebra.comul (R := A) (A := A ⊗[R] H) (a ⊗ₜ[R] h) =
      TensorProduct.AlgebraTensorModule.distribBaseChange R A H H
        (a ⊗ₜ[R] Coalgebra.comul (R := R) (A := H) h) := by
  rw [TensorProduct.comul_tmul, CommSemiring.comul_apply]
  induction Coalgebra.comul (R := R) (A := H) h using TensorProduct.inductionOn with
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | tmul g k =>
      simp only [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
        TensorProduct.AlgebraTensorModule.distribBaseChange_tmul]
      rw [TensorProduct.tmul_eq_smul_one_tmul a g,
        TensorProduct.tmul_eq_smul_one_tmul a k, TensorProduct.tmul_smul]
      exact TensorProduct.smul_tmul' a (1 ⊗ₜ[R] g) (1 ⊗ₜ[R] k)

end TauCeti.Coalgebra

namespace TauCeti.Coalgebra.IsCocomm

universe u v w

variable {k : Type u} {K : Type v} {H : Type w} [Field k] [Field K] [Algebra k K]
  [CommRing H] [_root_.Bialgebra k H]

/-- The tensor bialgebra base-change equivalence agrees with distributivity over base change on
elements coming from the original tensor square. -/
private theorem baseChangeTensorBialgEquiv_includeRight (y : H ⊗[k] H) :
    TauCeti.Bialgebra.TensorProduct.baseChangeTensorBialgEquiv k K H H
        (Algebra.TensorProduct.includeRight y) =
      TensorProduct.AlgebraTensorModule.distribBaseChange k K H H
        (Algebra.TensorProduct.includeRight y) := by
  induction y using TensorProduct.inductionOn with
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul x y =>
      rw [Algebra.TensorProduct.includeRight_apply,
        TauCeti.Bialgebra.TensorProduct.baseChangeTensorBialgEquiv_tmul,
        TensorProduct.AlgebraTensorModule.distribBaseChange_tmul]

/-- The tensor bialgebra base-change equivalence carries the tensor swap of an element from the
original tensor square to the tensor swap of its image. -/
private theorem baseChangeTensorBialgEquiv_includeRight_comm (y : H ⊗[k] H) :
    TauCeti.Bialgebra.TensorProduct.baseChangeTensorBialgEquiv k K H H
        (Algebra.TensorProduct.includeRight (TensorProduct.comm k H H y)) =
      TensorProduct.comm K (K ⊗[k] H) (K ⊗[k] H)
        (TauCeti.Bialgebra.TensorProduct.baseChangeTensorBialgEquiv k K H H
          (Algebra.TensorProduct.includeRight y)) := by
  induction y using TensorProduct.inductionOn with
  | add x y hx hy =>
      simpa only [map_add, LinearMap.map_add] using congrArg₂ (· + ·) hx hy
  | tmul x y =>
      simp only [TensorProduct.comm_tmul, Algebra.TensorProduct.includeRight_apply,
        TauCeti.Bialgebra.TensorProduct.baseChangeTensorBialgEquiv_tmul]

/-- Cocommutativity descends from a field extension. -/
theorem of_baseChange [h : _root_.Coalgebra.IsCocomm K (K ⊗[k] H)] :
    _root_.Coalgebra.IsCocomm k H := by
  constructor
  ext x
  apply Algebra.TensorProduct.includeRight_injective (B := H ⊗[k] H)
    (algebraMap k K).injective
  let e := TauCeti.Bialgebra.TensorProduct.baseChangeTensorBialgEquiv k K H H
  apply e.injective
  have he_comul :
      e (Algebra.TensorProduct.includeRight (Coalgebra.comul (R := k) x)) =
        Coalgebra.comul (R := K) (Algebra.TensorProduct.includeRight x) := by
    rw [baseChangeTensorBialgEquiv_includeRight]
    simp only [Algebra.TensorProduct.includeRight_apply]
    rw [TauCeti.Coalgebra.baseChange_comul_tmul]
  calc
    e (Algebra.TensorProduct.includeRight
        (TensorProduct.comm k H H (Coalgebra.comul (R := k) x))) =
        TensorProduct.comm K (K ⊗[k] H) (K ⊗[k] H)
          (e (Algebra.TensorProduct.includeRight (Coalgebra.comul (R := k) x))) :=
      baseChangeTensorBialgEquiv_includeRight_comm (Coalgebra.comul (R := k) x)
    _ = TensorProduct.comm K (K ⊗[k] H) (K ⊗[k] H)
        (Coalgebra.comul (R := K) (Algebra.TensorProduct.includeRight x)) :=
      congrArg (TensorProduct.comm K (K ⊗[k] H) (K ⊗[k] H)) he_comul
    _ = Coalgebra.comul (R := K) (Algebra.TensorProduct.includeRight x) :=
      Coalgebra.comm_comul K (Algebra.TensorProduct.includeRight x)
    _ = e (Algebra.TensorProduct.includeRight (Coalgebra.comul (R := k) x)) := he_comul.symm

end TauCeti.Coalgebra.IsCocomm


