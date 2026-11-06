-- Prove2me | Definitions.Def_TC433_Algebra_Coalgebra_Comodule_PointAction_f458ecf638
-- name    : TC433_Algebra_Coalgebra_Comodule_PointAction_f458ecf638
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:15:20.6067+00:00
-- url     : https://prove2.me/theorems/52ece079-feea-46ad-ad5d-2f96579cc3a2
-- title:
--   TauCeti: Algebra / Coalgebra / Comodule / PointAction
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.Algebra.Coalgebra.Comodule.PointAction for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/Algebra/Coalgebra/Comodule/PointAction.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import Definitions.Def_TC433_Compat4331_Tensor_6326550516

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Definitions.Def_TC433_Algebra_Coalgebra_Comodule_PointsAction_d42f6c2ad0
import Definitions.Def_TC433_Algebra_Coalgebra_Comodule_Evaluation_a8cf0c32e2
import Definitions.Def_TC433_RingTheory_FiniteType_PointSeparation_4425f69b81

/-!
# Detecting comodule fixed vectors on geometric points

Let `H` be a reduced commutative bialgebra of finite type over a field `k`, and let `M` be an
`H`-comodule. A vector `m : M` is fixed by the coaction if and only if every point of `H` valued in
an algebraically closed extension fixes `1 ⊗ m` in the scalar extension.

The reverse implication is the substantive one. Evaluating the pointwise fixed-vector equation
against every linear functional shows that every geometric point takes the corresponding matrix
coefficient of `m` to its trivial-comodule value. Reduced finite-type point separation then
identifies those coefficients in `H`. A finite-dimensional subspace containing the single tensor
`coact m - m ⊗ 1` has enough coordinate functionals to show that this tensor vanishes.

The representation-level restatements live in
`TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction`. This criterion is the bridge in the
Kolchin induction for Layer 5 of the ReductiveGroups roadmap: a common fixed vector obtained from
the geometric point representation is thereby promoted to a fixed vector of the comodule itself.

## Main declarations

* `TauCeti.Comodule.coact_eq_tmul_one_iff_forall_endOfPoint_tmul_eq`: geometric-point detection of
  a fixed vector for a bialgebra comodule.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, §2.4.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

namespace TauCeti.Comodule

open WithConv

universe u v w x

noncomputable section

section Bialgebra

variable {k : Type u} {H : Type v} {M : Type w} {K : Type x}
variable [Field k] [CommRing H] [Bialgebra k H] [Algebra.FiniteType k H] [IsReduced H]
variable [AddCommGroup M] [Module k M] [Comodule k H M]
variable [Field K] [Algebra k K] [IsAlgClosed K]

/-- A vector in a comodule over a reduced finite-type bialgebra is fixed by the coaction exactly
when every algebraically closed point fixes its scalar extension. -/
theorem coact_eq_tmul_one_iff_forall_endOfPoint_tmul_eq (m : M) :
    coact (R := k) (C := H) m = m ⊗ₜ[k] (1 : H) ↔
      ∀ g : H →ₐ[k] K, endOfPoint M g (1 ⊗ₜ[k] m) = 1 ⊗ₜ[k] m := by
  constructor
  · intro hm g
    rw [endOfPoint_tmul, hm]
    simp
  · intro h
    have hcoeff (φ : Module.Dual k M) :
        matrixCoefficient (C := H) φ m = (φ m) • (1 : H) := by
      apply TauCeti.eq_of_forall_algHom_apply_eq (k := k) (K := K)
      intro g
      have heval := congrArg
        (fun z ↦ TauCeti.Module.Dual.baseChangeEvaluation
          (R := k) (M := M) (A := K) (1 ⊗ₜ[k] φ) z) (h g)
      simpa [Algebra.smul_def] using heval
    let z := coact (R := k) (C := H) m - m ⊗ₜ[k] (1 : H)
    suffices z = 0 by exact sub_eq_zero.mp this
    obtain ⟨M', hM', hz⟩ := TensorProduct.exists_finite_submodule_left_of_setFinite
      ({z} : Set (M ⊗[k] H)) (Set.finite_singleton z)
    obtain ⟨z', hz'⟩ := hz (Set.mem_singleton z)
    let _ : Module.Finite k M' := hM'
    let b := Module.finBasis k M'
    have hz'zero : z' = 0 := by
      apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
      ext i
      rw [map_zero, Finsupp.zero_apply, TensorProduct.equivFinsuppOfBasisLeft_apply]
      obtain ⟨φ, hφ⟩ := LinearMap.exists_extend (b.coord i)
      rw [← hφ, LinearMap.rTensor_comp_apply, hz']
      simpa [z, matrixCoefficient_def, LinearMap.rTensor_def] using
        sub_eq_zero.mpr (hcoeff φ)
    rw [← hz', hz'zero, map_zero]

end Bialgebra

end

end TauCeti.Comodule


