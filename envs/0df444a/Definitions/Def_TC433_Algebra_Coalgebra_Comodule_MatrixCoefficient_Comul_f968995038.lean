-- Prove2me | Definitions.Def_TC433_Algebra_Coalgebra_Comodule_MatrixCoefficient_Comul_f968995038
-- name    : TC433_Algebra_Coalgebra_Comodule_MatrixCoefficient_Comul_f968995038
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:03:17.955141+00:00
-- url     : https://prove2.me/theorems/ab69cf19-face-4a15-9b58-d012be898c74
-- title:
--   TauCeti: Algebra / Coalgebra / Comodule / MatrixCoefficient / Comul
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Comul for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/Algebra/Coalgebra/Comodule/MatrixCoefficient/Comul.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import Definitions.Def_TC433_Compat4331_Tensor_6326550516

import Mathlib.RingTheory.Coalgebra.CoassocSimps
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Definitions.Def_TC433_Algebra_Coalgebra_Comodule_MatrixCoefficient_Basic_dbc1f44765

/-!
# Comultiplication of matrix coefficients

The comultiplication of a matrix coefficient is controlled by the coaction:

```text
Δ(c(φ, m)) = (c(φ, ·) ⊗ id)(ρ(m)).
```

For a finite basis `(eᵢ)`, expanding the coaction in that basis gives the familiar formula

```text
Δ(c(φ, m)) = ∑ i, c(φ, eᵢ) ⊗ c(eⁱ, m).
```

Both formulas are basic facts about matrix coefficients; the finite-basis expansion is what
makes the coefficient submodule of a finite free comodule stable under comultiplication in
`TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Subcoalgebra`.

## Main declarations

* `TauCeti.Comodule.comul_matrixCoefficient`: the basis-free comultiplication formula.
* `TauCeti.Comodule.comul_matrixCoefficient_eq_sum`: its expansion in a finite basis.
* `TauCeti.Comodule.coact_eq_sum_basis_matrixCoefficient`: the expansion of the coaction itself
  in a finite basis.

## References

This is the standard coefficient-coalgebra computation; see Sweedler, *Hopf Algebras*,
Chapter 2. It supplies a prerequisite for `ReductiveGroups/README.md` in TauCetiRoadmap,
Layer 1, "Finite-dimensional subcoalgebras".
-/

public section
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct
open TensorProduct Module

namespace TauCeti.Comodule

universe u v w x

variable {R : Type u} {C : Type v} {M : Type w}
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]

/-- Comultiplication of a matrix coefficient is obtained by applying its coefficient map to
the vector factor of the coaction. -/
@[simp]
theorem comul_matrixCoefficient (φ : Module.Dual R M) (m : M) :
    Coalgebra.comul (R := R) (A := C)
        (matrixCoefficient (R := R) (C := C) φ m) =
      TensorProduct.map
        (matrixCoefficientLinear (R := R) (C := C) φ) LinearMap.id
        (coact (R := R) (C := C) (M := M) m) := by
  -- Expose matrix coefficients as composite linear maps so `coassoc_simps` can rewrite
  -- coassociativity without tensor induction.
  change (Coalgebra.comul ∘ₗ (TensorProduct.lid R C).toLinearMap ∘ₗ
          TensorProduct.map φ LinearMap.id ∘ₗ
          coact (R := R) (C := C) (M := M)) m =
        (TensorProduct.map
            ((TensorProduct.lid R C).toLinearMap ∘ₗ
              TensorProduct.map φ LinearMap.id ∘ₗ
              coact (R := R) (C := C) (M := M))
            LinearMap.id ∘ₗ
          coact (R := R) (C := C) (M := M)) m
  apply LinearMap.congr_fun ?_ m
  calc
    _ = (TensorProduct.lid R (C ⊗[R] C)).toLinearMap ∘ₗ
        TensorProduct.map φ LinearMap.id ∘ₗ
        TensorProduct.map LinearMap.id Coalgebra.comul ∘ₗ
        coact (R := R) (C := C) (M := M) := by
          simp only [coassoc_simps]
    _ = (TensorProduct.lid R (C ⊗[R] C)).toLinearMap ∘ₗ
        TensorProduct.map φ LinearMap.id ∘ₗ
        (TensorProduct.assoc R M C C).toLinearMap ∘ₗ
        TensorProduct.map (coact (R := R) (C := C) (M := M)) LinearMap.id ∘ₗ
        coact (R := R) (C := C) (M := M) := by
          simpa only [coassoc_simps] using congrArg
            (fun f : M →ₗ[R] M ⊗[R] (C ⊗[R] C) =>
              (TensorProduct.lid R (C ⊗[R] C)).toLinearMap ∘ₗ
                TensorProduct.map φ LinearMap.id ∘ₗ f)
            (coact_coassoc (R := R) (C := C) (M := M)).symm
    _ = TensorProduct.map
          ((TensorProduct.lid R C).toLinearMap ∘ₗ
            TensorProduct.map φ LinearMap.id)
          LinearMap.id ∘ₗ
        TensorProduct.map (coact (R := R) (C := C) (M := M)) LinearMap.id ∘ₗ
        coact (R := R) (C := C) (M := M) := by
          simp only [TensorProduct.lid_tensor, coassoc_simps]
    _ = _ := by
      simp only [coassoc_simps]

omit [Coalgebra R C] [Comodule R C M] in
private theorem tensor_eq_sum_basis_tmul {ι : Type x} [Fintype ι] (b : Basis ι R M) (x : M ⊗[R] C) :
    x =
      ∑ i, b i ⊗ₜ[R]
        TensorProduct.lid R C
          (TensorProduct.map (b.coord i) LinearMap.id x) := by
  classical
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := C) b
  calc
    x = e.symm (e x) := (e.symm_apply_apply x).symm
    _ = (e x).sum fun i n => b i ⊗ₜ[R] n :=
      TensorProduct.equivFinsuppOfBasisLeft_symm_apply b (e x)
    _ = ∑ i, b i ⊗ₜ[R] (e x i) := Finsupp.sum_fintype _ _ (by simp)
    _ = ∑ i, b i ⊗ₜ[R]
        TensorProduct.lid R C
          (TensorProduct.map (b.coord i) LinearMap.id x) := by
      congr 1
      funext i
      rw [TensorProduct.equivFinsuppOfBasisLeft_apply]
      simp only [LinearMap.rTensor]

/-- The coaction of a comodule with a finite basis `(eᵢ)` expands as
`ρ(m) = ∑ i, eᵢ ⊗ c(eⁱ, m)` in matrix coefficients. -/
theorem coact_eq_sum_basis_matrixCoefficient {ι : Type x} [Fintype ι] (b : Basis ι R M) (m : M) :
    coact (R := R) (C := C) (M := M) m =
      ∑ i, b i ⊗ₜ[R]
        matrixCoefficient (R := R) (C := C) (b.coord i) m := by
  simpa only [matrixCoefficient_def] using
    tensor_eq_sum_basis_tmul (C := C) b
      (coact (R := R) (C := C) (M := M) m)

/-- The comultiplication of a matrix coefficient, expanded in a finite basis. -/
theorem comul_matrixCoefficient_eq_sum {ι : Type x} [Fintype ι]
    (b : Basis ι R M) (φ : Module.Dual R M) (m : M) :
    Coalgebra.comul (R := R) (A := C)
        (matrixCoefficient (R := R) (C := C) φ m) =
      ∑ i, matrixCoefficient (R := R) (C := C) φ (b i) ⊗ₜ[R]
        matrixCoefficient (R := R) (C := C) (b.coord i) m := by
  rw [comul_matrixCoefficient,
    coact_eq_sum_basis_matrixCoefficient (C := C) b, map_sum]
  simp only [TensorProduct.map_tmul, LinearMap.id_apply,
    matrixCoefficientLinear_apply]

end TauCeti.Comodule


