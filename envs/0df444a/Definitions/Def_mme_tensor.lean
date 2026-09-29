-- Prove2me | Definitions.Def_mme_tensor
-- name    : mme_tensor
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-05-28T14:35:36.850579+00:00
-- url     : https://prove2.me/theorems/2ba003dc-faf4-41a7-92f0-9583131c4ccf
-- statement:
--   Order-`d` tensor objects with **direct sum** and **Kronecker product**.
--
--   A `TensorObj K d` is a family of finite-dimensional `K`-vector spaces `V : Fin d → Type` together with an element `t : ⨂ᵢ V i`. Direct sum `add` (mode-wise product of spaces) and Kronecker product `kron` (mode-wise tensor product, built from the bilinear **interchange** map $(\bigotimes_i V_i)\otimes(\bigotimes_i W_i)\to\bigotimes_i(V_i\otimes W_i)$) give the semiring operations $\oplus$ and $\otimes$. Also provides `zeroObj`, `oneObj`, the diagonal unit `diagObj r`, the finite direct sum `bigAdd`, and the Kronecker power `kronPow`. Foundations for tensor rank and the matrix-multiplication exponent (Wigderson–Zuiddam framework).
-- source:
--   https://www.math.ias.edu/~avi/PUBLICATIONS/WigdersonZu_Final_Draft_Oct2023.pdf

import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.Prod
import Mathlib.Algebra.Module.PUnit
import Mathlib.Algebra.BigOperators.Pi

/-! # Order-`d` tensor objects: direct sum and Kronecker product

A concrete order-`d` tensor is a family of finite-dimensional `K`-vector spaces
`V : Fin d → Type` together with an element `t : ⨂ᵢ V i`. This file builds the two
operations the asymptotic theory needs — direct sum (`add`, `⊕`) and Kronecker product
(`kron`, `⊗`, via the mode-wise `interchange` map) — plus the unit/zero/diagonal
objects and the `bigAdd` / `kronPow` combinators used to phrase asymptotic rank.

We work directly with `TensorObj` (no isomorphism quotient): everything downstream is
phrased through restriction, which is automatically isomorphism-invariant. -/

universe u

open PiTensorProduct TensorProduct BigOperators

set_option maxHeartbeats 800000

namespace MME

/-- A concrete order-`d` tensor: `d` finite-dimensional `K`-spaces and an element of
their iterated tensor product. -/
structure TensorObj (K : Type u) [Field K] (d : ℕ) where
  V : Fin d → Type u
  [acg : ∀ i, AddCommGroup (V i)]
  [mod : ∀ i, Module K (V i)]
  [fin : ∀ i, Module.Finite K (V i)]
  t : PiTensorProduct K V

attribute [instance] TensorObj.acg TensorObj.mod TensorObj.fin

/-! ## The mode-wise interchange map

`interchange : (⨂ᵢ Vᵢ) ⊗ (⨂ᵢ Wᵢ) → ⨂ᵢ (Vᵢ ⊗ Wᵢ)`, the bilinear map underlying the
Kronecker product. Built by a double application of the `PiTensorProduct` universal
property. (mathlib's `tmulEquiv` merges index sets and does not provide this.) -/

section Interchange

variable {K : Type u} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {V W : ι → Type u}
  [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]

/-- For a fixed pure factor `v`, the multilinear map `w ↦ ⨂ᵢ (v i ⊗ w i)`. -/
def interchangeInner (v : ∀ i, V i) :
    MultilinearMap K W (PiTensorProduct K (fun i => V i ⊗[K] W i)) where
  toFun w := tprod K fun i => v i ⊗ₜ[K] w i
  map_update_add' w i x y := by
    have h1 : (fun j => v j ⊗ₜ[K] Function.update w i (x + y) j) =
        Function.update (fun j => v j ⊗ₜ[K] w j) i (v i ⊗ₜ[K] (x + y)) := by
      ext j; by_cases h : j = i
      · subst h; simp
      · simp [h]
    have h3 : Function.update (fun j => v j ⊗ₜ[K] w j) i (v i ⊗ₜ[K] x) =
        (fun j => v j ⊗ₜ[K] Function.update w i x j) := by
      ext j; by_cases h : j = i
      · subst h; simp
      · simp [h]
    have h4 : Function.update (fun j => v j ⊗ₜ[K] w j) i (v i ⊗ₜ[K] y) =
        (fun j => v j ⊗ₜ[K] Function.update w i y j) := by
      ext j; by_cases h : j = i
      · subst h; simp
      · simp [h]
    calc (tprod K) (fun j => v j ⊗ₜ[K] (Function.update w i (x + y)) j)
        _ = (tprod K) (Function.update (fun j => v j ⊗ₜ[K] w j) i (v i ⊗ₜ[K] (x + y))) := by rw [h1]
        _ = (tprod K) (Function.update (fun j => v j ⊗ₜ[K] w j) i
              (v i ⊗ₜ[K] x + v i ⊗ₜ[K] y)) := by rw [TensorProduct.tmul_add]
        _ = (tprod K) (Function.update (fun j => v j ⊗ₜ[K] w j) i (v i ⊗ₜ[K] x)) +
            (tprod K) (Function.update (fun j => v j ⊗ₜ[K] w j) i (v i ⊗ₜ[K] y)) := by
            rw [MultilinearMap.map_update_add]
        _ = (tprod K) (fun j => v j ⊗ₜ[K] (Function.update w i x) j) +
            (tprod K) (fun j => v j ⊗ₜ[K] (Function.update w i y) j) := by rw [h3, h4]
  map_update_smul' w i c x := by
    have h1 : (fun j => v j ⊗ₜ[K] Function.update w i (c • x) j) =
        Function.update (fun j => v j ⊗ₜ[K] w j) i (v i ⊗ₜ[K] (c • x)) := by
      ext j; by_cases h : j = i
      · subst h; simp
      · simp [h]
    calc (tprod K) (fun j => v j ⊗ₜ[K] (Function.update w i (c • x)) j)
        _ = (tprod K) (Function.update (fun j => v j ⊗ₜ[K] w j) i (v i ⊗ₜ[K] (c • x))) := by rw [h1]
        _ = (tprod K) (Function.update (fun j => v j ⊗ₜ[K] w j) i (c • (v i ⊗ₜ[K] x))) := by
            rw [TensorProduct.tmul_smul]
        _ = c • (tprod K) (Function.update (fun j => v j ⊗ₜ[K] w j) i (v i ⊗ₜ[K] x)) := by
            rw [MultilinearMap.map_update_smul]
        _ = c • (tprod K) (fun j => v j ⊗ₜ[K] (Function.update w i x) j) := by
            congr 1; congr; ext j; by_cases h : j = i
            · subst h; simp
            · simp [h]

/-- The multilinear map `v ↦ (lift of interchangeInner v)`, linear in the second tensor. -/
noncomputable def interchangeOuter :
    MultilinearMap K V
      (PiTensorProduct K W →ₗ[K] PiTensorProduct K (fun i => V i ⊗[K] W i)) where
  toFun v := lift (interchangeInner v)
  map_update_add' v i x y := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext; intro m
    simp only [LinearMap.add_apply, LinearMap.compMultilinearMap_apply, PiTensorProduct.lift.tprod]
    dsimp [interchangeInner]
    have h1 : (fun j => Function.update v i (x + y) j ⊗ₜ[K] m j) =
        Function.update (fun j => v j ⊗ₜ[K] m j) i ((x + y) ⊗ₜ[K] m i) := by
      ext j; by_cases h : j = i
      · subst h; simp
      · simp [h]
    have h3 : Function.update (fun j => v j ⊗ₜ[K] m j) i (x ⊗ₜ[K] m i) =
        (fun j => Function.update v i x j ⊗ₜ[K] m j) := by
      ext j; by_cases h : j = i
      · subst h; simp
      · simp [h]
    have h4 : Function.update (fun j => v j ⊗ₜ[K] m j) i (y ⊗ₜ[K] m i) =
        (fun j => Function.update v i y j ⊗ₜ[K] m j) := by
      ext j; by_cases h : j = i
      · subst h; simp
      · simp [h]
    calc (tprod K) (fun j => (Function.update v i (x + y)) j ⊗ₜ[K] m j)
        _ = (tprod K) (Function.update (fun j => v j ⊗ₜ[K] m j) i ((x + y) ⊗ₜ[K] m i)) := by rw [h1]
        _ = (tprod K) (Function.update (fun j => v j ⊗ₜ[K] m j) i
              (x ⊗ₜ[K] m i + y ⊗ₜ[K] m i)) := by rw [TensorProduct.add_tmul]
        _ = (tprod K) (Function.update (fun j => v j ⊗ₜ[K] m j) i (x ⊗ₜ[K] m i)) +
            (tprod K) (Function.update (fun j => v j ⊗ₜ[K] m j) i (y ⊗ₜ[K] m i)) := by
            rw [MultilinearMap.map_update_add]
        _ = (tprod K) (fun j => (Function.update v i x) j ⊗ₜ[K] m j) +
            (tprod K) (fun j => (Function.update v i y) j ⊗ₜ[K] m j) := by rw [h3, h4]
  map_update_smul' v i c x := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext; intro m
    simp only [LinearMap.smul_apply, LinearMap.compMultilinearMap_apply, PiTensorProduct.lift.tprod]
    dsimp [interchangeInner]
    have h1 : (fun j => Function.update v i (c • x) j ⊗ₜ[K] m j) =
        Function.update (fun j => v j ⊗ₜ[K] m j) i ((c • x) ⊗ₜ[K] m i) := by
      ext j; by_cases h : j = i
      · subst h; simp
      · simp [h]
    calc (tprod K) (fun j => (Function.update v i (c • x)) j ⊗ₜ[K] m j)
        _ = (tprod K) (Function.update (fun j => v j ⊗ₜ[K] m j) i ((c • x) ⊗ₜ[K] m i)) := by rw [h1]
        _ = (tprod K) (Function.update (fun j => v j ⊗ₜ[K] m j) i (c • (x ⊗ₜ[K] m i))) := by
            rw [TensorProduct.smul_tmul']
        _ = c • (tprod K) (Function.update (fun j => v j ⊗ₜ[K] m j) i (x ⊗ₜ[K] m i)) := by
            rw [MultilinearMap.map_update_smul]
        _ = c • (tprod K) (fun j => (Function.update v i x) j ⊗ₜ[K] m j) := by
            congr 1; congr; ext j; by_cases h : j = i
            · subst h; simp
            · simp [h]

/-- The mode-wise interchange bilinear map. -/
noncomputable def interchange :
    PiTensorProduct K V →ₗ[K]
      PiTensorProduct K W →ₗ[K] PiTensorProduct K (fun i => V i ⊗[K] W i) :=
  lift interchangeOuter

end Interchange

namespace TensorObj

variable {K : Type u} [Field K] {d : ℕ}

/-- Direct sum: mode-wise product of the spaces. -/
noncomputable def add (X Y : TensorObj K d) : TensorObj K d where
  V i := X.V i × Y.V i
  t := PiTensorProduct.map (fun i => LinearMap.inl K (X.V i) (Y.V i)) X.t +
       PiTensorProduct.map (fun i => LinearMap.inr K (X.V i) (Y.V i)) Y.t

/-- Kronecker product: mode-wise tensor product of the spaces, via `interchange`. -/
noncomputable def kron (X Y : TensorObj K d) : TensorObj K d where
  V i := X.V i ⊗[K] Y.V i
  t := interchange X.t Y.t

/-- The zero tensor object. -/
noncomputable def zeroObj : TensorObj K d where
  V _ := PUnit
  t := 0

/-- The unit tensor object: each mode is `K`, element is `1 ⊗ ⋯ ⊗ 1`. -/
noncomputable def oneObj : TensorObj K d where
  V _ := K
  t := tprod K (fun _ => (1 : K))

/-- The `r`-dimensional diagonal unit tensor `∑_{j<r} e_j ⊗ ⋯ ⊗ e_j`; the right-hand
side of `T ≤ r` for restriction rank. -/
noncomputable def diagObj (K : Type u) [Field K] (d r : ℕ) : TensorObj K d where
  V _ := Fin r → K
  t := ∑ j : Fin r, tprod K (fun _ => (Pi.single j 1 : Fin r → K))

/-- Finite direct sum of a family of tensor objects. -/
noncomputable def bigAdd : {k : ℕ} → (Fin k → TensorObj K d) → TensorObj K d
  | 0,      _ => zeroObj
  | 1,      f => f 0
  | (_+2),  f => add (f 0) (bigAdd (fun i => f i.succ))

/-- `n`-fold Kronecker power; `kronPow X 0 = oneObj`. -/
noncomputable def kronPow (X : TensorObj K d) : ℕ → TensorObj K d
  | 0      => oneObj
  | (n+1)  => kron X (kronPow X n)

end TensorObj

end MME


