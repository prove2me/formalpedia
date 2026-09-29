-- Prove2me | Definitions.Def_AutomorphicForm_TwistedCommutant
-- name    : AutomorphicForm_TwistedCommutant
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/e3185857-a262-5b44-8b0a-fe5935adf76f
-- title:
--   Twisted commutant subalgebra of a matrix over L⊗K​A
-- statement:
--   Throughout, $L/K$ is an extension of fields, $A$ a commutative $K$-algebra, $\sigma$ a $K$-algebra automorphism of $L$, and $\sigma$ acts on $L\otimes_K A$ through the ring homomorphism `sigmaTensor`, the base change $\sigma\otimes\mathrm{id}_A$; on matrices it acts entrywise, and on $\mathrm{GL}_2$ through the induced group homomorphism `sigmaGL`. Two small lemmas record that `sigmaTensor` fixes the image of $K$ and fixes each element $1\otimes a$ with $a\in A$.
--
--   The main definition, `twistedCommutant`, attaches to $\delta\in\mathrm{GL}_2(L\otimes_K A)$ the $K$-subalgebra
--   $$D_\delta=\{X\in M_2(L\otimes_K A)\;:\;X\,\delta=\delta\,\sigma(X)\}$$
--   of $M_2(L\otimes_K A)$, where $\delta$ is taken through its underlying matrix; `mem_twistedCommutant_iff` is the defining membership criterion, and the subalgebra fields record closure under addition and multiplication and that the image of $K$ lies in $D_\delta$. Further lemmas: multiplication by a scalar $1\otimes a$, $a\in A$, preserves $D_\delta$; an element $t\in\mathrm{GL}_2(L\otimes_K A)$ lies in the twisted centralizer $\{t: t\delta\sigma(t)^{-1}=\delta\}$ exactly when its matrix lies in $D_\delta$, whence `twistedCentralizerEquivUnits`, a group isomorphism of the twisted centralizer of $\delta$ with the unit group $D_\delta^\times$, compatible with the underlying matrices; and for $X\in D_\delta$ one has $\det X\cdot\det\delta=\det\delta\cdot\sigma(\det X)$.
--
--   The topological part assumes $L/K$ finite and $A$ a topological commutative $K$-algebra, with $L\otimes_K A$ carrying the $A$-module topology: `sigmaTensor` is continuous ($A$-linear on a finite module topology), $D_\delta$ is closed in $M_2(L\otimes_K A)$ when $A$ is Hausdorff, and locally compact when $A$ is in addition locally compact. Finally `twistedCommutantBorel` names the Borel $\sigma$-algebra of $D_\delta$ for the subspace topology, together with the fact that it is a Borel space, so that Haar measures on $D_\delta$ can appear as arguments later.
--
--   **Relation to Mathlib.** Mathlib supplies the ingredients ($\sigma\otimes\mathrm{id}$ as `Algebra.TensorProduct.map`, the `GL` functoriality map, `Subalgebra`, `borel`), but the $\sigma$-twisted commutant of a matrix and its identification with the twisted centralizer are the project's own notions; the untwisted case corresponds to Mathlib's `Subgroup.centralizer`.
--
--   **Where it is used.** The twisted commutant is the additive companion of the $\sigma$-twisted centralizer occurring in the comparison of twisted and ordinary orbital integrals for cyclic base change on $\mathrm{GL}_2$; its closedness, local compactness and Borel structure are what allow Haar measures on twisted centralizers to be used in the matching conditions for test functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_TwistedCommutant.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open TensorProduct
open scoped TensorProduct.RightActions

noncomputable section

namespace AutomorphicForm

section Algebra

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
  (σ : L ≃ₐ[K] L)

theorem sigmaTensor_algebraMap (r : K) :
    sigmaTensor K L A σ (algebraMap K (L ⊗[K] A) r) = algebraMap K (L ⊗[K] A) r :=
  (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A)).commutes r

theorem sigmaTensor_includeRight (a : A) :
    sigmaTensor K L A σ (Algebra.TensorProduct.includeRight (R := K) (A := L) a) =
      Algebra.TensorProduct.includeRight (R := K) (A := L) a := by
  show Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A) ((1 : L) ⊗ₜ[K] a) = (1 : L) ⊗ₜ[K] a
  rw [Algebra.TensorProduct.map_tmul]
  simp

def twistedCommutant (δ : GL (Fin 2) (L ⊗[K] A)) : Subalgebra K (Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) where
  carrier := {X | X * (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
    (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) * X.map (sigmaTensor K L A σ)}
  mul_mem' := by
    intro X Y hX hY
    simp only [Set.mem_setOf_eq] at hX hY ⊢
    have hm : (X * Y).map (sigmaTensor K L A σ) = X.map (sigmaTensor K L A σ) * Y.map (sigmaTensor K L A σ) := by
      rw [← RingHom.mapMatrix_apply, map_mul]; rfl
    rw [hm, mul_assoc, hY, ← mul_assoc, hX, mul_assoc]
  one_mem' := by
    simp only [Set.mem_setOf_eq]
    rw [Matrix.map_one _ (map_zero _) (map_one _), one_mul, mul_one]
  add_mem' := by
    intro X Y hX hY
    simp only [Set.mem_setOf_eq] at hX hY ⊢
    have hm : (X + Y).map (sigmaTensor K L A σ) = X.map (sigmaTensor K L A σ) + Y.map (sigmaTensor K L A σ) := by
      rw [← RingHom.mapMatrix_apply, map_add]; rfl
    rw [hm, add_mul, mul_add, hX, hY]
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    rw [Matrix.map_zero _ (map_zero _), zero_mul, mul_zero]
  algebraMap_mem' := by
    intro r
    simp only [Set.mem_setOf_eq]
    have hmap : (algebraMap K (Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) r).map (sigmaTensor K L A σ) =
        algebraMap K (Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) r := by
      rw [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_map (map_zero _)]
      congr 1
      funext i
      exact sigmaTensor_algebraMap K L A σ r
    rw [hmap]
    exact Algebra.commutes r _

variable {K L A σ}

theorem mem_twistedCommutant_iff (δ : GL (Fin 2) (L ⊗[K] A)) (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) :
    X ∈ twistedCommutant K L A σ δ ↔
      X * (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
        (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) * X.map (sigmaTensor K L A σ) :=
  Iff.rfl

theorem coe_sigmaGL (t : GL (Fin 2) (L ⊗[K] A)) :
    ((sigmaGL K L A σ t : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
      (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).map (sigmaTensor K L A σ) := by
  ext i j
  exact Matrix.GeneralLinearGroup.map_apply _ i j t

theorem mem_twistedCentralizer_iff_coe_mem_twistedCommutant (δ t : GL (Fin 2) (L ⊗[K] A)) :
    t ∈ twistedCentralizer K L A σ δ ↔
      (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) ∈ twistedCommutant K L A σ δ := by
  show t * δ * (sigmaGL K L A σ t)⁻¹ = δ ↔ _
  rw [mem_twistedCommutant_iff, mul_inv_eq_iff_eq_mul, ← coe_sigmaGL]
  constructor
  · intro h
    have := congrArg (fun g : GL (Fin 2) (L ⊗[K] A) => (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))) h
    simpa only [Matrix.GeneralLinearGroup.coe_mul] using this
  · intro h
    refine Units.ext ?_
    simpa only [Matrix.GeneralLinearGroup.coe_mul] using h

theorem includeRight_smul_mem_twistedCommutant (δ : GL (Fin 2) (L ⊗[K] A)) {X : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)}
    (hX : X ∈ twistedCommutant K L A σ δ) (a : A) :
    (Algebra.TensorProduct.includeRight (R := K) (A := L) a) • X ∈ twistedCommutant K L A σ δ := by
  rw [mem_twistedCommutant_iff] at hX ⊢
  have hm : ((Algebra.TensorProduct.includeRight (R := K) (A := L) a) • X).map (sigmaTensor K L A σ) =
      (Algebra.TensorProduct.includeRight (R := K) (A := L) a) • X.map (sigmaTensor K L A σ) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, sigmaTensor_includeRight]
  rw [Matrix.smul_mul, hX, hm, Matrix.mul_smul]

def twistedCentralizerEquivUnits (δ : GL (Fin 2) (L ⊗[K] A)) :
    twistedCentralizer K L A σ δ ≃* (twistedCommutant K L A σ δ)ˣ where
  toFun t :=
    { val := ⟨((t : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)),
        (mem_twistedCentralizer_iff_coe_mem_twistedCommutant δ _).1 t.2⟩
      inv := ⟨(((t : GL (Fin 2) (L ⊗[K] A))⁻¹ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)),
        (mem_twistedCentralizer_iff_coe_mem_twistedCommutant δ _).1 (Subgroup.inv_mem _ t.2)⟩
      val_inv := Subtype.ext (by
        show ((t : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) *
            (((t : GL (Fin 2) (L ⊗[K] A))⁻¹ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) = 1
        rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel]; rfl)
      inv_val := Subtype.ext (by
        show (((t : GL (Fin 2) (L ⊗[K] A))⁻¹ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) *
            ((t : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) = 1
        rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel]; rfl) }
  invFun u :=
    ⟨{ val := ((u : twistedCommutant K L A σ δ) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))
       inv := (((u⁻¹ : (twistedCommutant K L A σ δ)ˣ) : twistedCommutant K L A σ δ) :
          Matrix (Fin 2) (Fin 2) (L ⊗[K] A))
       val_inv := by
         have h := congrArg (fun x : twistedCommutant K L A σ δ => (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))) u.val_inv
         simp only [Subalgebra.coe_mul, Subalgebra.coe_one] at h
         exact h
       inv_val := by
         have h := congrArg (fun x : twistedCommutant K L A σ δ => (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))) u.inv_val
         simp only [Subalgebra.coe_mul, Subalgebra.coe_one] at h
         exact h },
      (mem_twistedCentralizer_iff_coe_mem_twistedCommutant δ _).2 (u : twistedCommutant K L A σ δ).2⟩
  left_inv t := Subtype.ext (Units.ext rfl)
  right_inv u := Units.ext (Subtype.ext rfl)
  map_mul' t t' := Units.ext (Subtype.ext (Matrix.GeneralLinearGroup.coe_mul _ _))

theorem coe_twistedCentralizerEquivUnits (δ : GL (Fin 2) (L ⊗[K] A)) (t : twistedCentralizer K L A σ δ) :
    (((twistedCentralizerEquivUnits δ t : (twistedCommutant K L A σ δ)ˣ) : twistedCommutant K L A σ δ) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
      ((t : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) :=
  rfl

theorem det_mul_det_eq_det_mul_sigmaTensor_det {δ : GL (Fin 2) (L ⊗[K] A)} {X : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)}
    (hX : X ∈ twistedCommutant K L A σ δ) :
    X.det * (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).det =
      (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).det * sigmaTensor K L A σ X.det := by
  rw [mem_twistedCommutant_iff] at hX
  have := congrArg Matrix.det hX
  rw [Matrix.det_mul, Matrix.det_mul] at this
  rw [this, RingHom.map_det, RingHom.mapMatrix_apply]

end Algebra

section Topology

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] (σ : L ≃ₐ[K] L)

theorem continuous_sigmaTensor : Continuous (sigmaTensor K L A σ) := by
  haveI := isTopologicalRing_tensor K L A
  let φ : L ⊗[K] A →ₗ[A] L ⊗[K] A :=
    { toFun := sigmaTensor K L A σ
      map_add' := map_add _
      map_smul' := by
        intro a x
        show sigmaTensor K L A σ (a • x) = a • sigmaTensor K L A σ x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul l b =>
            show Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A) (l ⊗ₜ[K] (a • b)) =
              a • Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A) (l ⊗ₜ[K] b)
            rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
            rfl
        | add x y hx hy => rw [smul_add, map_add, map_add, smul_add, hx, hy] }
  exact IsModuleTopology.continuous_of_linearMap φ

theorem isClosed_twistedCommutant [T2Space A] (δ : GL (Fin 2) (L ⊗[K] A)) :
    IsClosed (twistedCommutant K L A σ δ : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] A))) := by
  haveI := isTopologicalRing_tensor K L A
  haveI := t2Space_tensor K L A
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → L ⊗[K] A))
  have h1 : Continuous fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] A) => X * (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) :=
    continuous_id.mul continuous_const
  have h2 : Continuous fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] A) =>
      (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) * X.map (sigmaTensor K L A σ) :=
    continuous_const.mul (continuous_id.matrix_map (continuous_sigmaTensor K L A σ))
  exact isClosed_eq h1 h2

theorem locallyCompactSpace_twistedCommutant [T2Space A] [LocallyCompactSpace A] (δ : GL (Fin 2) (L ⊗[K] A)) :
    LocallyCompactSpace (twistedCommutant K L A σ δ) := by
  haveI := locallyCompactSpace_tensor K L A
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → L ⊗[K] A))
  exact (isClosed_twistedCommutant K L A σ δ).isClosedEmbedding_subtypeVal.locallyCompactSpace

omit [IsTopologicalRing A] in

@[reducible] def twistedCommutantBorel (δ : GL (Fin 2) (L ⊗[K] A)) :
    MeasurableSpace (twistedCommutant K L A σ δ) := borel _

omit [IsTopologicalRing A] in
theorem borelSpace_twistedCommutantBorel (δ : GL (Fin 2) (L ⊗[K] A)) :
    @BorelSpace (twistedCommutant K L A σ δ) _ (twistedCommutantBorel K L A σ δ) :=
  @BorelSpace.mk _ _ (twistedCommutantBorel K L A σ δ) rfl

end Topology

end AutomorphicForm

end


