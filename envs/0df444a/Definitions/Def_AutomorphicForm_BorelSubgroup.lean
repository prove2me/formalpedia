-- Prove2me | Definitions.Def_AutomorphicForm_BorelSubgroup
-- name    : AutomorphicForm_BorelSubgroup
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/5de11970-f92d-5f7b-9050-f4cb6e3dce1e
-- title:
--   Borel subgroup of GL2​ and its diagonal characters
-- statement:
--   For a commutative ring $A$, `borelSubgroup A` is the subgroup of $\mathrm{GL}_2(A)$ consisting of those invertible matrices whose $(1,0)$ entry vanishes, i.e. the invertible upper-triangular matrices; membership is stated by `mem_borelSubgroup_iff`, and `borel_entry_one_zero` records the defining equation for an element of the coerced subtype. On this subgroup two monoid homomorphisms to $A^\times$ are defined: `borelDiagFst` sends $b$ to the unit whose value is the $(0,0)$ entry of $b$ and whose inverse is the $(0,0)$ entry of $b^{-1}$, and `borelDiagSnd` does the same with the $(1,1)$ entries; the lemmas `borelDiagFst_apply_val` and `borelDiagSnd_apply_val` identify their underlying ring elements with those matrix entries. The determinant of an upper-triangular element factors as the product of these two characters: `det_borel_eq_diag_mul` asserts the equality $\det x = b_{00}\,b_{11}$ in $A^\times$ for $x$ in the Borel subgroup. The unipotent elements $\begin{pmatrix}1&x\\0&1\end{pmatrix}$, given by the project's `unipotentGL2`, lie in the Borel subgroup and have both diagonal characters equal to $1$.
--
--   In the adelic setting, with $R$ a Dedekind domain and $K$ its fraction field, `adelicBorel R K` is an abbreviation for `borelSubgroup` applied to the adele ring $\mathbb{A}_K$, a subgroup of $\mathrm{GL}_2(\mathbb{A}_K)$. Three families of elements are placed in it. The entries of `globalPoints R K γ` are the images under $K \to \mathbb{A}_K$ of the entries of $\gamma$ (`globalPoints_apply`); consequently a $\gamma$ in the Borel subgroup of $\mathrm{GL}_2(K)$ maps into `adelicBorel R K`, and its two diagonal characters are obtained from those of $\gamma$ by applying `Units.map` along $K \to \mathbb{A}_K$. The central scalar matrix attached to a unit $z \in \mathbb{A}_K^\times$ likewise lies in `adelicBorel R K`, with both diagonal characters equal to $z$.
--
--   **Relation to Mathlib.** Mathlib supplies $\mathrm{GL}_n$ over a commutative ring together with its determinant, functoriality in the ring and scalar homomorphisms; the upper-triangular Borel subgroup of $\mathrm{GL}_2$ and its two diagonal characters are set up here as project definitions.
--
--   **Where it is used.** These definitions provide the adelic Borel subgroup and its torus coordinates used by the automorphic-forms layer, where the unipotent elements are the ones integrated over in the constant-term and cuspidality definitions, and the global and central families describe the transformation behaviour of functions on $\mathrm{GL}_2(\mathbb{A}_K)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_BorelSubgroup.lean

import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace AutomorphicForm

section BorelCommRing

variable (A : Type*) [CommRing A]

def borelSubgroup : Subgroup (GL (Fin 2) A) where
  carrier := {x | (x : Matrix (Fin 2) (Fin 2) A) 1 0 = 0}
  mul_mem' := by
    intro x y hx hy
    have hx' : (x : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := hx
    have hy' : (y : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := hy
    show ((x * y : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0 = 0
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hx', hy']
    ring
  one_mem' := by
    show ((1 : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0 = 0
    rw [Matrix.GeneralLinearGroup.coe_one]
    exact Matrix.one_apply_ne (by decide)
  inv_mem' := by
    intro x hx
    have hx' : (x : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := hx
    show ((x⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0 = 0
    rw [Matrix.GeneralLinearGroup.coe_inv, Matrix.inv_def]
    simp [Matrix.adjugate_fin_two, hx']

@[simp] theorem mem_borelSubgroup_iff {x : GL (Fin 2) A} :
    x ∈ borelSubgroup A ↔ (x : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := Iff.rfl

theorem borel_entry_one_zero (b : ↥(borelSubgroup A)) :
    ((b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := b.2

variable {A}

def borelDiagFst : ↥(borelSubgroup A) →* Aˣ where
  toFun b :=
    { val := ((b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0
      inv := (((b⁻¹ : ↥(borelSubgroup A)) : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0
      val_inv := by
        have hinv : (((b⁻¹ : ↥(borelSubgroup A)) : GL (Fin 2) A) :
            Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := (b⁻¹).2
        have h1 : (((b : GL (Fin 2) A) * ((b⁻¹ : ↥(borelSubgroup A)) : GL (Fin 2) A) :
            GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := by
          rw [← Subgroup.coe_mul, mul_inv_cancel]
          show ((1 : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0 = 1
          rw [Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply_eq]
        rwa [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hinv,
          mul_zero, add_zero] at h1
      inv_val := by
        have hb : ((b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := b.2
        have h1 : ((((b⁻¹ : ↥(borelSubgroup A)) : GL (Fin 2) A) * (b : GL (Fin 2) A) :
            GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := by
          rw [← Subgroup.coe_mul, inv_mul_cancel]
          show ((1 : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0 = 1
          rw [Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply_eq]
        rwa [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hb,
          mul_zero, add_zero] at h1 }
  map_one' := by
    apply Units.ext
    show ((1 : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0 = 1
    rw [Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply_eq]
  map_mul' b c := by
    apply Units.ext
    have hc : ((c : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := c.2
    show (((b * c : ↥(borelSubgroup A)) : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0
        = ((b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0
          * ((c : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0
    rw [Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two, hc, mul_zero, add_zero]

def borelDiagSnd : ↥(borelSubgroup A) →* Aˣ where
  toFun b :=
    { val := ((b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1
      inv := (((b⁻¹ : ↥(borelSubgroup A)) : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1
      val_inv := by
        have hb : ((b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := b.2
        have h1 : (((b : GL (Fin 2) A) * ((b⁻¹ : ↥(borelSubgroup A)) : GL (Fin 2) A) :
            GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := by
          rw [← Subgroup.coe_mul, mul_inv_cancel]
          show ((1 : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1 = 1
          rw [Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply_eq]
        rwa [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hb,
          zero_mul, zero_add] at h1
      inv_val := by
        have hinv : (((b⁻¹ : ↥(borelSubgroup A)) : GL (Fin 2) A) :
            Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := (b⁻¹).2
        have h1 : ((((b⁻¹ : ↥(borelSubgroup A)) : GL (Fin 2) A) * (b : GL (Fin 2) A) :
            GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := by
          rw [← Subgroup.coe_mul, inv_mul_cancel]
          show ((1 : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1 = 1
          rw [Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply_eq]
        rwa [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hinv,
          zero_mul, zero_add] at h1 }
  map_one' := by
    apply Units.ext
    show ((1 : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1 = 1
    rw [Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply_eq]
  map_mul' b c := by
    apply Units.ext
    have hb : ((b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := b.2
    show (((b * c : ↥(borelSubgroup A)) : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1
        = ((b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1
          * ((c : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1
    rw [Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two, hb, zero_mul, zero_add]

@[simp] theorem borelDiagFst_apply_val (b : ↥(borelSubgroup A)) :
    ((borelDiagFst b : Aˣ) : A) = ((b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0 := rfl

@[simp] theorem borelDiagSnd_apply_val (b : ↥(borelSubgroup A)) :
    ((borelDiagSnd b : Aˣ) : A) = ((b : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1 := rfl

theorem det_borel_eq_diag_mul {x : GL (Fin 2) A} (hx : x ∈ borelSubgroup A) :
    Matrix.GeneralLinearGroup.det x
      = borelDiagFst (⟨x, hx⟩ : ↥(borelSubgroup A))
        * borelDiagSnd (⟨x, hx⟩ : ↥(borelSubgroup A)) := by
  apply Units.ext
  have hb : (x : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := hx
  show (x : Matrix (Fin 2) (Fin 2) A).det
      = (x : Matrix (Fin 2) (Fin 2) A) 0 0 * (x : Matrix (Fin 2) (Fin 2) A) 1 1
  rw [Matrix.det_fin_two, hb, mul_zero, sub_zero]

theorem unipotentGL2_mem_borelSubgroup (x : A) : unipotentGL2 x ∈ borelSubgroup A := by
  show ((unipotentGL2 x : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0 = 0
  rw [unipotentGL2_coe]
  simp

theorem borelDiagFst_unipotentGL2 (x : A) :
    borelDiagFst ⟨unipotentGL2 x, unipotentGL2_mem_borelSubgroup x⟩ = 1 := by
  apply Units.ext
  show ((unipotentGL2 x : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0 = 1
  rw [unipotentGL2_coe]
  simp

theorem borelDiagSnd_unipotentGL2 (x : A) :
    borelDiagSnd ⟨unipotentGL2 x, unipotentGL2_mem_borelSubgroup x⟩ = 1 := by
  apply Units.ext
  show ((unipotentGL2 x : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1 = 1
  rw [unipotentGL2_coe]
  simp

end BorelCommRing

section AdelicBorel

open NumberField

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

abbrev adelicBorel : Subgroup (AdelicGL2 R K) := borelSubgroup (AdeleRing R K)

theorem globalPoints_apply (γ : Matrix.GeneralLinearGroup (Fin 2) K) (i j : Fin 2) :
    ((globalPoints R K γ : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) i j
      = algebraMap K (AdeleRing R K) ((γ : Matrix (Fin 2) (Fin 2) K) i j) := rfl

theorem globalPoints_mem_adelicBorel {γ : Matrix.GeneralLinearGroup (Fin 2) K}
    (hγ : γ ∈ borelSubgroup K) : globalPoints R K γ ∈ adelicBorel R K := by
  have hγ' : (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := hγ
  show ((globalPoints R K γ : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 1 0 = 0
  rw [globalPoints_apply, hγ', map_zero]

theorem borelDiagFst_globalPoints {γ : Matrix.GeneralLinearGroup (Fin 2) K}
    (hγ : γ ∈ borelSubgroup K) (hmem : globalPoints R K γ ∈ adelicBorel R K) :
    borelDiagFst (⟨globalPoints R K γ, hmem⟩ : ↥(adelicBorel R K))
      = Units.map (algebraMap K (AdeleRing R K)) (borelDiagFst (⟨γ, hγ⟩ : ↥(borelSubgroup K))) := by
  apply Units.ext
  show ((globalPoints R K γ : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 0 0
      = algebraMap K (AdeleRing R K) ((γ : Matrix (Fin 2) (Fin 2) K) 0 0)
  exact globalPoints_apply R K γ 0 0

theorem borelDiagSnd_globalPoints {γ : Matrix.GeneralLinearGroup (Fin 2) K}
    (hγ : γ ∈ borelSubgroup K) (hmem : globalPoints R K γ ∈ adelicBorel R K) :
    borelDiagSnd (⟨globalPoints R K γ, hmem⟩ : ↥(adelicBorel R K))
      = Units.map (algebraMap K (AdeleRing R K)) (borelDiagSnd (⟨γ, hγ⟩ : ↥(borelSubgroup K))) := by
  apply Units.ext
  show ((globalPoints R K γ : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 1 1
      = algebraMap K (AdeleRing R K) ((γ : Matrix (Fin 2) (Fin 2) K) 1 1)
  exact globalPoints_apply R K γ 1 1

theorem centralScalar_mem_adelicBorel (z : (AdeleRing R K)ˣ) :
    centralScalar R K z ∈ adelicBorel R K := by
  show ((centralScalar R K z : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 1 0 = 0
  have hval : ((centralScalar R K z : AdelicGL2 R K) :
      Matrix (Fin 2) (Fin 2) (AdeleRing R K)) = Matrix.scalar (Fin 2) (z : AdeleRing R K) := rfl
  rw [hval, Matrix.scalar_apply]
  exact Matrix.diagonal_apply_ne _ (by decide)

theorem borelDiagFst_centralScalar (z : (AdeleRing R K)ˣ)
    (hmem : centralScalar R K z ∈ adelicBorel R K) :
    borelDiagFst (⟨centralScalar R K z, hmem⟩ : ↥(adelicBorel R K)) = z := by
  apply Units.ext
  show ((centralScalar R K z : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 0 0
      = (z : AdeleRing R K)
  have hval : ((centralScalar R K z : AdelicGL2 R K) :
      Matrix (Fin 2) (Fin 2) (AdeleRing R K)) = Matrix.scalar (Fin 2) (z : AdeleRing R K) := rfl
  rw [hval, Matrix.scalar_apply, Matrix.diagonal_apply_eq]

theorem borelDiagSnd_centralScalar (z : (AdeleRing R K)ˣ)
    (hmem : centralScalar R K z ∈ adelicBorel R K) :
    borelDiagSnd (⟨centralScalar R K z, hmem⟩ : ↥(adelicBorel R K)) = z := by
  apply Units.ext
  show ((centralScalar R K z : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 1 1
      = (z : AdeleRing R K)
  have hval : ((centralScalar R K z : AdelicGL2 R K) :
      Matrix (Fin 2) (Fin 2) (AdeleRing R K)) = Matrix.scalar (Fin 2) (z : AdeleRing R K) := rfl
  rw [hval, Matrix.scalar_apply, Matrix.diagonal_apply_eq]

end AdelicBorel

end AutomorphicForm


