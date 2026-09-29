-- Prove2me | Definitions.Def_Mathlib_RightActionInstances
-- name    : Mathlib_RightActionInstances
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/27119073-ee28-5768-a8dd-b41c9759d6d2
-- title:
--   Right-factor module, algebra and base-change structures on tensor products
-- statement:
--   For a commutative ring (or semiring) $R$, a commutative $R$-algebra $S$ and an $R$-module $M$, this module installs, as instances scoped to the namespace `TensorProduct.RightActions`, the $S$-module structure on $M \otimes_R S$ coming from the right-hand factor: the scalar action is defined by transporting the usual left action along Mathlib's commutation isomorphism $M \otimes_R S \cong S \otimes_R M$, so that $s \cdot (m \otimes t) = m \otimes (st)$, and `smul_def` records this description. For a (possibly non-commutative) $R$-algebra $B$ there is correspondingly an $S$-algebra structure on $B \otimes_R S$ whose structure map is `Algebra.TensorProduct.includeRight`, i.e. $s \mapsto 1 \otimes s$ (`algebraMap_eval`). With these conventions in force, `Algebra.TensorProduct.comm` is the $A$-algebra isomorphism $A \otimes_R B \cong B \otimes_R A$ (left action on the source, right action on the target) sending $a \otimes b$ to $b \otimes a$, and `Module.TensorProduct.comm` is the corresponding $A$-linear isomorphism $A \otimes_R M \cong M \otimes_R A$; the two `comm_apply_tmul`/`comm_symm_apply_tmul` lemmas evaluate them on pure tensors. Transported along these isomorphisms come instances: $M \otimes_R A$ is module-finite, resp. free, over $A$ when $M$ is so over $R$; the scalar tower $R \to A \to M \otimes_R A$; and, for $A$ a topological space and $M$ module-finite over $R$, the module topology on $M \otimes_R A$ together with the witness that this topology is the module topology, and (in the additive-group case) the fact that it makes $M \otimes_R A$ a topological additive group.
--
--   The remaining declarations are the right-handed forms of base change. `LinearMap.baseChange` sends an $R$-linear $\varphi : V \to W$ to the $A$-linear map $V \otimes_R A \to W \otimes_R A$ obtained by conjugating Mathlib's base change with the commutation isomorphisms; `baseChange_id` and `baseChange_comp` state that this is functorial (identity to identity, composition in diagrammatic order to composition). `LinearEquiv.baseChange` upgrades this to an $A$-linear isomorphism, with inverse the base change of $\varphi^{-1}$. `AlgebraMap.baseChange` sends an $R$-algebra map $\varphi : B \to C$ to the $A$-algebra map $B \otimes_R A \to C \otimes_R A$ underlying $\varphi \otimes \mathrm{id}_A$. Finally `Algebra.TensorProduct.basis` turns an $R$-basis of $M$ indexed by $\iota$ into an $A$-basis of $M \otimes_R A$ indexed by the same $\iota$.
--
--   **Relation to Mathlib.** Mathlib puts the module and algebra structure on a tensor product $A \otimes_R M$ on the left-hand factor; these are the mirror-image structures on the right-hand factor, obtained by transport along Mathlib's `TensorProduct.comm`, together with right-handed copies of `LinearMap.baseChange`, `Algebra.TensorProduct.basis` and the base change of algebra maps. They are deliberately declared as scoped instances, since global versions would give $A \otimes_R A$ two competing $A$-algebra structures.
--
--   **Where it is used.** These conventions are the ambient setting for the many base-change constructions in the development, where a finite module or algebra over a base ring is tensored with a coefficient or topological ring placed in the right-hand factor and the module topology is used on the result.
--
--   *Attribution:* this file contains material adapted from third-party Apache-2.0 sources (whole file (100%): `FLT/Hacks/RightActionInstances.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard, Pietro Monticone). See ATTRIBUTION.md and NOTICE in the source repository.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Mathlib_RightActionInstances.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

section

namespace TensorProduct.RightActions

noncomputable section semiring

variable (R S A B M : Type*) [CommSemiring R] [CommSemiring S] [AddCommMonoid M]
    [Algebra R S] [Module R M]
    [CommSemiring A] [Algebra R A]
    [Semiring B] [Algebra R B]

scoped instance : SMul S (M ⊗[R] S) where
  smul s e := TensorProduct.comm _ _ _ (s • (TensorProduct.comm _ _ _ e))

@[simp]
lemma smul_def (r : S) (m : M ⊗[R] S) :
    r • m = (TensorProduct.comm _ _ _).symm (r • (TensorProduct.comm _ _ _ m)) := rfl

scoped instance : Module S (M ⊗[R] S) where
  one_smul x := by simp_rw [smul_def, one_smul, (TensorProduct.comm R M S).symm_apply_apply]
  mul_smul a b x := by simp_rw [smul_def, mul_smul, (TensorProduct.comm R M S).apply_symm_apply]
  smul_zero := by simp
  smul_add := by simp
  add_smul := by simp [add_smul]
  zero_smul := by simp

scoped instance : Algebra S (B ⊗[R] S) where
  algebraMap := Algebra.TensorProduct.includeRight.toRingHom
  commutes' s bs := by
    induction bs with
    | zero => simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.includeRight_apply, mul_zero, zero_mul]
    | tmul x y =>
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
          mul_one, mul_comm]
    | add x y _ _ =>
        simp_all only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.includeRight_apply, mul_add, add_mul]
  smul_def' s bs := by
    induction bs with
    | zero => simp only [smul_zero, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.includeRight_apply, mul_zero]
    | tmul b s =>
        simp only [smul_def, TensorProduct.comm_tmul, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        rw [TensorProduct.smul_tmul']
        simp only [smul_eq_mul, TensorProduct.comm_symm_tmul]
    | add x y hx hy =>
        simp_all only [smul_def, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.includeRight_apply, smul_add, mul_add]

@[simp] lemma algebraMap_eval (s : S) : algebraMap S (B ⊗[R] S) s = 1 ⊗ₜ s := rfl

def Algebra.TensorProduct.comm : A ⊗[R] B ≃ₐ[A] B ⊗[R] A where
  __ := _root_.Algebra.TensorProduct.comm R A B
  commutes' _ := rfl

variable {A B} in
@[simp] lemma Algebra.TensorProduct.comm_apply_tmul (a : A) (b : B) :
    Algebra.TensorProduct.comm R A B (a ⊗ₜ b) = b ⊗ₜ a := by
  rfl

@[simp] lemma Algebra.TensorProduct.comm_symm_apply_tmul (b : B) (a : A) :
    (Algebra.TensorProduct.comm R A B).symm (b ⊗ₜ a) = a ⊗ₜ b := rfl

def Module.TensorProduct.comm : A ⊗[R] M ≃ₗ[A] M ⊗[R] A where
  __ := (_root_.TensorProduct.comm R A M).toAddEquiv
  map_smul' a am := by
    induction am with
    | zero => simp only [smul_zero, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
      map_zero, RingHom.id_apply]
    | tmul x y =>
        simp only [smul_tmul', smul_eq_mul, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
          LinearEquiv.coe_coe, comm_tmul, RingHom.id_apply, smul_def, comm_symm_tmul]
    | add x y hx hy =>
      simp_all only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
        RingHom.id_apply, smul_def, smul_add, map_add]

variable {A N} in
@[simp] lemma Module.TensorProduct.comm_apply_tmul (a : A) (m : M) :
    Module.TensorProduct.comm R A M (a ⊗ₜ m) = m ⊗ₜ a := rfl

@[simp] lemma Module.TensorProduct.comm_symm_apply_tmul (m : M) (a : A) :
    (Module.TensorProduct.comm R A M).symm (m ⊗ₜ a) = a ⊗ₜ m := rfl

scoped instance [Module.Finite R M] : Module.Finite A (M ⊗[R] A) :=
  Module.Finite.equiv (Module.TensorProduct.comm R A M)

scoped instance [Module.Free R M] : Module.Free A (M ⊗[R] A) :=
  Module.Free.of_equiv (Module.TensorProduct.comm R A M)

scoped instance : IsScalarTower R A (M ⊗[R] A) where
  smul_assoc r a ma := by simp

@[nolint unusedArguments]

scoped instance [TopologicalSpace A] [Module.Finite R M] :
    TopologicalSpace (M ⊗[R] A) :=
  moduleTopology A (M ⊗[R] A)

scoped instance [TopologicalSpace A] [Module.Finite R M] :
  IsModuleTopology A (M ⊗[R] A) := ⟨rfl⟩

noncomputable abbrev LinearMap.baseChange (R : Type*) [CommRing R]
    (V W : Type*) [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (A : Type*) [CommRing A] [Algebra R A]
    (φ : V →ₗ[R] W) : V ⊗[R] A →ₗ[A] W ⊗[R] A :=
  (Module.TensorProduct.comm R A W) ∘ₗ
    (_root_.LinearMap.baseChange A φ) ∘ₗ
    (Module.TensorProduct.comm R A V).symm

@[simp]
lemma LinearMap.baseChange_id (R : Type*) [CommRing R]
    (V : Type*) [AddCommGroup V] [Module R V]
    (A : Type*) [CommRing A] [Algebra R A] :
    LinearMap.baseChange R V V A .id = .id := by
  ext
  simp

theorem LinearMap.baseChange_comp (R : Type*) [CommRing R]
    (U V W : Type*) [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] (A : Type*) [CommRing A] [Algebra R A]
    (φ : U →ₗ[R] V) (ψ : V →ₗ[R] W) :
    LinearMap.baseChange R V W A ψ ∘ₗ LinearMap.baseChange R U V A φ =
    LinearMap.baseChange R U W A (ψ ∘ₗ φ) := by
  ext
  simp [_root_.LinearMap.baseChange_comp]

example (X Y) (f : X → Y) (g : Y → X) : Function.LeftInverse f g ↔ f ∘ g = id := by
  exact Function.leftInverse_iff_comp

noncomputable abbrev LinearEquiv.baseChange (R : Type*) [CommRing R]
    (V W : Type*) [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (A : Type*) [CommRing A] [Algebra R A]
    (φ : V ≃ₗ[R] W) : V ⊗[R] A ≃ₗ[A] W ⊗[R] A where
  __ := LinearMap.baseChange _ _ _ _ φ.toLinearMap
  invFun := LinearMap.baseChange _ _ _ _ φ.symm.toLinearMap
  left_inv := by
    intro x
    calc
    _ = (LinearMap.baseChange R W V A φ.symm ∘ₗ LinearMap.baseChange R V W A φ) x := rfl
    _ = _ := by simp [LinearMap.baseChange_comp]
  right_inv := by
    intro y
    change ((LinearMap.baseChange R V W A φ) ∘ₗ (LinearMap.baseChange R W V A φ.symm)) y = _
    simp [LinearMap.baseChange_comp]

noncomputable def AlgebraMap.baseChange (R : Type*) [CommRing R]
    (B C : Type*) [Ring B] [Algebra R B] [Ring C] [Algebra R C]
    (A : Type*) [CommRing A] [Algebra R A]
    (φ : B →ₐ[R] C) : B ⊗[R] A →ₐ[A] C ⊗[R] A where
  __ := Algebra.TensorProduct.map φ (.id R A)
  commutes' a := by simp

def Algebra.TensorProduct.basis {R : Type*} (A : Type*) {M : Type*} {ι : Type*}
    [CommSemiring R] [CommSemiring A] [Algebra R A] [AddCommMonoid M] [Module R M]
    (b : Module.Basis ι R M) :
    Module.Basis ι A (M ⊗[R] A) :=
  (_root_.Algebra.TensorProduct.basis A b).map (Module.TensorProduct.comm R A M)

end semiring

noncomputable section ring

variable (R A B M : Type*) [CommRing R]
    [CommRing A] [Algebra R A]
    [Ring B] [Algebra R B]
    [AddCommGroup M] [Module R M]

scoped instance [TopologicalSpace A] [Module.Finite R M] :
    IsTopologicalAddGroup (M ⊗[R] A) := IsModuleTopology.topologicalAddGroup A (M ⊗[R] A)

end ring

end TensorProduct.RightActions


