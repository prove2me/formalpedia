-- Prove2me | Definitions.Def_OAIQ031A017
-- name    : OAIQ031A017
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T12:56:58.442924+00:00
-- url     : https://prove2.me/theorems/3e6fcfdd-2742-4314-ba64-d19e4ca0694c
-- title:
--   Definitions bundle OAIQ031A017 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 45 declarations of OpenAI's Lean: 10 definitions, 1 inductive type or structure, 7 instances and 27 theorems. The definitions and types are `OAI.ArExplicit.ConeCokernel.Right`, `OAI.ArExplicit.ExternalTensor.tensorRestriction`, `OAI.ArExplicit.RawSyzygy`, `OAI.ArExplicit.TateKoszul.column`, `OAI.ArExplicit.Triangular`, `OAI.ArExplicit.Triangular.coordinateAddEquiv`, `OAI.ArExplicit.Triangular.coordinates`, `OAI.ArExplicit.Triangular.diagonal`, `OAI.ArExplicit.restrictPiEquiv`, `OAI.ArExplicit.splitCokernelSection`, `OAI.ArExplicit.splitKernelProjection`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Complete_TateKoszul`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/TateKoszul.lean), [`AuslanderReiten_Cones_ConeCokernel`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/ConeCokernel.lean), [`AuslanderReiten_Cones_ConeConnectingCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/ConeConnectingCoordinates.lean), [`AuslanderReiten_Homology_RestrictionProjective`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/RestrictionProjective.lean), [`AuslanderReiten_Modules_SplitModules`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/SplitModules.lean), [`AuslanderReiten_Resolutions_BinaryKoszul`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/BinaryKoszul.lean), [`AuslanderReiten_Resolutions_BinaryKoszulDual`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/BinaryKoszulDual.lean), [`AuslanderReiten_Tensor_ExternalTensorTransport`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorTransport.lean), [`AuslanderReiten_Triangular_Triangular`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/Triangular.lean), [`AuslanderReiten_Triangular_TriangularRadical`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/TriangularRadical.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A028`, `OAIQ031A037`, `OAIQ031A038`, `OAIQ031A039` and `OAIQ031A042`; the statement `OAI_ArExplicit_MainConclusions_scalarExtension`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_BinaryKoszul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.BinaryKoszul

universe u

variable (k : Type u) [CommRing k]

omit [CommRing k] in
@[simp]
theorem cons_succ_castSucc {n : ℕ} (a : k) (f : Fin (n + 1) → k) (i : Fin n) :
    (Fin.cons a f : Fin (n + 2) → k) i.succ.castSucc = f i.castSucc := by
  rw [Fin.castSucc_succ]
  rfl

end ArExplicit.BinaryKoszul

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_BinaryKoszulDual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.BinaryKoszul

universe u

variable (k : Type u) [Field k]

theorem exact_dual {U V W : Type u}
    [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W]
    (f : U →ₗ[k] V) (g : V →ₗ[k] W) (h : LinearMap.range f = LinearMap.ker g) :
    LinearMap.range g.dualMap = LinearMap.ker f.dualMap := by
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker,
    LinearMap.ker_dualMap_eq_dualAnnihilator_range, h]

end ArExplicit.BinaryKoszul

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_TateKoszul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.TateKoszul

universe u
variable {k : Type u} [Field k]
variable (H : ℤ → Type u) [∀ a, AddCommGroup (H a)] [∀ a, Module k (H a)]

variable {H}

variable {x y : ∀ a : ℤ, H a →ₗ[k] H (a + 3)}

def column (a : ℤ) : H a →ₗ[k] (H (a + 3) × H (a + 3)) :=
  (y a).prod (-(x a))

end ArExplicit.TateKoszul

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_ConeCokernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

variable {R M N E : Type*} [Ring R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [AddCommGroup E] [Module R E]

theorem projective_of_exact [Module.Projective R M] [Module.Projective R N]
    (i : M →ₗ[R] E) (p : E →ₗ[R] N) (hi : Function.Injective i)
    (hp : Function.Surjective p) (hex : Function.Exact i p) : Module.Projective R E := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p (LinearMap.id : N →ₗ[R] N) hp
  have hpi (m : M) : p (i m) = 0 := (hex (i m)).mpr ⟨m, rfl⟩
  have hps (n : N) : p (s n) = n := DFunLike.congr_fun hs n
  apply Module.Projective.of_equiv (LinearEquiv.ofBijective (i.coprod s) ?_)
  constructor
  · apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    rintro ⟨m,n⟩ h
    have hn : n = 0 := by
      have ht := congrArg p h
      simpa only [LinearMap.coprod_apply, map_add, hpi, hps, zero_add, map_zero] using ht
    subst n
    have hm : m = 0 := hi (by simpa using h)
    simp [hm]
  · intro e
    obtain ⟨m, hm⟩ := (hex (e - s (p e))).mp (by rw [map_sub, hps, sub_self])
    refine ⟨(m, p e), ?_⟩
    change i m + s (p e) = e
    rw [hm, sub_add_cancel]

namespace ConeCokernel

variable {Q₀ Q₁ P₀ P₁ P₂ : Type*}
variable [AddCommGroup Q₀] [Module R Q₀] [AddCommGroup Q₁] [Module R Q₁]
variable [AddCommGroup P₀] [Module R P₀] [AddCommGroup P₁] [Module R P₁]
variable [AddCommGroup P₂] [Module R P₂]
variable (dQ : Q₁ →ₗ[R] Q₀) (dP : P₁ →ₗ[R] P₀) (f : P₁ →ₗ[R] Q₀)

abbrev Right := P₀ ⧸ LinearMap.range dP

end ConeCokernel
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_SplitModules
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

universe u

variable {R M N : Type u} [Ring R] [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

def splitKernelProjection (f : M →ₗ[R] N) (s : N →ₗ[R] M) (hs : f.comp s = LinearMap.id) :
    M →ₗ[R] LinearMap.ker f :=
  (LinearMap.id - s.comp f).codRestrict _ (by
    intro x
    change f (x - s (f x)) = 0
    rw [map_sub, show f (s (f x)) = f x from DFunLike.congr_fun hs (f x)]
    exact sub_self _)

@[simp] theorem splitKernelProjection_subtype (f : M →ₗ[R] N) (s : N →ₗ[R] M)
    (hs : f.comp s = LinearMap.id) :
    (splitKernelProjection f s hs).comp (LinearMap.ker f).subtype = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp [splitKernelProjection, show f x.val = 0 from x.property]

theorem projective_kernel_of_surjective [Module.Projective R M] [Module.Projective R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) : Module.Projective R (LinearMap.ker f) := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f (LinearMap.id : N →ₗ[R] N) hf
  exact Module.Projective.of_split (LinearMap.ker f).subtype (splitKernelProjection f s hs)
    (splitKernelProjection_subtype f s hs)

theorem finite_kernel_of_surjective [Module.Finite R M] [Module.Projective R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) : Module.Finite R (LinearMap.ker f) := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f (LinearMap.id : N →ₗ[R] N) hf
  apply Module.Finite.of_surjective (splitKernelProjection f s hs)
  intro x
  exact ⟨x.val, DFunLike.congr_fun (splitKernelProjection_subtype f s hs) x⟩

def splitCokernelSection (i : M →ₗ[R] N) (r : N →ₗ[R] M) (hr : r.comp i = LinearMap.id) :
    (N ⧸ LinearMap.range i) →ₗ[R] N :=
  (LinearMap.range i).liftQ (LinearMap.id - i.comp r) (by
    rintro x ⟨m, rfl⟩
    change i m - i (r (i m)) = 0
    rw [show r (i m) = m from DFunLike.congr_fun hr m]
    exact sub_self _)

@[simp] theorem splitCokernelSection_mkQ (i : M →ₗ[R] N) (r : N →ₗ[R] M)
    (hr : r.comp i = LinearMap.id) :
    (LinearMap.range i).mkQ.comp (splitCokernelSection i r hr) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range i) x
  change (LinearMap.range i).mkQ (x - i (r x)) = (LinearMap.range i).mkQ x
  rw [map_sub]
  have hi : (LinearMap.range i).mkQ (i (r x)) = 0 :=
    DFunLike.congr_fun (LinearMap.range_mkQ_comp i) (r x)
  rw [hi, sub_zero]

theorem projective_cokernel_of_injective [Module.Injective R M] [Module.Projective R N]
    (i : M →ₗ[R] N) (hi : Function.Injective i) : Module.Projective R (N ⧸ LinearMap.range i) := by
  obtain ⟨r, hr⟩ := Module.Injective.extension_property R M M N i hi (LinearMap.id : M →ₗ[R] M)
  exact Module.Projective.of_split (splitCokernelSection i r hr) (LinearMap.range i).mkQ
    (splitCokernelSection_mkQ i r hr)

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_ConeConnectingCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex
universe u
variable {R : Type u} [Ring R]
variable (H : CochainComplex (ModuleCat.{u} R) ℤ)

abbrev RawSyzygy := H.X (-1) ⧸ LinearMap.range (H.d (-2) (-1)).hom

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_RestrictionProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory

universe u

variable {R S : Type u} [Ring R] [Ring S] (j : R →+* S)

instance finitePiProjective {P ι : Type*} [AddCommGroup P] [Module R P]
    [Module.Projective R P] [Fintype ι] : Module.Projective R (ι → P) :=
  Module.Projective.of_equiv (DFinsupp.linearEquivFunOnFintype :
    (Π₀ _ : ι, P) ≃ₗ[R] (ι → P))

def restrictPiEquiv (ι : Type) :
    ((ModuleCat.restrictScalars j).obj (ModuleCat.of S (ι → S))) ≃ₗ[R]
      (ι → ((ModuleCat.restrictScalars j).obj (ModuleCat.of S S))) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (M : ModuleCat.{u} S) [Module.Finite S M]

theorem restrict_finite [Module.Finite R ((ModuleCat.restrictScalars j).obj (ModuleCat.of S S))] :
    Module.Finite R ((ModuleCat.restrictScalars j).obj M) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' S M
  have : Module.Finite R ((ModuleCat.restrictScalars j).obj (ModuleCat.of S (Fin n → S))) :=
    Module.Finite.equiv (restrictPiEquiv j (Fin n)).symm
  exact Module.Finite.of_surjective
    (((ModuleCat.restrictScalars j).map (ModuleCat.ofHom p)).hom) hp

theorem restrict_projective [Module.Projective S M]
    [Module.Projective R ((ModuleCat.restrictScalars j).obj (ModuleCat.of S S))] :
    Module.Projective R ((ModuleCat.restrictScalars j).obj M) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' S M
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p (LinearMap.id : M →ₗ[S] M) hp
  have : Module.Projective R ((ModuleCat.restrictScalars j).obj (ModuleCat.of S (Fin n → S))) :=
    Module.Projective.of_equiv (restrictPiEquiv j (Fin n)).symm
  apply Module.Projective.of_split
    (((ModuleCat.restrictScalars j).map (ModuleCat.ofHom s)).hom)
    (((ModuleCat.restrictScalars j).map (ModuleCat.ofHom p)).hom)
  apply LinearMap.ext
  intro x
  exact DFunLike.congr_fun hs x

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorTransport
attribute [-instance] _root_.OAI.ArExplicit.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable (h : A ≃ₐ[k] A) (j : B ≃ₐ[k] B)

abbrev tensorRestriction : ModuleCat.{u} (A ⊗[k] B) ⥤ ModuleCat.{u} (A ⊗[k] B) :=
  ModuleCat.restrictScalars (Algebra.TensorProduct.map h.toAlgHom j.toAlgHom).toRingHom

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_Triangular
attribute [-instance] _root_.OAI.ArExplicit.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

@[ext] structure Triangular (R F : Type*) where
  top : R
  bottom : R
  off : F

namespace Triangular

variable {R F : Type*}

def coordinates : Triangular R F ≃ (R × R) × F where
  toFun x := ((x.top, x.bottom), x.off)
  invFun x := ⟨x.1.1, x.1.2, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instAddCommGroup [AddCommGroup R] [AddCommGroup F] : AddCommGroup (Triangular R F) :=
  coordinates.addCommGroup

def coordinateAddEquiv [AddCommGroup R] [AddCommGroup F] :
    Triangular R F ≃+ (R × R) × F where
  toEquiv := coordinates
  map_add' _ _ := rfl

variable [Ring R] [AddCommGroup F]
variable [Module R F] [Module Rᵐᵒᵖ F]

instance instOne : One (Triangular R F) := ⟨⟨1, 1, 0⟩⟩

instance instMul : Mul (Triangular R F) :=
  ⟨fun x y => ⟨x.top * y.top, x.bottom * y.bottom,
    x.bottom • y.off + MulOpposite.op y.top • x.off⟩⟩

section BasicCoordinates

omit [Module R F] [Module Rᵐᵒᵖ F]

@[simp] theorem top_zero : (0 : Triangular R F).top = 0 := rfl
@[simp] theorem bottom_zero : (0 : Triangular R F).bottom = 0 := rfl
@[simp] theorem off_zero : (0 : Triangular R F).off = 0 := rfl
@[simp] theorem top_one : (1 : Triangular R F).top = 1 := rfl
@[simp] theorem bottom_one : (1 : Triangular R F).bottom = 1 := rfl
@[simp] theorem off_one : (1 : Triangular R F).off = 0 := rfl
@[simp] theorem top_add (x y : Triangular R F) : (x + y).top = x.top + y.top := rfl
@[simp] theorem bottom_add (x y : Triangular R F) :
    (x + y).bottom = x.bottom + y.bottom := rfl
@[simp] theorem off_add (x y : Triangular R F) : (x + y).off = x.off + y.off := rfl
end BasicCoordinates

@[simp] theorem top_mul (x y : Triangular R F) : (x * y).top = x.top * y.top := rfl
@[simp] theorem bottom_mul (x y : Triangular R F) :
    (x * y).bottom = x.bottom * y.bottom := rfl
@[simp] theorem off_mul (x y : Triangular R F) :
    (x * y).off = x.bottom • y.off + MulOpposite.op y.top • x.off := rfl

variable [SMulCommClass R Rᵐᵒᵖ F]

instance instRing : Ring (Triangular R F) where
  __ := (inferInstance : AddCommGroup (Triangular R F))
  mul_assoc x y z := by
    ext
    · exact mul_assoc ..
    · exact mul_assoc ..
    · simp only [off_mul, bottom_mul, top_mul, mul_smul, smul_add, MulOpposite.op_mul]
      rw [← smul_comm x.bottom (MulOpposite.op z.top) y.off]
      exact (add_assoc ..).symm
  one_mul x := by ext <;> simp
  mul_one x := by ext <;> simp
  left_distrib x y z := by ext <;> simp [mul_add, smul_add, add_smul, add_add_add_comm]
  right_distrib x y z := by ext <;> simp [add_mul, smul_add, add_smul, add_add_add_comm]
  zero_mul x := by ext <;> simp
  mul_zero x := by ext <;> simp

def diagonal : Triangular R F →+* R × R where
  toFun x := (x.top, x.bottom)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem diagonal_surjective : Function.Surjective (diagonal (R := R) (F := F)) := by
  intro x
  exact ⟨⟨x.1, x.2, 0⟩, rfl⟩

section Scalars

variable (k : Type*) [CommRing k] [Algebra k R] [Module k F]

instance instModule : Module k (Triangular R F) := coordinateAddEquiv.module k

@[simp] theorem top_smul (c : k) (x : Triangular R F) : (c • x).top = c • x.top := rfl
@[simp] theorem bottom_smul (c : k) (x : Triangular R F) :
    (c • x).bottom = c • x.bottom := rfl
@[simp] theorem off_smul (c : k) (x : Triangular R F) : (c • x).off = c • x.off := rfl

variable [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass k Rᵐᵒᵖ F]

instance instAlgebra : Algebra k (Triangular R F) := Algebra.ofModule
  (by
    intro c x y
    ext
    · exact smul_mul_assoc c x.top y.top
    · exact smul_mul_assoc c x.bottom y.bottom
    · simp only [off_mul, off_smul, bottom_smul, smul_assoc, smul_add]
      rw [← smul_comm c (MulOpposite.op y.top) x.off])
  (by
    intro c x y
    ext
    · exact mul_smul_comm c x.top y.top
    · exact mul_smul_comm c x.bottom y.bottom
    · simp only [off_mul, off_smul, top_smul, MulOpposite.op_smul,
        smul_assoc, smul_add]
      rw [← smul_comm c x.bottom y.off])

end Scalars

end Triangular
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_TriangularRadical
attribute [-instance] _root_.OAI.ArExplicit.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.Triangular

variable {R F : Type*} [Ring R] [AddCommGroup F]
variable [Module R F] [Module Rᵐᵒᵖ F] [SMulCommClass R Rᵐᵒᵖ F]

theorem diagonal_kernel_square :
    (RingHom.ker (diagonal (R := R) (F := F))) ^ 2 = ⊥ := by
  apply le_antisymm _ bot_le
  rw [Submodule.pow_succ, Submodule.pow_one]
  apply Ideal.mul_le.mpr
  intro a ha b hb
  change (a.top, a.bottom) = (0, 0) at ha
  change (b.top, b.bottom) = (0, 0) at hb
  have ha₁ : a.top = 0 := congrArg Prod.fst ha
  have ha₂ : a.bottom = 0 := congrArg Prod.snd ha
  have hb₁ : b.top = 0 := congrArg Prod.fst hb
  have hb₂ : b.bottom = 0 := congrArg Prod.snd hb
  change a * b = 0
  ext <;> simp [ha₁, ha₂, hb₁, hb₂]

end ArExplicit.Triangular

end OAI
end


