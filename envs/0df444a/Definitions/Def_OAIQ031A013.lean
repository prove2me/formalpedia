-- Prove2me | Definitions.Def_OAIQ031A013
-- name    : OAIQ031A013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T13:00:35.018228+00:00
-- url     : https://prove2.me/theorems/cc4476c5-4000-4f0d-83f3-a5940d639b31
-- title:
--   Definitions bundle OAIQ031A013 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 22 declarations of OpenAI's Lean: 7 definitions, 1 inductive type or structure and 14 theorems. The definitions and types are `OAI.ArExplicit.CompleteComparison.functorComplex`, `OAI.ArExplicit.FiniteProjectivePresentation`, `OAI.ArExplicit.FiniteProjectivePresentation.choose`, `OAI.ArExplicit.LinearHomology.cycleEquiv`, `OAI.ArExplicit.ResolutionProducts.resolutionEndpointMap`, `OAI.ArExplicit.fullHomPostcomp`, `OAI.ArExplicit.fullHomPostcompCocycle`, `OAI.ArExplicit.linearRetractEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Algebras_BaseRadical`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/BaseRadical.lean), [`AuslanderReiten_Algebras_Radical`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/Radical.lean), [`AuslanderReiten_Bar_NativeBarFreeEndpoint`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/NativeBarFreeEndpoint.lean), [`AuslanderReiten_Complete_CompleteTailFunctor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteTailFunctor.lean), [`AuslanderReiten_Duality_ProjectiveTraceDuality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Duality/ProjectiveTraceDuality.lean), [`AuslanderReiten_Duality_SymmetricStableDuality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Duality/SymmetricStableDuality.lean), [`AuslanderReiten_HomComplex_FullHomComposition`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FullHomComposition.lean), [`AuslanderReiten_HomComplex_FullHomNaturality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FullHomNaturality.lean), [`AuslanderReiten_Homology_LinearHomologyCongr`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/LinearHomologyCongr.lean), [`AuslanderReiten_Homology_LinearRetractEquiv`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/LinearRetractEquiv.lean), [`AuslanderReiten_Resolutions_ResolutionEndpointIso`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/ResolutionEndpointIso.lean), [`AuslanderReiten_Stable_TargetStableCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Stable/TargetStableCoordinates.lean).
--
--   **Imports.** It imports the bundle `OAIQ031A000` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A035`, `OAIQ031A036`, `OAIQ031A039`, `OAIQ031A041` and `OAIQ031A042`; the statement `OAI_ArExplicit_MainConclusions_scalarExtension`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A000

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_Radical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

variable {R S : Type*} [Ring R] [Ring S]

theorem mem_jacobson_prod_iff (x : R × S) :
    x ∈ Ring.jacobson (R × S) ↔ x.1 ∈ Ring.jacobson R ∧ x.2 ∈ Ring.jacobson S := by
  constructor
  · intro hx
    have : RingHomSurjective (RingHom.fst R S) := ⟨fun r => ⟨(r, 0), rfl⟩⟩
    have : RingHomSurjective (RingHom.snd R S) := ⟨fun s => ⟨(0, s), rfl⟩⟩
    exact ⟨Ring.le_comap_jacobson (RingHom.fst R S) hx,
      Ring.le_comap_jacobson (RingHom.snd R S) hx⟩
  · rintro ⟨hr, hs⟩
    rw [← Ideal.jacobson_bot] at hr hs ⊢
    apply Ideal.mem_jacobson_iff.mpr
    intro y
    obtain ⟨r, hr⟩ := Ideal.mem_jacobson_iff.mp hr y.1
    obtain ⟨s, hs⟩ := Ideal.mem_jacobson_iff.mp hs y.2
    exact ⟨(r, s), Prod.ext hr hs⟩

theorem jacobson_prod_eq_bot (hR : Ring.jacobson R = ⊥) (hS : Ring.jacobson S = ⊥) :
    Ring.jacobson (R × S) = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨hr, hs⟩ := (mem_jacobson_prod_iff x).mp hx
  rw [hR] at hr
  rw [hS] at hs
  exact Prod.ext hr hs

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_BaseRadical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.BaseAlgebra

open ArExplicit.Letter

variable {k : Type*} [Field k] (q : k)

theorem fifth_power_eq_zero (a : BaseAlgebra k q) (he : a.coeff e = 0)
    (hf : a.coeff f = 0) : a ^ 5 = 0 := by
  ext i
  cases i <;> simp [pow_succ, product, he, hf]

theorem field_jacobson : Ring.jacobson k = ⊥ := by
  let : (⊥ : Ideal k).IsMaximal := Ideal.bot_isMaximal
  exact le_antisymm (Ring.jacobson_le_of_isMaximal ⊥) bot_le

end ArExplicit.BaseAlgebra

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_NativeBarFreeEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.BarBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

theorem compValues {R : Type*} [Ring R] {X Y Z : ModuleCat R}
    (f : X ⟶ Y) (g : Y ⟶ Z) {x : X} {y : Y} {z : Z}
    (hf : f x = y) (hg : g y = z) : (f ≫ g) x = z := by
  rw [ModuleCat.comp_apply, hf, hg]

end ArExplicit.BarBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteTailFunctor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.CompleteComparison
universe u
variable {R S : Type u} [Ring R] [Ring S]
variable (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive]

omit [F.Additive] in
theorem functor_iso_square {A₀ A₁ B₀ B₁ : ModuleCat.{u} R}
    {U V : ModuleCat.{u} S} (a : A₀ ≅ A₁) (b : B₀ ≅ B₁)
    (e : U ≅ F.obj A₁) (f : V ≅ F.obj B₁) (d : A₁ ⟶ B₁) :
    (e.hom ≫ F.map a.inv) ≫ F.map (a.hom ≫ d ≫ b.inv) =
      (e.hom ≫ F.map d ≫ f.inv) ≫ f.hom ≫ F.map b.inv := by
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← F.map_comp_assoc, a.inv_hom_id, F.map_id, Category.id_comp]

variable (K : CochainComplex (ModuleCat.{u} R) ℤ)
abbrev functorComplex := (F.mapHomologicalComplex (.up ℤ)).obj K

end ArExplicit.CompleteComparison

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Duality_SymmetricStableDuality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.FrobeniusTrace

universe u

variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable {M N : Type u} [AddCommGroup M] [Module R M] [Module k M]
variable [IsScalarTower k R M] [AddCommGroup N] [Module R N] [Module k N]
variable [IsScalarTower k R N]

variable [SMulCommClass R k M]

theorem free_map_apply (r : ℕ) (f : (Fin r → R) →ₗ[R] M) (v : Fin r → R) :
    f v = ∑ i : Fin r, v i • f (Pi.single i 1) := by
  have hv : v = ∑ i : Fin r, v i • Pi.single i (1 : R) := by
    ext j
    simp [Pi.single_apply]
  calc
    f v = f (∑ i : Fin r, v i • Pi.single i (1 : R)) := congrArg f hv
    _ = _ := by simp

end ArExplicit.FrobeniusTrace

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_LinearHomologyCongr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.LinearHomology

universe u

variable {k : Type u} [Field k]
variable {U V W U' V' W' : Type u}
variable [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
variable [AddCommGroup W] [Module k W] [AddCommGroup U'] [Module k U']
variable [AddCommGroup V'] [Module k V'] [AddCommGroup W'] [Module k W']
variable (f : U →ₗ[k] V) (g : V →ₗ[k] W) (h : g.comp f = 0)
variable (f' : U' →ₗ[k] V') (g' : V' →ₗ[k] W') (h' : g'.comp f' = 0)
variable (a : U ≃ₗ[k] U') (b : V ≃ₗ[k] V') (c : W ≃ₗ[k] W')
variable (hf : ∀ x, b (f x) = f' (a x)) (hg : ∀ x, c (g x) = g' (b x))

def cycleEquiv : LinearMap.ker g ≃ₗ[k] LinearMap.ker g' where
  toFun x := ⟨b x.val, by
    change g' (b x.val) = 0
    rw [← hg, x.property, map_zero]⟩
  invFun y := ⟨b.symm y.val, by
    apply c.injective
    rw [hg, b.apply_symm_apply, y.property, map_zero]⟩
  left_inv x := Subtype.ext (b.symm_apply_apply x.val)
  right_inv y := Subtype.ext (b.apply_symm_apply y.val)
  map_add' x y := Subtype.ext (b.map_add x.val y.val)
  map_smul' r x := Subtype.ext (b.map_smul r x.val)

end ArExplicit.LinearHomology

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_LinearRetractEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

universe u

variable {k A B C D : Type u} [Semiring k]
variable [AddCommMonoid A] [Module k A] [AddCommMonoid B] [Module k B]
variable [AddCommMonoid C] [Module k C] [AddCommMonoid D] [Module k D]

def linearRetractEquiv (i : A →ₗ[k] B) (p : B →ₗ[k] A) (hpi : p.comp i = LinearMap.id)
    (j : C →ₗ[k] D) (q : D →ₗ[k] C) (hqj : q.comp j = LinearMap.id)
    (e : B ≃ₗ[k] D) (he : ∀ b, e (i (p b)) = j (q (e b))) : A ≃ₗ[k] C where
  toFun a := q (e (i a))
  invFun c := p (e.symm (j c))
  left_inv a := by
    change p (e.symm (j (q (e (i a))))) = a
    rw [← he, e.symm_apply_apply]
    exact (DFunLike.congr_fun hpi _).trans (DFunLike.congr_fun hpi a)
  right_inv c := by
    change q (e (i (p (e.symm (j c))))) = c
    rw [he, e.apply_symm_apply]
    exact (DFunLike.congr_fun hqj _).trans (DFunLike.congr_fun hqj c)
  map_add' a b := by simp
  map_smul' r a := by simp

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Duality_ProjectiveTraceDuality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

universe u

variable (R P : Type u) [Ring R] [AddCommGroup P] [Module R P]

structure FiniteProjectivePresentation where
  rank : ℕ
  inclusion : P →ₗ[R] (Fin rank → R)
  projection : (Fin rank → R) →ₗ[R] P
  split : projection.comp inclusion = LinearMap.id

namespace FiniteProjectivePresentation

noncomputable def choose [Module.Finite R P] [Module.Projective R P] :
    FiniteProjectivePresentation R P := by
  let h := Module.Finite.exists_fin' R P
  let hs := Module.projective_lifting_property h.choose_spec.choose
    (LinearMap.id : P →ₗ[R] P) h.choose_spec.choose_spec
  exact ⟨h.choose, hs.choose, h.choose_spec.choose, hs.choose_spec⟩

variable {R P}

@[simp]
theorem split_apply (F : FiniteProjectivePresentation R P) (x : P) :
    F.projection (F.inclusion x) = x := DFunLike.congr_fun F.split x

end FiniteProjectivePresentation

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory
open CochainComplex CochainComplex.HomComplex

variable {C : Type*} [Category* C] [Preadditive C]
variable {F G K : CochainComplex C ℤ} (φ : F ⟶ G) (n : ℤ)

def fullHomPostcompCocycle : Cocycle K F n →+ Cocycle K G n where
  toFun x := x.postcomp φ
  map_zero' := by apply Cocycle.ext; simp
  map_add' x y := by apply Cocycle.ext; simp

def fullHomPostcomp : CohomologyClass K F n →+ CohomologyClass K G n :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom _ _ _).comp (fullHomPostcompCocycle φ n)) (by
      intro x hx
      apply (CohomologyClass.mk_eq_zero_iff _).mpr
      obtain ⟨m, hm, y, hy⟩ := hx
      refine ⟨m, hm, y.comp (Cochain.ofHom φ) (add_zero m), ?_⟩
      simpa [fullHomPostcompCocycle] using congrArg (fun z => z.comp (Cochain.ofHom φ) (add_zero n)) hy)

@[simp] theorem fullHomPostcomp_mk (x : Cocycle K F n) :
    fullHomPostcomp φ n (CohomologyClass.mk x) = CohomologyClass.mk (x.postcomp φ) := rfl

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomNaturality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CochainComplex CochainComplex.HomComplex
namespace ArExplicit
variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
variable {Φ Ψ : C ⥤ D} [Φ.Additive] [Ψ.Additive]
variable {K L : CochainComplex C ℤ} {n : ℤ}

variable {F G H I : CochainComplex C ℤ}

theorem fullHomPostcomp_comp (f : F ⟶ G) (g : G ⟶ H) (x : CohomologyClass I F n) :
    fullHomPostcomp g n (fullHomPostcomp f n x) = fullHomPostcomp (f ≫ g) n x := by
  obtain ⟨x,rfl⟩ := CohomologyClass.mk_surjective x
  simp only [fullHomPostcomp_mk]
  congr 1
  apply Cocycle.ext
  apply Cochain.ext
  intro i j hij
  change ((x.val.comp (Cochain.ofHom f) (add_zero n)).comp (Cochain.ofHom g)
      (add_zero n)).v i j hij = (x.val.comp (Cochain.ofHom (f ≫ g)) (add_zero n)).v i j hij
  rw [Cochain.comp_v _ _ (add_zero n) i j j hij (add_zero j),
    Cochain.comp_v _ _ (add_zero n) i j j hij (add_zero j),
    Cochain.comp_v _ _ (add_zero n) i j j hij (add_zero j)]
  simp only [Cochain.ofHom_v, HomologicalComplex.comp_f, Category.assoc]

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_ResolutionEndpointIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace ArExplicit.ResolutionProducts
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {X Y Z : C}
variable (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)

omit [Abelian C] in
theorem compose_square {A B D X Y Z : C}
    (p : A ⟶ X) (q : B ⟶ Y) (r : D ⟶ Z)
    (f : A ⟶ B) (g : B ⟶ D) (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z)
    (hp : p ≫ a = f ≫ q) (hq : q ≫ b = g ≫ r) (hc : p ≫ c = (f ≫ g) ≫ r) :
    p ≫ c = p ≫ a ≫ b := by
  calc
    p ≫ c = (f ≫ g) ≫ r := hc
    _ = f ≫ g ≫ r := Category.assoc _ _ _
    _ = f ≫ q ≫ b := congrArg (fun z => f ≫ z) hq.symm
    _ = (f ≫ q) ≫ b := (Category.assoc _ _ _).symm
    _ = (p ≫ a) ≫ b := congrArg (fun z => z ≫ b) hp.symm
    _ = p ≫ a ≫ b := Category.assoc _ _ _

def resolutionEndpointMap (f : P.complex ⟶ Q.complex) : X ⟶ Y :=
  P.isColimitCokernelCofork.desc (CokernelCofork.ofπ (f.f 0 ≫ Q.π.f 0) (by
    rw [← Category.assoc, ← f.comm 1 0, Category.assoc,
      Q.complex_d_comp_π_f_zero, comp_zero]))

@[reassoc] theorem resolutionEndpointMap_augmentation (f : P.complex ⟶ Q.complex) :
    P.π.f 0 ≫ resolutionEndpointMap P Q f = f.f 0 ≫ Q.π.f 0 :=
  Cofork.IsColimit.π_desc P.isColimitCokernelCofork

theorem resolutionEndpointMap_id : resolutionEndpointMap P P (𝟙 _) = 𝟙 X := by
  apply (cancel_epi (P.π.f 0)).1
  erw [resolutionEndpointMap_augmentation]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

end ArExplicit.ResolutionProducts

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Stable_TargetStableCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.CompleteComparison
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ} {n : ℤ}

@[reassoc] theorem component_transport (x : Cochain K L n)
    (p q r : ℤ) (hpq : p + n = q) (hqr : q = r) :
    x.v p q hpq ≫ (L.XIsoOfEq hqr).hom = x.v p r (hpq.trans hqr) := by
  subst r
  simp

end ArExplicit.CompleteComparison

end

end OAI
end


