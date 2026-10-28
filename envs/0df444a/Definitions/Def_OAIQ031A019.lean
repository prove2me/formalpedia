-- Prove2me | Definitions.Def_OAIQ031A019
-- name    : OAIQ031A019
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T12:57:17.543158+00:00
-- url     : https://prove2.me/theorems/d436dc23-1f62-4fb6-8fdb-3d5484e5368e
-- title:
--   Definitions bundle OAIQ031A019 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 18 declarations of OpenAI's Lean: 8 definitions, 1 inductive type or structure and 9 theorems. The definitions and types are `OAI.ArExplicit.FullHomEquivalence`, `OAI.ArExplicit.FullHomEquivalence.cocycle`, `OAI.ArExplicit.FullHomEquivalence.cohomology`, `OAI.ArExplicit.FullHomEquivalence.cohomologyMap`, `OAI.ArExplicit.GorensteinProjective`, `OAI.ArExplicit.GorensteinProjectiveAllTargets`, `OAI.ArExplicit.MainConclusions`, `OAI.ArExplicit.PositiveExtVanish`, `OAI.ArExplicit.transportProjectiveResolution`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_ModuleBarHomTwist`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarHomTwist.lean), [`AuslanderReiten_Basic`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Basic.lean), [`AuslanderReiten_Complete_CompleteResolutionAllProjectives`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteResolutionAllProjectives.lean), [`AuslanderReiten_Complete_CompleteResolutionTail`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteResolutionTail.lean), [`AuslanderReiten_Ext_ExtBridge`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExtBridge.lean), [`AuslanderReiten_HomComplex_FullHomTransport`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FullHomTransport.lean), [`AuslanderReiten_Resolutions_ResolutionCokernel`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/ResolutionCokernel.lean), [`AuslanderReiten_Resolutions_ResolutionCubicConjugate`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/ResolutionCubicConjugate.lean), [`AuslanderReiten_Resolutions_ResolutionExtSquare`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/ResolutionExtSquare.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A040` and `OAIQ031A043`; the statements `OAI.ArExplicit.GorensteinProjective.scalarExtension`, `OAI.ArExplicit.PositiveExtVanish.scalarExtension` and `OAI.ArExplicit.Statement.fullStatement_of_mainConclusions`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace ArExplicit

universe u v w

def GorensteinProjective (R : Type u) [Ring R]
    (M : Type v) [AddCommGroup M] [Module R M] : Prop :=
  ∃ P : ChainComplex (ModuleCat.{max u v} R) ℤ,
    (∀ n : ℤ, Module.Finite R (P.X n) ∧ Module.Projective R (P.X n)) ∧
    (∀ n : ℤ,
      LinearMap.range (P.d (n + 1) n).hom =
        LinearMap.ker (P.d n (n - 1)).hom) ∧
    (∀ (n : ℤ) (f : P.X n →ₗ[R] R),
      f.comp (P.d (n + 1) n).hom = 0 →
      ∃ g : P.X (n - 1) →ₗ[R] R, f = g.comp (P.d n (n - 1)).hom) ∧
    Nonempty (M ≃ₗ[R] (P.X 0 ⧸ LinearMap.range (P.d 1 0).hom))

def PositiveExtVanish (R : Type u) [Ring R]
    (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] : Prop :=
  ∀ n : ℕ, 0 < n →
    Subsingleton (CategoryTheory.Abelian.Ext (ModuleCat.of R M) (ModuleCat.of R N) n)

def MainConclusions (k : Type u) [Field k]
    (R : Type u) [Ring R] [Algebra k R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module k M]
    [IsScalarTower k R M] : Prop :=
  FiniteDimensional k R ∧
  FiniteDimensional k M ∧
  ¬ Module.Projective R M ∧
  GorensteinProjective R M ∧
  PositiveExtVanish R M M ∧
  PositiveExtVanish R M R ∧
  Nonempty ((R ⧸ Ring.jacobson R) ≃ₐ[k] (Fin 8 → k)) ∧
  (Ring.jacobson R) ^ 4 ≠ ⊥

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteResolutionTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit
universe u
variable {R : Type u} [Ring R]

def transportProjectiveResolution {X Y : ModuleCat.{u} R}
    (Q : ProjectiveResolution X) (e : X ≅ Y) : ProjectiveResolution Y where
  complex := Q.complex
  projective := Q.projective
  π := Q.π ≫ (ChainComplex.single₀ (ModuleCat.{u} R)).map e.hom

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExtBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory

namespace ArExplicit

universe u

variable (R : Type u) [Ring R]
  (M N : Type u) [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

theorem positiveExtVanish_iff_resolution
    (P : ProjectiveResolution (ModuleCat.of R M)) :
    PositiveExtVanish R M N ↔
      ∀ (n : ℕ) (f : P.complex.X (n + 1) ⟶ ModuleCat.of R N),
        P.complex.d (n + 2) (n + 1) ≫ f = 0 →
        ∃ g : P.complex.X n ⟶ ModuleCat.of R N,
          P.complex.d (n + 1) n ≫ g = f := by
  constructor
  · intro h n f hf
    have := h (n + 1) (Nat.zero_lt_succ n)
    exact (P.extMk_eq_zero_iff f (n + 2) rfl hf n rfl).mp
      (Subsingleton.elim _ _)
  · intro h n hn
    obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    have hz : ∀ a : CategoryTheory.Abelian.Ext
        (ModuleCat.of R M) (ModuleCat.of R N) (p + 1), a = 0 := by
      intro a
      obtain ⟨f, hf, rfl⟩ := P.extMk_surjective a (p + 2) rfl
      exact (P.extMk_eq_zero_iff f (p + 2) rfl hf p rfl).mpr (h p f hf)
    exact ⟨fun a b => (hz a).trans (hz b).symm⟩

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarHomTwist
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.ModuleBar
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
variable (h : R ≃ₐ[k] R) (e : M ≃ₗ[k] M)
variable (he : ∀ a m, e (a • m) = h a • e m)
include he

omit [IsScalarTower k R M] in
theorem inverse_transport_smul (a : R) (m : M) :
    e.symm (h a • m) = a • e.symm m := by
  apply e.injective
  rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteResolutionAllProjectives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
universe u v w x y
variable {R : Type u} [Ring R]
variable {K : Type v} [AddCommGroup K] [Module R K]
variable {L : Type w} [AddCommGroup L] [Module R L]
variable {M : Type x} [AddCommGroup M] [Module R M]
variable {Q : Type y} [AddCommGroup Q] [Module R Q]

def GorensteinProjectiveAllTargets (R : Type u) [Ring R]
    (M : Type v) [AddCommGroup M] [Module R M] : Prop :=
  ∃ P : ChainComplex (ModuleCat.{max u v} R) ℤ,
    (∀ n : ℤ, Module.Finite R (P.X n) ∧ Module.Projective R (P.X n)) ∧
    (∀ n : ℤ, LinearMap.range (P.d (n+1) n).hom = LinearMap.ker (P.d n (n-1)).hom) ∧
    (∀ (Q : Type y) [AddCommGroup Q] [Module R Q] [Module.Projective R Q]
      (n : ℤ) (f : P.X n →ₗ[R] Q), f.comp (P.d (n+1) n).hom = 0 →
        ∃ g : P.X (n-1) →ₗ[R] Q, f = g.comp (P.d n (n-1)).hom) ∧
    Nonempty (M ≃ₗ[R] (P.X 0 ⧸ LinearMap.range (P.d 1 0).hom))

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory CochainComplex.HomComplex

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]

structure FullHomEquivalence (K L : CochainComplex C ℤ) (K' L' : CochainComplex D ℤ) where
  cochain : ∀ n : ℤ, Cochain K L n ≃+ Cochain K' L' n
  differential : ∀ (n m : ℤ) (x : Cochain K L n), δ n m (cochain n x) = cochain m (δ n m x)

namespace FullHomEquivalence

variable {K L : CochainComplex C ℤ} {K' L' : CochainComplex D ℤ}
variable (e : FullHomEquivalence K L K' L') (n : ℤ)

def cocycle : Cocycle K L n →+ Cocycle K' L' n where
  toFun x := Cocycle.mk (e.cochain n x.1) (n+1) rfl (by
    rw [e.differential, Cocycle.δ_eq_zero, map_zero])
  map_zero' := by apply Cocycle.ext; exact (e.cochain n).map_zero
  map_add' x y := by apply Cocycle.ext; exact (e.cochain n).map_add x.1 y.1

theorem cocycle_bijective : Function.Bijective (e.cocycle n) := by
  constructor
  · intro x y h
    apply Cocycle.ext
    exact (e.cochain n).injective (congrArg Subtype.val h)
  · intro y
    let x := (e.cochain n).symm y.1
    have hx : δ n (n+1) x = 0 := by
      apply (e.cochain (n+1)).injective
      rw [← e.differential, map_zero]
      change δ n (n+1) (e.cochain n ((e.cochain n).symm y.1)) = 0
      rw [AddEquiv.apply_symm_apply, Cocycle.δ_eq_zero]
    refine ⟨Cocycle.mk x (n+1) rfl hx, ?_⟩
    apply Cocycle.ext
    exact (e.cochain n).apply_symm_apply y.1

theorem boundary_iff (x : Cocycle K L n) :
    e.cocycle n x ∈ coboundaries K' L' n ↔ x ∈ coboundaries K L n := by
  rw [mem_coboundaries_iff _ (n-1) (by omega), mem_coboundaries_iff _ (n-1) (by omega)]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨(e.cochain (n-1)).symm y, ?_⟩
    apply (e.cochain n).injective
    rw [← e.differential, AddEquiv.apply_symm_apply]
    exact hy
  · rintro ⟨y, hy⟩
    refine ⟨e.cochain (n-1) y, ?_⟩
    rw [e.differential, hy]
    rfl

def cohomologyMap : CohomologyClass K L n →+ CohomologyClass K' L' n :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom _ _ _).comp (e.cocycle n)) (by
      intro x hx
      exact (CohomologyClass.mk_eq_zero_iff _).mpr ((e.boundary_iff n x).mpr hx))

@[simp] theorem cohomologyMap_mk (x : Cocycle K L n) :
    e.cohomologyMap n (CohomologyClass.mk x) = CohomologyClass.mk (e.cocycle n x) := rfl

theorem cohomologyMap_bijective : Function.Bijective (e.cohomologyMap n) := by
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    obtain ⟨y, rfl⟩ := CohomologyClass.mk_surjective x
    exact (CohomologyClass.mk_eq_zero_iff y).mpr
      ((e.boundary_iff n y).mp ((CohomologyClass.mk_eq_zero_iff _).mp hx))
  · intro y
    obtain ⟨y, rfl⟩ := CohomologyClass.mk_surjective y
    obtain ⟨x, rfl⟩ := (e.cocycle_bijective n).2 y
    exact ⟨CohomologyClass.mk x, rfl⟩

def cohomology : CohomologyClass K L n ≃+ CohomologyClass K' L' n :=
  AddEquiv.ofBijective (e.cohomologyMap n) (e.cohomologyMap_bijective n)

end FullHomEquivalence
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_ResolutionCokernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [Ring R] {M : ModuleCat.{u} R}
variable (P : ProjectiveResolution M)

theorem resolution_range_eq_ker :
    LinearMap.range (P.complex.d 1 0).hom = LinearMap.ker (P.π.f 0).hom := by
  have h := P.exact₀
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at h
  exact h

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_ResolutionExtSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
namespace ArExplicit
universe u v
section General
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]
variable {X X' Y Y' : C} (P : ProjectiveResolution X) (Q : ProjectiveResolution X')

theorem resolutionExt_square (a : X ⟶ X') (b : Y ⟶ Y')
    (φ : ProjectiveResolution.Hom P Q a) (n : ℕ)
    (f : P.complex.X n ⟶ Y) (g : Q.complex.X n ⟶ Y')
    (hf : P.complex.d (n+1) n ≫ f = 0) (hg : Q.complex.d (n+1) n ≫ g = 0)
    (h : φ.hom.f n ≫ g = f ≫ b) :
    (Ext.mk₀ a).comp (Q.extMk g (n+1) rfl hg) (zero_add _) =
      (P.extMk f (n+1) rfl hf).comp (Ext.mk₀ b) (add_zero _) := by
  rw [ProjectiveResolution.mk₀_comp_extMk g (n+1) rfl hg φ,
    ProjectiveResolution.extMk_comp_mk₀]
  congr 1

end General

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_ResolutionCubicConjugate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
namespace ArExplicit
universe u

theorem cubicAugmentedSquare {C : Type*} [Category C]
    {P₃ P₀ Q₃ Q₀ B S N : C}
    (φ₃ : P₃ ⟶ Q₃) (φ₀ : P₀ ⟶ Q₀) (p : P₃ ⟶ P₀) (q : Q₃ ⟶ Q₀)
    (π : P₀ ⟶ B) (ρ : Q₀ ⟶ N) (e : B ⟶ S) (j : S ⟶ N) (f : P₃ ⟶ S)
    (hφ : φ₀ ≫ ρ = π ≫ (e ≫ j)) (hc : p ≫ φ₀ = φ₃ ≫ q)
    (hf : f = p ≫ π ≫ e) :
    φ₃ ≫ (q ≫ ρ) = f ≫ j := by
  rw [← Category.assoc, ← hc, Category.assoc, hφ, hf]
  simp only [Category.assoc]

end ArExplicit

end

end OAI
end


