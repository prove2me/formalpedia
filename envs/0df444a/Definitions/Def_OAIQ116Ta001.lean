-- Prove2me | Definitions.Def_OAIQ116Ta001
-- name    : OAIQ116Ta001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T01:33:27.436822+00:00
-- url     : https://prove2.me/theorems/4d307977-078b-45db-9e2a-8881c29d2c1c
-- title:
--   Definitions bundle OAIQ116Ta001 of the split of OpenAI, A counterexample to Tachikawa's second conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Tachikawa.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Tachikawa's second conjecture*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 311 declarations of OpenAI's Lean: 120 definitions, 3 inductive types or structures, 34 instances and 154 theorems. The definitions and types are `OAI.Tachikawa.B`, `OAI.Tachikawa.BalancedTensor.oppositeFree`, `OAI.Tachikawa.C`, `OAI.Tachikawa.C.Ce`, `OAI.Tachikawa.C.Cf`, `OAI.Tachikawa.C.Simple`, `OAI.Tachikawa.C.augmentation`, `OAI.Tachikawa.C.basis`, `OAI.Tachikawa.C.ce`, `OAI.Tachikawa.C.cf`, `OAI.Tachikawa.C.character`, `OAI.Tachikawa.C.e`, `OAI.Tachikawa.C.eC`, `OAI.Tachikawa.C.ec`, `OAI.Tachikawa.C.ell`, `OAI.Tachikawa.C.f`, `OAI.Tachikawa.C.fC`, `OAI.Tachikawa.C.fc`, `OAI.Tachikawa.C.lambdaEll`, `OAI.Tachikawa.C.lambdaU`, `OAI.Tachikawa.C.mul`, `OAI.Tachikawa.C.resD`, `OAI.Tachikawa.C.resObj`, `OAI.Tachikawa.C.rhoEll`, `OAI.Tachikawa.C.rhoU`, `OAI.Tachikawa.C.u`, `OAI.Tachikawa.C.unit`, `OAI.Tachikawa.C.v`, `OAI.Tachikawa.C.vHom`, `OAI.Tachikawa.CokerAt`, `OAI.Tachikawa.CokerAt.augmentationEquiv`, `OAI.Tachikawa.CokerAt.descend`, `OAI.Tachikawa.CokerAt.factorThrough`, `OAI.Tachikawa.CokerAt.map`, `OAI.Tachikawa.CokerAt.δ`, `OAI.Tachikawa.CokerAt.ι`, `OAI.Tachikawa.CokerAt.π`, `OAI.Tachikawa.ComparisonStep`, `OAI.Tachikawa.CompleteCone.complex`, `OAI.Tachikawa.CompleteCone.inLeft` and 83 more.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory, in whole or in part: `Tachikawa_Bimodule`, `Tachikawa_CompleteResolution`, `Tachikawa_CompleteTensor`, `Tachikawa_Cone`, `Tachikawa_Coresolution`, `Tachikawa_Corner`, `Tachikawa_DownHom`, `Tachikawa_Nakayama`, `Tachikawa_OuterExt`, `Tachikawa_OuterTensor`, `Tachikawa_Perfect`, `Tachikawa_Period`, `Tachikawa_ReverseResolution`, `Tachikawa_RightInduction`, `Tachikawa_Socle`, `Tachikawa_StableDuality`, `Tachikawa_StableShift`, `Tachikawa_Tensor`, `Tachikawa_TwistHom`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ116Ta003`, `OAIQ116Ta004` and `OAIQ116Ta005`.
-- source:
--   OpenAI, A counterexample to Tachikawa's second conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Tachikawas-second-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ116_Tach.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_StableDuality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
variable {R M P : Type} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommGroup P] [Module R P]

lemma injective_of_retract [Module.Injective R P]
    (i : M →ₗ[R] P) (s : P →ₗ[R] M) (hs : s.comp i = LinearMap.id) :
    Module.Injective R M := by
  constructor
  intro X Y _ _ _ _ f hf g
  obtain ⟨h, hh⟩ := Module.Injective.extension_property R P X Y f hf (i.comp g)
  refine ⟨s.comp h, ?_⟩
  intro x
  change s (h (f x)) = g x
  have hhx : h (f x) = i (g x) := LinearMap.congr_fun hh x
  rw [hhx]
  exact LinearMap.congr_fun hs (g x)

lemma injective_of_finite_projective [Module.Injective R R]
    [Module.Finite R M] [Module.Projective R M] : Module.Injective R M := by
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  exact injective_of_retract g f hfg

end Tachikawa



namespace Tachikawa
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {M N P : Type} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module R M] [Module R N] [Module R P]
  [Module k M] [Module k N] [Module k P]
  [IsScalarTower k R M] [IsScalarTower k R N] [IsScalarTower k R P]

def homPrecompose (i : M →ₗ[R] P) : (P →ₗ[R] N) →ₗ[k] (M →ₗ[R] N) where
  toFun f := f.comp i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Tachikawa



namespace Tachikawa
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {M : Type} [AddCommGroup M] [Module R M]

structure FiniteFreeCover (R M : Type) [Ring R] [AddCommGroup M] [Module R M] where
  rank : ℕ
  map : (Fin rank → R) →ₗ[R] M
  surjective : Function.Surjective map

def finiteFreeCover [Module.Finite R M] : FiniteFreeCover R M :=
  let data := Module.Finite.exists_fin' R M
  ⟨data.choose, data.choose_spec.choose, data.choose_spec.choose_spec⟩

end Tachikawa



namespace Tachikawa
open CategoryTheory

theorem ext_subsingleton_of_boundaries {C : Type*} [Category C] [Abelian C] [HasExt C]
    {X Y : C} (P : ProjectiveResolution X) (n : ℕ)
    (h : ∀ f : P.complex.X (n+1) ⟶ Y,
      P.complex.d (n+2) (n+1) ≫ f = 0 →
      ∃ g : P.complex.X n ⟶ Y, P.complex.d (n+1) n ≫ g = f) :
    Subsingleton (Abelian.Ext X Y (n+1)) := by
  have hzero (α : Abelian.Ext X Y (n+1)) : α = 0 := by
    obtain ⟨f, hf, rfl⟩ := P.extMk_surjective α (n+2) rfl
    exact (P.extMk_eq_zero_iff f (n+2) rfl hf n rfl).mpr (h f hf)
  exact ⟨fun α β => (hzero α).trans (hzero β).symm⟩

end Tachikawa

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_CompleteResolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {R : Type} [Ring R]

def CokerAt (P : ChainComplex (ModuleCat R) ℤ) (j : ℤ) :=
  P.X j ⧸ LinearMap.range (P.d (j+1) j).hom

namespace CokerAt
variable (P : ChainComplex (ModuleCat R) ℤ) (j : ℤ)
instance instAddCommGroup : AddCommGroup (CokerAt P j) :=
  inferInstanceAs (AddCommGroup (P.X j ⧸ LinearMap.range (P.d (j+1) j).hom))
instance instModule : Module R (CokerAt P j) :=
  inferInstanceAs (Module R (P.X j ⧸ LinearMap.range (P.d (j+1) j).hom))

def π : P.X j →ₗ[R] CokerAt P j := (LinearMap.range (P.d (j+1) j).hom).mkQ

lemma π_surjective : Function.Surjective (π P j) := Submodule.mkQ_surjective _

lemma π_d : (π P j).comp (P.d (j+1) j).hom = 0 := by
  apply LinearMap.ext
  intro x
  exact Submodule.Quotient.mk_eq_zero _ |>.mpr ⟨x, rfl⟩

def ι : CokerAt P j →ₗ[R] P.X (j-1) :=
  (LinearMap.range (P.d (j+1) j).hom).liftQ (P.d j (j-1)).hom (by
    rintro x ⟨y, rfl⟩
    have h := P.d_comp_d (j+1) j (j-1)
    exact LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp h) y)

@[simp] lemma ι_π (x : P.X j) : ι P j (π P j x) = P.d j (j-1) x := rfl

lemma ι_comp_π : (ι P j).comp (π P j) = (P.d j (j-1)).hom := rfl

lemma ι_injective (h : Function.Exact (P.d (j+1) j) (P.d j (j-1))) :
    Function.Injective (ι P j) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  obtain ⟨y, rfl⟩ := π_surjective P j x
  apply Submodule.Quotient.mk_eq_zero _ |>.mpr
  exact (h y).mp hx

def descend {N : Type} [AddCommGroup N] [Module R N] (f : P.X j →ₗ[R] N)
    (hf : f.comp (P.d (j+1) j).hom = 0) : CokerAt P j →ₗ[R] N :=
  (LinearMap.range (P.d (j+1) j).hom).liftQ f (by
    rintro x ⟨y, rfl⟩
    exact LinearMap.congr_fun hf y)

@[simp] lemma descend_π {N : Type} [AddCommGroup N] [Module R N]
    (f : P.X j →ₗ[R] N) (hf) (x : P.X j) : descend P j f hf (π P j x) = f x := rfl

lemma descend_comp_π {N : Type} [AddCommGroup N] [Module R N]
    (f : P.X j →ₗ[R] N) (hf) : (descend P j f hf).comp (π P j) = f := rfl
end CokerAt

def ComplexExact (P : ChainComplex (ModuleCat R) ℤ) : Prop :=
  ∀ j, Function.Exact (P.d (j+1) j) (P.d j (j-1))

def TotallyAcyclic (P : ChainComplex (ModuleCat R) ℤ) : Prop :=
  ComplexExact P ∧ ∀ (j : ℤ) (f : P.X j →ₗ[R] R),
    f.comp (P.d (j+1) j).hom = 0 →
    ∃ g : P.X (j-1) →ₗ[R] R, g.comp (P.d j (j-1)).hom = f

namespace TotallyAcyclic
variable {P : ChainComplex (ModuleCat R) ℤ} (hP : TotallyAcyclic P)
include hP

lemma projective_boundaries {N : Type} [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (j : ℤ) (f : P.X j →ₗ[R] N)
    (hf : f.comp (P.d (j+1) j).hom = 0) :
    ∃ g : P.X (j-1) →ₗ[R] N, g.comp (P.d j (j-1)).hom = f := by
  let c := finiteFreeCover (R := R) (M := N)
  obtain ⟨s, hs⟩ := Module.projective_lifting_property c.map (LinearMap.id (R := R) (M := N))
    c.surjective
  have hc (i : Fin c.rank) :
      ((LinearMap.proj i).comp (s.comp f)).comp (P.d (j+1) j).hom = 0 := by
    rw [LinearMap.comp_assoc, LinearMap.comp_assoc, hf, LinearMap.comp_zero, LinearMap.comp_zero]
  choose g hg using fun i : Fin c.rank => hP.2 j ((LinearMap.proj i).comp (s.comp f)) (hc i)
  refine ⟨c.map.comp (LinearMap.pi g), ?_⟩
  have heq : (LinearMap.pi g).comp (P.d j (j-1)).hom = s.comp f := by
    apply LinearMap.ext
    intro x
    funext i
    exact LinearMap.congr_fun (hg i) x
  rw [LinearMap.comp_assoc, heq, ← LinearMap.comp_assoc, hs, LinearMap.id_comp]

lemma extend_coker {N : Type} [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (j : ℤ) (f : CokerAt P j →ₗ[R] N) :
    ∃ g : P.X (j-1) →ₗ[R] N, g.comp (CokerAt.ι P j) = f := by
  obtain ⟨g, hg⟩ := hP.projective_boundaries j (f.comp (CokerAt.π P j)) (by
    rw [LinearMap.comp_assoc, CokerAt.π_d, LinearMap.comp_zero])
  refine ⟨g, ?_⟩
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := CokerAt.π_surjective P j x
  exact LinearMap.congr_fun hg y
end TotallyAcyclic
end Tachikawa



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (P : ChainComplex (ModuleCat R) ℤ)

namespace CokerAt
instance instModule_1 (j : ℤ) : Module k (CokerAt P j) :=
  Module.compHom (CokerAt P j) (algebraMap k R)
instance instIsScalarTower (j : ℤ) : IsScalarTower k R (CokerAt P j) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl
end CokerAt

lemma ComplexExact.adjacent (hex : ComplexExact P) (i j l : ℤ)
    (hi : i = j+1) (hl : l = j-1) :
    Function.Exact (P.d i j) (P.d j l) := by
  subst i
  subst l
  exact hex j

end Tachikawa



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {R : Type} [Ring R]

namespace CokerAt
variable (P : ChainComplex (ModuleCat R) ℤ)

def δ (i j : ℤ) : CokerAt P i →ₗ[R] P.X j :=
  descend P i (P.d i j).hom (ModuleCat.hom_ext_iff.mp (P.d_comp_d (i+1) i j))

@[simp] lemma δ_π (i j : ℤ) (x : P.X i) : δ P i j (π P i x) = P.d i j x := rfl

lemma δ_injective (hex : ComplexExact P) (i j : ℤ) (h : i = j+1) :
    Function.Injective (δ P i j) := by
  have hj : j = i-1 := by omega
  subst j
  exact ι_injective P i (hex i)

lemma π_comp_δ (i j : ℤ) (h : i = j+1) : (π P j).comp (δ P i j) = 0 := by
  subst i
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := π_surjective P (j+1) x
  exact LinearMap.congr_fun (π_d P j) y

lemma δ_π_exact (i j : ℤ) (h : i = j+1) :
    Function.Exact (δ P i j) (π P j) := by
  subst i
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).mp hx
    exact ⟨π P (j+1) y, hy⟩
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun (π_comp_δ P _ _ rfl) y

def factorThrough {L M N : Type} [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]
    [Module R L] [Module R M] [Module R N]
    (i : M →ₗ[R] N) (hi : Function.Injective i) (f : L →ₗ[R] N)
    (hf : ∀ x, f x ∈ LinearMap.range i) : L →ₗ[R] M :=
  (LinearEquiv.ofInjective i hi).symm.toLinearMap.comp (f.codRestrict _ hf)

lemma factorThrough_spec {L M N : Type} [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]
    [Module R L] [Module R M] [Module R N]
    (i : M →ₗ[R] N) (hi : Function.Injective i) (f : L →ₗ[R] N)
    (hf : ∀ x, f x ∈ LinearMap.range i) :
    i.comp (factorThrough i hi f hf) = f := by
  ext x
  change i ((LinearEquiv.ofInjective i hi).symm ⟨f x, hf x⟩) = f x
  exact LinearEquiv.ofInjective_symm_apply i _
end CokerAt

namespace TotallyAcyclic
variable {P : ChainComplex (ModuleCat R) ℤ}

lemma extend_at (hP : TotallyAcyclic P) {N : Type} [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (i j : ℤ) (h : i = j+1)
    (f : CokerAt P i →ₗ[R] N) :
    ∃ g : P.X j →ₗ[R] N, g.comp (CokerAt.δ P i j) = f := by
  have hj : j = i-1 := by omega
  subst j
  exact hP.extend_coker i f
end TotallyAcyclic

variable (P Q : ChainComplex (ModuleCat R) ℤ)

structure ComparisonStep (i j : ℤ) (u : CokerAt P i →ₗ[R] CokerAt Q i)
    (v : CokerAt P j →ₗ[R] CokerAt Q j) where
  map : P.X j →ₗ[R] Q.X j
  upper : map.comp (CokerAt.δ P i j) = (CokerAt.δ Q i j).comp u
  lower : (CokerAt.π Q j).comp map = v.comp (CokerAt.π P j)

lemma comparison_step_up (hq : ComplexExact Q)
    (proj : ∀ j, Module.Projective R (P.X j)) (i j : ℤ) (h : i = j+1)
    (v : CokerAt P j →ₗ[R] CokerAt Q j) :
    ∃ u : CokerAt P i →ₗ[R] CokerAt Q i, Nonempty (ComparisonStep P Q i j u v) := by
  let := proj j
  obtain ⟨f, hf⟩ := Module.projective_lifting_property (CokerAt.π Q j)
    (v.comp (CokerAt.π P j)) (CokerAt.π_surjective Q j)
  have hr (x : CokerAt P i) : f (CokerAt.δ P i j x) ∈ LinearMap.range (CokerAt.δ Q i j) := by
    apply (CokerAt.δ_π_exact Q i j h _).mp
    change ((CokerAt.π Q j).comp f) (CokerAt.δ P i j x) = 0
    rw [hf]
    change v (((CokerAt.π P j).comp (CokerAt.δ P i j)) x) = 0
    rw [CokerAt.π_comp_δ P i j h]
    exact map_zero v
  let u := CokerAt.factorThrough (CokerAt.δ Q i j) (CokerAt.δ_injective Q hq i j h)
    (f.comp (CokerAt.δ P i j)) hr
  exact ⟨u, ⟨⟨f, (CokerAt.factorThrough_spec _ _ _ _).symm, hf⟩⟩⟩

lemma comparison_step_down (hp : TotallyAcyclic P)
    (qfin : ∀ j, Module.Finite R (Q.X j)) (qproj : ∀ j, Module.Projective R (Q.X j))
    (i j : ℤ) (h : i = j+1) (u : CokerAt P i →ₗ[R] CokerAt Q i) :
    ∃ v : CokerAt P j →ₗ[R] CokerAt Q j, Nonempty (ComparisonStep P Q i j u v) := by
  let := qfin j
  let := qproj j
  obtain ⟨f, hf⟩ := hp.extend_at i j h ((CokerAt.δ Q i j).comp u)
  subst i
  have hf' : ((CokerAt.π Q j).comp f).comp (P.d (j+1) j).hom = 0 := by
    ext x
    have hfx := LinearMap.congr_fun hf (CokerAt.π P (j+1) x)
    change f (P.d (j+1) j x) = CokerAt.δ Q (j+1) j (u (CokerAt.π P (j+1) x)) at hfx
    change CokerAt.π Q j (f (P.d (j+1) j x)) = 0
    rw [hfx]
    exact LinearMap.congr_fun (CokerAt.π_comp_δ Q _ _ rfl) _
  exact ⟨CokerAt.descend P j ((CokerAt.π Q j).comp f) hf', ⟨⟨f, hf, rfl⟩⟩⟩

namespace CompleteLift
variable (hp : TotallyAcyclic P) (hq : ComplexExact Q)
    (pproj : ∀ j, Module.Projective R (P.X j))
    (qfin : ∀ j, Module.Finite R (Q.X j)) (qproj : ∀ j, Module.Projective R (Q.X j))

def up (j : ℤ) (v : CokerAt P j →ₗ[R] CokerAt Q j) :
    CokerAt P (j+1) →ₗ[R] CokerAt Q (j+1) :=
  (comparison_step_up P Q hq pproj (j+1) j rfl v).choose

def upSquare (j : ℤ) (v : CokerAt P j →ₗ[R] CokerAt Q j) :
    ComparisonStep P Q (j+1) j (up P Q hq pproj j v) v :=
  (comparison_step_up P Q hq pproj (j+1) j rfl v).choose_spec.some

def down (j : ℤ) (u : CokerAt P j →ₗ[R] CokerAt Q j) :
    CokerAt P (j-1) →ₗ[R] CokerAt Q (j-1) :=
  (comparison_step_down P Q hp qfin qproj j (j-1) (by omega) u).choose

def downSquare (j : ℤ) (u : CokerAt P j →ₗ[R] CokerAt Q j) :
    ComparisonStep P Q j (j-1) u (down P Q hp qfin qproj j u) :=
  (comparison_step_down P Q hp qfin qproj j (j-1) (by omega) u).choose_spec.some

variable (u₀ : CokerAt P 0 →ₗ[R] CokerAt Q 0)

def cokerMap (j : ℤ) : CokerAt P j →ₗ[R] CokerAt Q j :=
  j.inductionOn' 0 u₀ (fun j _ => up P Q hq pproj j) (fun j _ => down P Q hp qfin qproj j)

lemma cokerMap_zero : cokerMap P Q hp hq pproj qfin qproj u₀ 0 = u₀ :=
  Int.inductionOn'_self

lemma cokerMap_up (j : ℤ) (hj : 0 ≤ j) :
    cokerMap P Q hp hq pproj qfin qproj u₀ (j+1) =
      up P Q hq pproj j (cokerMap P Q hp hq pproj qfin qproj u₀ j) :=
  Int.inductionOn'_add_one hj

lemma cokerMap_down (j : ℤ) (hj : j ≤ 0) :
    cokerMap P Q hp hq pproj qfin qproj u₀ (j-1) =
      down P Q hp qfin qproj j (cokerMap P Q hp hq pproj qfin qproj u₀ j) :=
  Int.inductionOn'_sub_one hj

lemma hasSquare_down (i j : ℤ) (h : i-1=j) (hi : i ≤ 0) :
    Nonempty (ComparisonStep P Q i j
      (cokerMap P Q hp hq pproj qfin qproj u₀ i)
      (cokerMap P Q hp hq pproj qfin qproj u₀ j)) := by
  subst j
  rw [cokerMap_down P Q hp hq pproj qfin qproj u₀ i hi]
  exact ⟨downSquare P Q hp qfin qproj i _⟩

lemma hasSquare (j : ℤ) : Nonempty (ComparisonStep P Q (j+1) j
    (cokerMap P Q hp hq pproj qfin qproj u₀ (j+1))
    (cokerMap P Q hp hq pproj qfin qproj u₀ j)) := by
  by_cases hj : 0 ≤ j
  · rw [cokerMap_up P Q hp hq pproj qfin qproj u₀ j hj]
    exact ⟨upSquare P Q hq pproj j _⟩
  · exact hasSquare_down P Q hp hq pproj qfin qproj u₀ (j+1) j (by omega) (by omega)

def square (j : ℤ) : ComparisonStep P Q (j+1) j
    (cokerMap P Q hp hq pproj qfin qproj u₀ (j+1))
    (cokerMap P Q hp hq pproj qfin qproj u₀ j) :=
  (hasSquare P Q hp hq pproj qfin qproj u₀ j).some

def chainMap : P ⟶ Q :=
  ChainComplex.ofHom
    (fun j => ModuleCat.ofHom (square P Q hp hq pproj qfin qproj u₀ j).map) (fun j => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      let s := square P Q hp hq pproj qfin qproj u₀ j
      let s' := square P Q hp hq pproj qfin qproj u₀ (j+1)
      change Q.d (j+1) j (s'.map x) = s.map (P.d (j+1) j x)
      rw [← CokerAt.δ_π Q (j+1) j]
      have h₁ := LinearMap.congr_fun s'.lower x
      have h₂ := LinearMap.congr_fun s.upper (CokerAt.π P (j+1) x)
      change CokerAt.π Q (j+1) (s'.map x) = _ at h₁
      rw [h₁]
      exact h₂.symm)

end CompleteLift

namespace CokerAt
variable {P Q}

def map (f : P ⟶ Q) (j : ℤ) : CokerAt P j →ₗ[R] CokerAt Q j :=
  descend P j ((π Q j).comp (f.f j).hom) (by
    apply LinearMap.ext
    intro x
    have h := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (f.comm (j+1) j)) x
    change Q.d (j+1) j (f.f (j+1) x) = f.f j (P.d (j+1) j x) at h
    change π Q j (f.f j (P.d (j+1) j x)) = 0
    rw [← h]
    exact LinearMap.congr_fun (π_d Q j) (f.f (j+1) x))

@[simp] lemma map_π (f : P ⟶ Q) (j : ℤ) (x : P.X j) :
    map f j (π P j x) = π Q j (f.f j x) := rfl

lemma map_comp {S : ChainComplex (ModuleCat R) ℤ} (f : P ⟶ Q) (g : Q ⟶ S) (j : ℤ) :
    map (f ≫ g) j = (map g j).comp (map f j) := by
  ext x
  obtain ⟨y, rfl⟩ := π_surjective P j x
  rfl

end CokerAt

end Tachikawa



namespace Tachikawa.CokerAt
open CategoryTheory
variable {R : Type} [Ring R] (P : ChainComplex (ModuleCat.{0} R) ℤ)
  (N : ModuleCat.{0} R) (j : ℤ) (a : P.X j →ₗ[R] N)
  (he : Function.Exact (P.d (j+1) j) a) (hs : Function.Surjective a)

def augmentationEquiv : CokerAt P j ≃ₗ[R] N :=
  LinearEquiv.ofBijective (descend P j a he.linearMap_comp_eq_zero) (by
    constructor
    · apply LinearMap.ker_eq_bot.mp
      apply LinearMap.ker_eq_bot'.mpr
      intro x hx
      obtain ⟨y,rfl⟩ := π_surjective P j x
      change a y = 0 at hx
      obtain ⟨z,hz⟩ := (he y).mp hx
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨z,hz⟩
    · intro x
      obtain ⟨y,rfl⟩ := hs x
      exact ⟨π P j y,rfl⟩)

@[simp] lemma augmentationEquiv_π (x : P.X j) :
    augmentationEquiv P N j a he hs (π P j x) = a x := rfl
end Tachikawa.CokerAt

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Tensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa.BalancedTensor
variable {k R S M M' N N' N'' : Type} [Field k] [Ring R] [Ring S]
  [Algebra k R] [Algebra k S]
  [AddCommGroup M] [Module k M] [Module S M] [Module Rᵐᵒᵖ M]
  [IsScalarTower k S M] [IsScalarTower k Rᵐᵒᵖ M]
  [AddCommGroup M'] [Module k M'] [Module S M'] [Module Rᵐᵒᵖ M']
  [IsScalarTower k S M']
  [AddCommGroup N] [Module k N] [Module R N] [IsScalarTower k R N]
  [AddCommGroup N'] [Module k N'] [Module R N'] [IsScalarTower k R N']
  [AddCommGroup N''] [Module k N''] [Module R N''] [IsScalarTower k R N'']

def oppositeFree (ι : Type) : (ι → Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖ] (ι → R) where
  toFun x i := (x i).unop
  invFun x i := MulOpposite.op (x i)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Tachikawa.BalancedTensor



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_CompleteTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]

structure FiniteModule (k R : Type) [Field k] [Ring R] [Algebra k R] where
  obj : ModuleCat.{0} R
  finite : Module.Finite R obj

namespace FiniteModule
instance instCoeSortType : CoeSort (FiniteModule k R) Type := ⟨fun M => M.obj⟩
instance instAddCommGroupCarrierObj (M : FiniteModule k R) : AddCommGroup M := inferInstanceAs (AddCommGroup M.obj)
instance instModuleCarrierObj_1 (M : FiniteModule k R) : Module k M := inferInstanceAs (Module k M.obj)
instance instIsScalarTowerCarrierObj (M : FiniteModule k R) : IsScalarTower k R M := inferInstanceAs (IsScalarTower k R M.obj)
instance instFiniteCarrierObj (M : FiniteModule k R) : Module.Finite R M := M.finite
instance instFiniteCarrierObj_1 (M : FiniteModule k R) : Module.Finite k M := Module.Finite.trans R M

variable (M : FiniteModule k R)

def cover : FiniteFreeCover R M := finiteFreeCover

def syzygy : FiniteModule k R where
  obj := ModuleCat.of R (LinearMap.ker M.cover.map)
  finite := by
    let : IsNoetherianRing R := IsNoetherianRing.of_finite k R
    exact inferInstanceAs (Module.Finite R (LinearMap.ker M.cover.map))

def positive : ℕ → FiniteModule k R
  | 0 => M
  | n+1 => (positive n).syzygy

abbrev posTerm (n : ℕ) := Fin (M.positive n).cover.rank → R

def posDifferential (n : ℕ) : M.posTerm (n+1) →ₗ[R] M.posTerm n :=
  (LinearMap.ker (M.positive n).cover.map).subtype.comp (M.positive (n+1)).cover.map

lemma pos_exact (n : ℕ) : Function.Exact (M.posDifferential (n+1)) (M.posDifferential n) := by
  intro x
  change ((M.positive (n+1)).cover.map x).val = 0 ↔ _
  constructor
  · intro hx
    have hx' : (M.positive (n+1)).cover.map x = 0 := Subtype.ext hx
    obtain ⟨y, hy⟩ := (M.positive (n+2)).cover.surjective ⟨x, hx'⟩
    exact ⟨y, congrArg Subtype.val hy⟩
  · rintro ⟨y, rfl⟩
    exact congrArg Subtype.val ((M.positive (n+2)).cover.map y).property

end FiniteModule
end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex
open scoped ModuleCat.Algebra
variable {R : Type} [Ring R]
variable {P Q : ChainComplex (ModuleCat.{0} R) ℤ} (f : P ⟶ Q)

def GoodComponent (i j : ℤ) (h : P.X i →ₗ[R] Q.X j) : Prop :=
  ((f.f i).hom - (Q.d j i).hom.comp h).comp (P.d j i).hom = 0

lemma goodComponent_up (hq : ComplexExact Q)
    (pproj : ∀ j, Module.Projective R (P.X j))
    (i j l : ℤ) (hij : i+1=j) (hjl : j+1=l)
    (a : P.X i →ₗ[R] Q.X j) (ha : GoodComponent f i j a) :
    ∃ b : P.X j →ₗ[R] Q.X l,
      (f.f j).hom = a.comp (P.d j i).hom + (Q.d l j).hom.comp b ∧
      GoodComponent f j l b := by
  let := pproj j
  let r := (f.f j).hom - a.comp (P.d j i).hom
  have hr (x : P.X j) : r x ∈ LinearMap.range (Q.d l j).hom := by
    have he := hq j
    have hi : i = j-1 := by omega
    have hl : l = j+1 := by omega
    subst i
    subst l
    apply (he _).mp
    have hc := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (f.comm j (j-1))) x
    change Q.d j (j-1) (f.f j x) = f.f (j-1) (P.d j (j-1) x) at hc
    have hh := LinearMap.congr_fun ha x
    change f.f (j-1) (P.d j (j-1) x) - Q.d j (j-1) (a (P.d j (j-1) x)) = 0 at hh
    change Q.d j (j-1) (f.f j x - a (P.d j (j-1) x)) = 0
    rw [map_sub, hc]
    exact hh
  obtain ⟨b, hb⟩ := Module.projective_lifting_property
    (Q.d l j).hom.rangeRestrict (r.codRestrict _ hr) (by rintro ⟨x, y, rfl⟩; exact ⟨y, rfl⟩)
  have hb' : (Q.d l j).hom.comp b = r := by
    ext x
    exact congrArg Subtype.val (LinearMap.congr_fun hb x)
  refine ⟨b, ?_, ?_⟩
  · rw [hb']
    dsimp only [r]
    abel
  · unfold GoodComponent
    rw [hb']
    dsimp only [r]
    rw [sub_sub_cancel, LinearMap.comp_assoc]
    have hd : (P.d j i).hom.comp (P.d l j).hom = 0 :=
      ModuleCat.hom_ext_iff.mp (P.d_comp_d _ _ _)
    rw [hd, LinearMap.comp_zero]

lemma goodComponent_down (hp : TotallyAcyclic P)
    (qfin : ∀ j, Module.Finite R (Q.X j)) (qproj : ∀ j, Module.Projective R (Q.X j))
    (i j l : ℤ) (hij : i+1=j) (hjl : j+1=l)
    (b : P.X j →ₗ[R] Q.X l) (hb : GoodComponent f j l b) :
    ∃ a : P.X i →ₗ[R] Q.X j,
      (f.f j).hom = a.comp (P.d j i).hom + (Q.d l j).hom.comp b ∧
      GoodComponent f i j a := by
  subst l
  let := qfin j
  let := qproj j
  have hi : i = j-1 := by omega
  subst i
  obtain ⟨a, ha⟩ := hp.projective_boundaries j
    ((f.f j).hom - (Q.d (j+1) j).hom.comp b) hb
  refine ⟨a, ?_, ?_⟩
  · rw [ha]
    abel
  · unfold GoodComponent
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.zero_apply]
    have hc := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (f.comm j (j-1))) x
    change Q.d j (j-1) (f.f j x) = f.f (j-1) (P.d j (j-1) x) at hc
    have hx := LinearMap.congr_fun ha x
    change a (P.d j (j-1) x) = f.f j x - Q.d (j+1) j (b x) at hx
    rw [hx, map_sub, ← hc]
    have hd := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (Q.d_comp_d (j+1) j (j-1))) (b x)
    change Q.d j (j-1) (Q.d (j+1) j (b x)) = 0 at hd
    rw [hd, sub_zero, sub_self]

namespace CompleteNull

def State (j : ℤ) := {h : P.X j →ₗ[R] Q.X (j+1) // GoodComponent f j (j+1) h}

def stateMap {i : ℤ} (a : State f i) (j : ℤ) (h : i+1=j) : P.X i →ₗ[R] Q.X j := by
  subst j
  exact a.val

end CompleteNull

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_StableShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa.VectorSplit
open CategoryTheory
variable {k : Type*} [Field k] {I : Type*} {c : ComplexShape I}
variable (K : HomologicalComplex (ModuleCat k) c)

abbrev Z (i : I) := LinearMap.ker (K.d i (c.next i)).hom

def inc (i : I) : Z K i →ₗ[k] K.X i := (Z K i).subtype

def retract (i : I) : K.X i →ₗ[k] Z K i :=
  ((inc K i).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr Subtype.val_injective)).choose

lemma retract_inc (i : I) : (retract K i).comp (inc K i) = LinearMap.id :=
  ((inc K i).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr Subtype.val_injective)).choose_spec

@[simp] lemma retract_cycle (i : I) (z : Z K i) : retract K i z = z :=
  LinearMap.congr_fun (retract_inc K i) z

lemma cycle_d (i j : I) (z : Z K i) : K.d i j z = 0 := by
  by_cases h : c.Rel i j
  · have hj : c.next i = j := c.next_eq' h
    subst j
    exact z.property
  · rw [K.shape i j h]
    rfl

def boundary (i : I) : K.X (c.prev i) →ₗ[k] Z K i :=
  (K.d (c.prev i) i).hom.codRestrict _ (fun x => by
    change K.d i (c.next i) (K.d (c.prev i) i x) = 0
    exact congrArg (fun f : K.X (c.prev i) ⟶ K.X (c.next i) => f x)
      (K.d_comp_d (c.prev i) i (c.next i)))

@[simp] lemma boundary_cycle (i : I) (z : Z K (c.prev i)) : boundary K i z = 0 := by
  apply Subtype.ext
  exact cycle_d K (c.prev i) i z

abbrev H (i : I) := Z K i ⧸ LinearMap.range (boundary K i)

def quotient (i : I) : Z K i →ₗ[k] H K i := (LinearMap.range (boundary K i)).mkQ

def representatives (i : I) : H K i →ₗ[k] Z K i :=
  ((quotient K i).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _))).choose

lemma quotient_representatives (i : I) :
    (quotient K i).comp (representatives K i) = LinearMap.id :=
  ((quotient K i).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _))).choose_spec

@[simp] lemma quotient_representatives_apply (i : I) (x : H K i) :
    quotient K i (representatives K i x) = x :=
  LinearMap.congr_fun (quotient_representatives K i) x

@[simp] lemma quotient_boundary (i : I) (x : K.X (c.prev i)) :
    quotient K i (boundary K i x) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).2 ⟨x,rfl⟩

def boundaryPart (i : I) : Z K i →ₗ[k] LinearMap.range (boundary K i) :=
  (LinearMap.id - (representatives K i).comp (quotient K i)).codRestrict _ (fun z => by
    apply (Submodule.Quotient.mk_eq_zero _).1
    change quotient K i (z - representatives K i (quotient K i z)) = 0
    rw [map_sub, quotient_representatives_apply, sub_self])

def rawLift (i : I) : LinearMap.range (boundary K i) →ₗ[k] K.X (c.prev i) :=
  ((boundary K i).rangeRestrict.exists_rightInverse_of_surjective
    (boundary K i).range_rangeRestrict).choose

lemma boundary_rawLift (i : I) (z : LinearMap.range (boundary K i)) :
    boundary K i (rawLift K i z) = z := by
  have h := LinearMap.congr_fun
    (((boundary K i).rangeRestrict.exists_rightInverse_of_surjective
      (boundary K i).range_rangeRestrict).choose_spec) z
  exact congrArg Subtype.val h

def lift (i : I) : LinearMap.range (boundary K i) →ₗ[k] K.X (c.prev i) :=
  (LinearMap.id - (inc K (c.prev i)).comp (retract K (c.prev i))).comp (rawLift K i)

lemma boundary_lift (i : I) (z : LinearMap.range (boundary K i)) :
    boundary K i (lift K i z) = z := by
  change boundary K i (rawLift K i z - inc K (c.prev i) (retract K (c.prev i) (rawLift K i z))) = z
  change boundary K i (rawLift K i z - (retract K (c.prev i) (rawLift K i z) : K.X (c.prev i))) = z
  rw [map_sub, boundary_cycle, sub_zero, boundary_rawLift]

def complement (i : I) : K.X i →ₗ[k] K.X i :=
  LinearMap.id - (inc K i).comp (retract K i)

lemma complement_cycle (i : I) (z : Z K i) : complement K i z = 0 := by
  change (z : K.X i) - inc K i (retract K i z) = 0
  rw [retract_cycle]
  exact sub_self _

lemma complement_eq_lift (i : I) (hi : c.Rel (c.prev i) i) (x : K.X (c.prev i)) :
    complement K (c.prev i) x = lift K i ((boundary K i).rangeRestrict x) := by
  have hz : x - rawLift K i ((boundary K i).rangeRestrict x) ∈ Z K (c.prev i) := by
    change K.d (c.prev i) (c.next (c.prev i)) (x - rawLift K i ((boundary K i).rangeRestrict x)) = 0
    rw [c.next_eq' hi, map_sub]
    have h := congrArg Subtype.val (boundary_rawLift K i ((boundary K i).rangeRestrict x))
    exact sub_eq_zero.mpr h.symm
  have h := complement_cycle K (c.prev i) ⟨_,hz⟩
  change complement K (c.prev i) (x - rawLift K i ((boundary K i).rangeRestrict x)) = 0 at h
  rw [map_sub, sub_eq_zero] at h
  exact h

def homotopyComponent (i : I) : K.X i →ₗ[k] K.X (c.prev i) :=
  (lift K i).comp ((boundaryPart K i).comp (retract K i))

lemma homotopy_d (i : I) (x : K.X i) :
    K.d (c.prev i) i (homotopyComponent K i x) =
      inc K i (retract K i x) - inc K i (representatives K i (quotient K i (retract K i x))) := by
  exact congrArg Subtype.val (boundary_lift K i (boundaryPart K i (retract K i x)))

lemma homotopy_boundary (i : I) (hi : c.Rel (c.prev i) i) (x : K.X (c.prev i)) :
    homotopyComponent K i (K.d (c.prev i) i x) = complement K (c.prev i) x := by
  change lift K i (boundaryPart K i (retract K i (boundary K i x))) = _
  rw [retract_cycle]
  have h : boundaryPart K i (boundary K i x) = (boundary K i).rangeRestrict x := by
    apply Subtype.ext
    change boundary K i x - representatives K i (quotient K i (boundary K i x)) = _
    rw [quotient_boundary, map_zero, sub_zero]
    rfl
  rw [h]
  exact (complement_eq_lift K i hi x).symm

end Tachikawa.VectorSplit



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (P : ChainComplex (ModuleCat R) ℤ) (N : ModuleCat R)

def completeHom : CochainComplex (ModuleCat k) ℤ :=
  (((linearYoneda k (ModuleCat R)).obj N).mapHomologicalComplex (.up ℤ)).obj P.op

@[simp] lemma completeHom_d (i j : ℤ) (f : P.X i ⟶ N) :
    (completeHom (k := k) P N).d i j f = P.d j i ≫ f := rfl

lemma completeHom_memZ (j : ℤ) (f : P.X j ⟶ N) :
    f ∈ VectorSplit.Z (completeHom (k := k) P N) j ↔ P.d (j+1) j ≫ f = 0 := by
  change (completeHom (k := k) P N).d j ((ComplexShape.up ℤ).next j) f = 0 ↔ _
  rw [(ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel j (j+1) from rfl)]
  rfl

namespace CompleteHom

def cokerCycles (j : ℤ) : (CokerAt P j →ₗ[R] N) ≃ₗ[k]
    VectorSplit.Z (completeHom (k := k) P N) j where
  toFun f := ⟨ModuleCat.ofHom (f.comp (CokerAt.π P j)), by
    apply (completeHom_memZ P N j _).mpr
    apply ModuleCat.hom_ext
    change (f.comp (CokerAt.π P j)).comp (P.d (j+1) j).hom = 0
    rw [LinearMap.comp_assoc,CokerAt.π_d,LinearMap.comp_zero]⟩
  invFun z := CokerAt.descend P j z.val.hom (ModuleCat.hom_ext_iff.mp
    ((completeHom_memZ P N j z.val).mp z.property))
  left_inv f := by
    ext x
    obtain ⟨y,rfl⟩ := CokerAt.π_surjective P j x
    rfl
  right_inv z := by
    apply Subtype.ext
    apply ModuleCat.hom_ext
    rfl
  map_add' f g := rfl
  map_smul' r f := rfl

end CompleteHom
end Tachikawa



namespace Tachikawa.VectorSplit
open CategoryTheory
variable {k : Type*} [Field k] {I : Type*} {c : ComplexShape I}
  {K L M : HomologicalComplex (ModuleCat k) c}

def cycleMap (f : K ⟶ L) (i : I) : Z K i →ₗ[k] Z L i :=
  ((f.f i).hom.comp (Z K i).subtype).codRestrict _ (fun x => by
    change L.d i (c.next i) (f.f i x) = 0
    have h := congrArg (fun z => z x) (f.comm i (c.next i))
    change L.d i (c.next i) (f.f i x) = f.f (c.next i) (K.d i (c.next i) x) at h
    rw [x.property,map_zero] at h
    exact h)

lemma cycleMap_boundary (f : K ⟶ L) (i : I) (x : K.X (c.prev i)) :
    cycleMap f i (boundary K i x) = boundary L i (f.f (c.prev i) x) := by
  apply Subtype.ext
  exact (congrArg (fun z => z x) (f.comm (c.prev i) i)).symm

def Hmap (f : K ⟶ L) (i : I) : H K i →ₗ[k] H L i :=
  (LinearMap.range (boundary K i)).mapQ (LinearMap.range (boundary L i)) (cycleMap f i)
    (by rintro _ ⟨x,rfl⟩; exact ⟨f.f (c.prev i) x,(cycleMap_boundary f i x).symm⟩)

end Tachikawa.VectorSplit



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  (P : ChainComplex (ModuleCat.{0} R) ℤ) {M N L : ModuleCat.{0} R}

def completeHomMap (f : M ⟶ N) : completeHom (k := k) P M ⟶ completeHom (k := k) P N where
  f a := ModuleCat.ofHom (show (P.X a ⟶ M) →ₗ[k] (P.X a ⟶ N) from
    { toFun := fun g => g ≫ f
      map_add' := fun _ _ => by simp only [Preadditive.add_comp]
      map_smul' := fun r g => by simpa only [RingHom.id_apply] using (Linear.smul_comp (P.X a) M N r g f) })
  comm' _ _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro g
    rfl

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Coresolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section
namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
variable {R : Type*} [Ring R]

def coresolutionOfExact (M : ModuleCat R) (P : ℕ → ModuleCat R)
    (d : ∀ n, P n ⟶ P (n+1)) (ε : M ⟶ P 0)
    (hd : ∀ n, Function.Exact (d n) (d (n+1)))
    (hε : Function.Exact ε (d 0)) (inj : Function.Injective ε)
    (injs : ∀ n, Injective (P n)) : InjectiveResolution M := by
  let sq : ∀ n, d n ≫ d (n+1) = 0 := fun n => ModuleCat.hom_ext <| LinearMap.ext <|
    (hd n).apply_apply_eq_zero
  let K := CochainComplex.of P d sq
  let ι : (CochainComplex.single₀ (ModuleCat R)).obj M ⟶ K :=
    (CochainComplex.fromSingle₀Equiv _ _).symm ⟨ε, by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact hε.apply_apply_eq_zero⟩
  refine {cocomplex := K, ι := ι, injective := injs, quasiIso := ⟨fun n => ?_⟩}
  cases n with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros _ (by rfl) (by rfl) (by simp)]
    · constructor
      · apply (ShortComplex.moduleCat_exact_iff _).2
        change ∀ x : P 0, K.d 0 1 x = 0 → ∃ y : M, ε y = x
        rw [show K.d 0 1 = d 0 from CochainComplex.of_d P d 0]
        exact fun x => (hε x).mp
      · change Mono ε
        exact (ModuleCat.mono_iff_injective ε).2 inj
  | succ n =>
    rw [quasiIsoAt_iff_exactAt _ _ (CochainComplex.exactAt_succ_single_obj _ _)]
    rw [HomologicalComplex.exactAt_iff' _ n (n+1) (n+2) (by simp) (by simp)]
    apply (ShortComplex.moduleCat_exact_iff _).2
    change ∀ x : P (n+1), K.d (n+1) (n+2) x = 0 → ∃ y, K.d n (n+1) y = x
    rw [show K.d n (n+1) = d n from CochainComplex.of_d P d n,
      show K.d (n+1) (n+2) = d (n+1) from CochainComplex.of_d P d (n+1)]
    exact fun x => (hd n x).mp

end Tachikawa



namespace Tachikawa.VectorSplit
open CategoryTheory HomologicalComplex
variable {k : Type*} [Field k] {I : Type*} {c : ComplexShape I}
variable (K : HomologicalComplex (ModuleCat k) c)

def hom (i j : I) : K.X i ⟶ K.X j := by
  classical
  exact if h : c.Rel j i then
    ModuleCat.ofHom (homotopyComponent K i) ≫ (K.XIsoOfEq (c.prev_eq' h)).hom
    else 0

lemma hom_eq (i j : I) (h : c.Rel j i) :
    hom K i j = ModuleCat.ofHom (homotopyComponent K i) ≫
      (K.XIsoOfEq (c.prev_eq' h)).hom := dite_eq_left h

lemma hom_eq_zero (i j : I) (h : ¬ c.Rel j i) : hom K i j = 0 := dite_eq_right h

lemma d_hom_of_rel (i j : I) (h : c.Rel i j) :
    K.d i j ≫ hom K j i = ModuleCat.ofHom (complement K i) := by
  obtain rfl := c.prev_eq' h
  rw [hom_eq K j (c.prev j) h]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact homotopy_boundary K j h x

end Tachikawa.VectorSplit



namespace Tachikawa
open CategoryTheory HomologicalComplex
variable {C₁ C₂ D I₁ I₂ J : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X₁, (F.obj X₁).Additive]
  (c : ComplexShape J) [DecidableEq J] [TotalComplexShape c₁ c₂ c]
  {K₁ L₁ M₁ : HomologicalComplex C₁ c₁} {K₂ L₂ M₂ : HomologicalComplex C₂ c₂}
  [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c] [HasMapBifunctor M₁ M₂ F c]

lemma bifunctorMap_comp (f₁ : K₁ ⟶ L₁) (g₁ : L₁ ⟶ M₁) (f₂ : K₂ ⟶ L₂) (g₂ : L₂ ⟶ M₂) :
    mapBifunctorMap f₁ f₂ F c ≫ mapBifunctorMap g₁ g₂ F c =
      mapBifunctorMap (f₁ ≫ g₁) (f₂ ≫ g₂) F c := by
  ext j i₁ i₂ h
  simp only [HomologicalComplex.comp_f, ι_mapBifunctorMap_assoc, ι_mapBifunctorMap,
    Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rw [NatTrans.naturality_assoc]

lemma bifunctorMap_id : mapBifunctorMap (𝟙 K₁) (𝟙 K₂) F c = 𝟙 _ := by
  ext j i₁ i₂ h
  rw [ι_mapBifunctorMap]
  change (F.map (𝟙 (K₁.X i₁))).app (K₂.X i₂) ≫
    (F.obj (K₁.X i₁)).map (𝟙 (K₂.X i₂)) ≫ _ = _
  rw [F.map_id, (F.obj (K₁.X i₁)).map_id]
  simp only [NatTrans.id_app, Category.id_comp, HomologicalComplex.id_f, Category.comp_id]

def bifunctorHomotopyEquiv (e₁ : HomotopyEquiv K₁ L₁) (e₂ : HomotopyEquiv K₂ L₂) :
    HomotopyEquiv (mapBifunctor K₁ K₂ F c) (mapBifunctor L₁ L₂ F c) where
  hom := mapBifunctorMap e₁.hom e₂.hom F c
  inv := mapBifunctorMap e₁.inv e₂.inv F c
  homotopyHomInvId := (Homotopy.ofEq (bifunctorMap_comp F c _ _ _ _)).trans
    ((mapBifunctorMapHomotopy₁ e₁.homotopyHomInvId (e₂.hom ≫ e₂.inv) F c).trans
      ((mapBifunctorMapHomotopy₂ (𝟙 K₁) e₂.homotopyHomInvId F c).trans
        (Homotopy.ofEq (bifunctorMap_id F c))))
  homotopyInvHomId := (Homotopy.ofEq (bifunctorMap_comp F c _ _ _ _)).trans
    ((mapBifunctorMapHomotopy₁ e₁.homotopyInvHomId (e₂.inv ≫ e₂.hom) F c).trans
      ((mapBifunctorMapHomotopy₂ (𝟙 L₁) e₂.homotopyInvHomId F c).trans
        (Homotopy.ofEq (bifunctorMap_id F c))))

end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
variable (k R : Type) [Field k] [Ring R] [Algebra k R]
  (P : ChainComplex (ModuleCat R) ℕ) (N : ModuleCat R)

def resolutionHom : CochainComplex (ModuleCat k) ℕ :=
  (((linearYoneda k (ModuleCat R)).obj N).mapHomologicalComplex (.up ℕ)).obj P.op

variable {k R} {M : ModuleCat R} (Q : ProjectiveResolution M)

lemma extMk_smul {n : ℕ} (f : Q.complex.X n ⟶ N)
    (hf : Q.complex.d (n+1) n ≫ f = 0) (r : k)
    (hrf : Q.complex.d (n+1) n ≫ (r • f) = 0) :
    Q.extMk (r • f) (n+1) rfl hrf = r • Q.extMk f (n+1) rfl hf := by
  have h := Q.extMk_comp_mk₀ f (n+1) rfl hf (r • 𝟙 N)
  simpa only [CategoryTheory.Linear.comp_smul, Category.comp_id, Ext.mk₀_smul,
    Ext.comp_smul, Ext.comp_mk₀_id] using h.symm

end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Abelian CochainComplex.HomComplex
open scoped ModuleCat.Algebra
variable (k R : Type) [Field k] [Ring R] [Algebra k R]
  (P : CochainComplex (ModuleCat R) ℕ) (N : ModuleCat R)

def coresolutionHom : CochainComplex (ModuleCat k) ℕ :=
  (((linearCoyoneda k (ModuleCat R)).obj (Opposite.op N)).mapHomologicalComplex (.up ℕ)).obj P

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_TwistHom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section
namespace Tachikawa
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesProjectiveObjects] [F.PreservesHomology]
  {X : C} (P : ProjectiveResolution X)

abbrev mappedResolution := F.mapProjectiveResolution P

end Tachikawa

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_OuterTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section



namespace Tachikawa.TotalMap
open CategoryTheory CategoryTheory.Limits HomologicalComplex₂
universe u
variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
variable {I₁ I₂ J : Type u} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
variable (F : C ⥤ D) [F.Additive] (K : HomologicalComplex₂ C c₁ c₂)
variable (c : ComplexShape J) [TotalComplexShape c₁ c₂ c] [DecidableEq J]

variable [K.HasTotal c]

instance sourceHasCoproduct (j : J) : HasCoproduct
    (K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c) j) :=
  (inferInstance : K.HasTotal c) j

end Tachikawa.TotalMap



set_option backward.isDefEq.respectTransparency true



namespace Tachikawa.OuterTensor
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable (k A B : Type) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

def freeObj (m : ℕ) : ModuleCat A := ModuleCat.of A (Fin m → A)

def underlyingFree (m : ℕ) : (freeObj A m) ≃ₗ[k] (Fin m → A) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    ext i
    change (algebraMap k A r) * x i = r • x i
    exact (Algebra.smul_def r (x i)).symm

def freeEquivLinear (m n : ℕ) :
    ((freeObj A m) ⊗[k] (freeObj B n)) ≃ₗ[k]
      (Fin m → Fin n → A ⊗[k] B) :=
  (TensorProduct.congr (underlyingFree k A m) (underlyingFree k B n)).trans
    ((TensorProduct.piLeft k (Fin n → B) (fun _ : Fin m => A)).trans
      (LinearEquiv.piCongrRight fun _ => TensorProduct.piRight k k A (fun _ : Fin n => B)))

end Tachikawa.OuterTensor



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_OuterExt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section
namespace Tachikawa
open CategoryTheory HomologicalComplex
variable {k : Type*} [Field k]
  {K L M N : ChainComplex (ModuleCat k) ℕ}

lemma vectorTensor_quasiIso (f : K ⟶ L) (g : M ⟶ N) [QuasiIso f] [QuasiIso g] :
    QuasiIso (mapBifunctorMap f g
      (CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat k)) (.down ℕ)) := by
  obtain ⟨e, he⟩ := (ChainComplex.quasiIso_iff_of_projective f).mp inferInstance
  obtain ⟨e', he'⟩ := (ChainComplex.quasiIso_iff_of_projective g).mp inferInstance
  rw [← he, ← he']
  exact (bifunctorHomotopyEquiv _ (.down ℕ) e e').quasiIso_hom

end Tachikawa



namespace Tachikawa.OuterTensor
open CategoryTheory HomologicalComplex
open scoped TensorProduct
variable (k A B : Type) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  {K K' : ChainComplex (ModuleCat A) ℕ} {L L' : ChainComplex (ModuleCat B) ℕ}

instance restrictionPreservesHomology {R S : Type} [Ring R] [Ring S] (f : R →+* S) :
    (ModuleCat.restrictScalars f).PreservesHomology where
  preservesKernels _ := inferInstance
  preservesCokernels _ := inferInstance

end Tachikawa.OuterTensor



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  [HasZeroObject C₁] [HasZeroObject C₂] [HasZeroObject D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X₁, (F.obj X₁).Additive]

def bifunctorZeroIso (K : ChainComplex C₁ ℕ) (L : ChainComplex C₂ ℕ)
    [HasMapBifunctor K L F (.down ℕ)] :
    (mapBifunctor K L F (.down ℕ)).X 0 ≅ (F.obj (K.X 0)).obj (L.X 0) where
  hom := mapBifunctorDesc (fun i j h => eqToHom (by
    have hh : i + j = 0 := h
    obtain ⟨rfl,rfl⟩ := Nat.add_eq_zero_iff.mp hh
    rfl))
  inv := ιMapBifunctor K L F (.down ℕ) 0 0 0 rfl
  hom_inv_id := by
    apply mapBifunctor.hom_ext
    intro i j h
    have hh : i + j = 0 := h
    obtain ⟨rfl,rfl⟩ := Nat.add_eq_zero_iff.mp hh
    rw [ι_mapBifunctorDesc_assoc]
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  inv_hom_id := by rw [ι_mapBifunctorDesc]; rfl

variable (M : C₁) (N : C₂)
variable [HasMapBifunctor ((ChainComplex.single₀ C₁).obj M)
  ((ChainComplex.single₀ C₂).obj N) F (.down ℕ)]
abbrev singleBifunctor := mapBifunctor ((ChainComplex.single₀ C₁).obj M)
  ((ChainComplex.single₀ C₂).obj N) F (.down ℕ)

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Nakayama
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Nakayama
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {P Z : Type} [AddCommGroup P] [Module R P]
  [AddCommGroup Z] [Module R Z] [Module k Z] [IsScalarTower k R Z]

variable (n : ℕ) (p : P →ₗ[R] (Fin n → R)) (s : (Fin n → R) →ₗ[R] P)
  (hs : s.comp p = LinearMap.id)

include hs in
lemma decomposed (x : P) : ∑ i, p x i • s (Pi.single i 1) = x := by
  have hh := congrArg (fun a : (Fin n → R) →ₗ[R] P => a (p x))
    ((LinearEquiv.piRing R P (Fin n) ℤ).symm_apply_apply s)
  have hh' : (∑ i, p x i • s (Pi.single i 1)) = s (p x) := by
    simpa only [LinearEquiv.piRing_symm_apply, LinearEquiv.piRing_apply] using hh
  exact hh'.trans (LinearMap.congr_fun hs x)

end Tachikawa.Nakayama



namespace Tachikawa
variable {k U V W : Type*} [Field k]
  [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

lemma exact_dual (f : U →ₗ[k] V) (g : V →ₗ[k] W) (h : Function.Exact f g) :
    Function.Exact g.dualMap f.dualMap := by
  rw [LinearMap.exact_iff, LinearMap.ker_dualMap_eq_dualAnnihilator_range,
    LinearMap.range_dualMap_eq_dualAnnihilator_ker, (LinearMap.exact_iff.mp h)]

end Tachikawa



namespace Tachikawa
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {P Q Z : Type} [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q] [AddCommGroup Z] [Module R Z]
  [Module k Z] [IsScalarTower k R Z]

def homPrecomp (f : P →ₗ[R] Q) : (Q →ₗ[R] Z) →ₗ[k] (P →ₗ[R] Z) where
  toFun g := g.comp f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Tachikawa



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]



def TrivialInflation (k R M : Type) [Field k] [Ring R] [Algebra k R]
    [AddCommGroup M] [Module R M] := M

namespace TrivialInflation
variable {M N : Type} [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
  [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]
instance instAddCommGroup : AddCommGroup (TrivialInflation k R M) := inferInstanceAs (AddCommGroup M)
instance instModule : Module k (TrivialInflation k R M) := inferInstanceAs (Module k M)
instance instModule_1 : Module R (TrivialInflation k R M) := inferInstanceAs (Module R M)
instance instIsScalarTower : IsScalarTower k R (TrivialInflation k R M) := inferInstanceAs (IsScalarTower k R M)

end TrivialInflation
end Tachikawa

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Corner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa

def LeftCorner {R : Type*} [Ring R] (p : R) : Submodule R R where
  carrier := {a | a * p = a}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change a * p = a at ha
    change b * p = b at hb
    change (a + b) * p = a + b
    rw [add_mul, ha, hb]
  smul_mem' := by intro a b hb; change (a * b) * p = a * b; rw [mul_assoc, hb]

@[simp] lemma mem_leftCorner {R : Type*} [Ring R] (p a : R) :
    a ∈ LeftCorner p ↔ a * p = a := Iff.rfl

namespace LeftCorner
variable {R : Type*} [Ring R] {p : R} (hp : p * p = p)

def generator : LeftCorner p := ⟨p, hp⟩

def projection : R →ₗ[R] LeftCorner p :=
  (LinearMap.mulRight R p).codRestrict (LeftCorner p) (fun a => by
    change (a * p) * p = a * p
    rw [mul_assoc, hp])

@[simp] lemma projection_apply (a : R) : (projection hp a : R) = a * p := rfl

lemma projection_comp_inclusion : (projection hp).comp (LeftCorner p).subtype = LinearMap.id := by
  ext a
  exact a.property

include hp in
lemma projective : Module.Projective R (LeftCorner p) :=
  Module.Projective.of_split (LeftCorner p).subtype (projection hp) (projection_comp_inclusion hp)

variable {N : Type*} [AddCommGroup N] [Module R N]

lemma hom_apply (f : LeftCorner p →ₗ[R] N) (a : LeftCorner p) :
    f a = (a : R) • f (generator hp) := by
  rw [← f.map_smul]
  congr 1
  apply Subtype.ext
  exact a.property.symm

def lift (n : N) (_hn : p • n = n) : LeftCorner p →ₗ[R] N where
  toFun a := (a : R) • n
  map_add' _ _ := add_smul _ _ _
  map_smul' _ _ := mul_smul _ _ _

@[simp] lemma lift_apply (n : N) (hn : p • n = n) (a : LeftCorner p) :
    lift n hn a = (a : R) • n := rfl

@[simp] lemma lift_generator (n : N) (hn : p • n = n) : lift n hn (generator hp) = n := hn

lemma generator_fixed (f : LeftCorner p →ₗ[R] N) : p • f (generator hp) = f (generator hp) := by
  rw [← f.map_smul]
  congr 1
  exact Subtype.ext hp

lemma hom_ext {f g : LeftCorner p →ₗ[R] N} (h : f (generator hp) = g (generator hp)) : f = g := by
  ext a
  calc
    f a = (a : R) • f (generator hp) := hom_apply hp f a
    _ = (a : R) • g (generator hp) := by rw [h]
    _ = g a := (hom_apply hp g a).symm

def mulRight {q : R} (b : R) (hb : b * q = b) : LeftCorner p →ₗ[R] LeftCorner q where
  toFun a := ⟨(a : R) * b, by change ((a : R) * b) * q = (a : R) * b; rw [mul_assoc, hb]⟩
  map_add' a c := Subtype.ext (add_mul _ _ _)
  map_smul' a c := Subtype.ext (mul_assoc _ _ _)

@[simp] lemma mulRight_apply {q : R} (b : R) (hb : b * q = b) (a : LeftCorner p) :
    (mulRight b hb a : R) = (a : R) * b := rfl

end LeftCorner
end Tachikawa

end


namespace Tachikawa

noncomputable section

def C (k : Type*) (_q : k) := Fin 10 → k

namespace C

variable {k : Type*} [Field k] (q : k)

instance instAddCommGroup : AddCommGroup (C k q) := inferInstanceAs (AddCommGroup (Fin 10 → k))
instance instModule : Module k (C k q) := inferInstanceAs (Module k (Fin 10 → k))

@[simp] lemma add_apply (a b : C k q) (i : Fin 10) : (a + b) i = a i + b i := rfl
@[simp] lemma zero_apply (i : Fin 10) : (0 : C k q) i = 0 := rfl
@[simp] lemma neg_apply (a : C k q) (i : Fin 10) : (-a) i = -a i := rfl
@[simp] lemma smul_apply (a : k) (b : C k q) (i : Fin 10) : (a • b) i = a * b i := rfl

def mul (a b : C k q) : C k q := ![
  a 0 * b 0,
  a 1 * b 1,
  a 0 * b 2 + a 2 * b 0 + q * a 5 * b 7,
  a 0 * b 3 + a 3 * b 0 + a 5 * b 7,
  a 0 * b 4 + a 4 * b 0 + q * a 2 * b 3 + a 3 * b 2 +
    a 5 * b 8 + q * a 6 * b 7,
  a 0 * b 5 + a 5 * b 1,
  a 0 * b 6 + a 6 * b 1 + a 2 * b 5 + a 3 * b 5 + a 5 * b 9,
  a 1 * b 7 + a 7 * b 0,
  a 1 * b 8 + a 8 * b 0 + a 7 * b 2 + q ^ 2 * a 7 * b 3 + q * a 9 * b 7,
  a 1 * b 9 + a 9 * b 1 + (1 + q) * a 7 * b 5]

def unit : C k q := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]

omit [Field k] in
@[ext] lemma ext {a b : C k q} (h : ∀ i, a i = b i) : a = b := funext h

lemma mul_assoc (a b c : C k q) : mul q (mul q a b) c = mul q a (mul q b c) := by
  ext i
  fin_cases i <;> simp [mul] <;> ring

lemma unit_mul (a : C k q) : mul q (unit q) a = a := by
  ext i
  fin_cases i <;> simp [mul, unit]

lemma mul_unit (a : C k q) : mul q a (unit q) = a := by
  ext i
  fin_cases i <;> simp [mul, unit]

lemma mul_add (a b c : C k q) : mul q a (b + c) = mul q a b + mul q a c := by
  ext i
  rw [add_apply]
  fin_cases i <;> simp [mul, add_apply] <;> ring

lemma add_mul (a b c : C k q) : mul q (a + b) c = mul q a c + mul q b c := by
  ext i
  rw [add_apply]
  fin_cases i <;> simp [mul, add_apply] <;> ring

instance instRing : Ring (C k q) where
  __ := (inferInstance : AddCommGroup (C k q))
  mul := mul q
  one := unit q
  mul_assoc := mul_assoc q
  one_mul := unit_mul q
  mul_one := mul_unit q
  left_distrib := mul_add q
  right_distrib := add_mul q
  zero_mul a := by
    ext i
    change mul q 0 a i = 0
    fin_cases i <;> simp [mul, zero_apply]
  mul_zero a := by
    ext i
    change mul q a 0 i = 0
    fin_cases i <;> simp [mul, zero_apply]

lemma smul_mul (r : k) (a b : C k q) : (r • a) * b = r • (a * b) := by
  ext i
  change mul q (r • a) b i = (r • mul q a b) i
  rw [smul_apply]
  fin_cases i <;> simp [mul, smul_apply] <;> ring

lemma mul_smul (r : k) (a b : C k q) : a * (r • b) = r • (a * b) := by
  ext i
  change mul q a (r • b) i = (r • mul q a b) i
  rw [smul_apply]
  fin_cases i <;> simp [mul, smul_apply] <;> ring

instance instAlgebra : Algebra k (C k q) := Algebra.ofModule (smul_mul q) (mul_smul q)

instance instFiniteDimensional : FiniteDimensional k (C k q) :=
  inferInstanceAs (FiniteDimensional k (Fin 10 → k))

end C
end
end Tachikawa



noncomputable section
namespace Tachikawa.C

variable {k : Type*} [Field k] (q : k)

def basis : Module.Basis (Fin 10) k (C k q) := Pi.basisFun k (Fin 10)

@[simp] lemma basis_apply (i j : Fin 10) : basis q i j = if j = i then 1 else 0 := by
  change (Pi.basisFun k (Fin 10) i) j = _
  simp [Pi.basisFun_apply, Pi.single_apply]

def f : C k q := ![0,1,0,0,0,0,0,0,0,0]

lemma mul_f (a : C k q) : a * f q = ![0,a 1,0,0,0,a 5,a 6,0,0,a 9] := by
  ext i
  change mul q a (f q) i = _
  fin_cases i <;> simp [mul, f]

lemma trace_left_right_f (a : C k q) :
    LinearMap.trace k (C k q) ((LinearMap.mulLeft k a).comp (LinearMap.mulRight k (f q))) =
      2 * a 0 + 2 * a 1 := by
  rw [LinearMap.trace_eq_matrix_trace k (basis q)]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply,
    LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
  change (∑ i : Fin 10, (a * ((basis q i) * f q)) i) = _
  simp only [mul_f]
  change (∑ i : Fin 10, mul q a ![0,(basis q i) 1,0,0,0,(basis q i) 5,
    (basis q i) 6,0,0,(basis q i) 9] i) = _
  simp [Fin.sum_univ_succ, mul, basis_apply]
  ring

lemma trace_left_right_f_eq_zero [CharP k 2] (a : C k q) :
    LinearMap.trace k (C k q) ((LinearMap.mulLeft k a).comp (LinearMap.mulRight k (f q))) = 0 := by
  have hc (r s : k) : 2 * r + 2 * s = 0 := by
    rw [show (2 : k) = 0 from CharP.cast_eq_zero k 2]
    simp only [zero_mul, add_zero]
  exact (trace_left_right_f q a).trans (hc (a 0) (a 1))




def e : C k q := ![1,0,0,0,0,0,0,0,0,0]
def u : C k q := ![0,0,0,0,0,1,0,0,0,0]
def ell (c : k) : C k q := ![0,0,1,c,0,0,0,0,0,0]

lemma mul_e (a : C k q) : a * e q = ![a 0,0,a 2,a 3,a 4,0,0,a 7,a 8,0] := by
  ext i
  change mul q a (e q) i = _
  fin_cases i <;> simp [mul, e]

lemma e_idempotent : e q * e q = e q := by rw [mul_e]; rfl
lemma f_idempotent : f q * f q = f q := by rw [mul_f]; rfl
lemma u_mul_f : u q * f q = u q := by rw [mul_f]; rfl
lemma ell_mul_e (c : k) : ell q c * e q = ell q c := by rw [mul_e]; rfl

abbrev Ce := LeftCorner (e q)
abbrev Cf := LeftCorner (f q)

instance instProjectiveSubtypeMemSubmoduleCe : Module.Projective (C k q) (Ce q) := LeftCorner.projective (e_idempotent q)
instance instProjectiveSubtypeMemSubmoduleCf : Module.Projective (C k q) (Cf q) := LeftCorner.projective (f_idempotent q)

def ce (a b c d t j : k) : Ce q := ⟨![a,0,b,c,d,0,0,t,j,0], by
  exact mul_e q ![a,0,b,c,d,0,0,t,j,0]⟩
def cf (a u v n : k) : Cf q := ⟨![0,a,0,0,0,u,v,0,0,n], by
  exact mul_f q ![0,a,0,0,0,u,v,0,0,n]⟩

lemma ce_eta (a : Ce q) : ce q (a.val 0) (a.val 2) (a.val 3) (a.val 4) (a.val 7) (a.val 8) = a := by
  apply Subtype.ext
  exact (mul_e q a.val).symm.trans a.property

lemma cf_eta (a : Cf q) : cf q (a.val 1) (a.val 5) (a.val 6) (a.val 9) = a := by
  apply Subtype.ext
  exact (mul_f q a.val).symm.trans a.property

@[simp] lemma ce_eq_zero (a b c d t j : k) : ce q a b c d t j = 0 ↔
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ t = 0 ∧ j = 0 := by
  constructor
  · intro h
    have hv := congrArg Subtype.val h
    exact ⟨congrFun hv 0, congrFun hv 2, congrFun hv 3, congrFun hv 4,
      congrFun hv 7, congrFun hv 8⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    apply Subtype.ext
    ext i
    fin_cases i <;> rfl

@[simp] lemma cf_eq_zero (a u v n : k) : cf q a u v n = 0 ↔
    a = 0 ∧ u = 0 ∧ v = 0 ∧ n = 0 := by
  constructor
  · intro h
    have hv := congrArg Subtype.val h
    exact ⟨congrFun hv 1, congrFun hv 5, congrFun hv 6, congrFun hv 9⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    apply Subtype.ext
    ext i
    fin_cases i <;> rfl

def rhoU : Ce q →ₗ[C k q] Cf q := LeftCorner.mulRight (u q) (u_mul_f q)
def rhoEll (c : k) : Ce q →ₗ[C k q] Ce q := LeftCorner.mulRight (ell q c) (ell_mul_e q c)

lemma rhoU_ce (a b c d t j : k) :
    rhoU q (ce q a b c d t j) = cf q 0 a (b + c) ((1 + q) * t) := by
  apply Subtype.ext
  ext i
  change mul q ![a,0,b,c,d,0,0,t,j,0] (u q) i = _
  fin_cases i <;> simp [mul, u, cf]

lemma rhoEll_ce (z a b c d t j : k) :
    rhoEll q z (ce q a b c d t j) = ce q 0 a (z * a) (q * z * b + c) 0 ((1 + q^2 * z) * t) := by
  apply Subtype.ext
  ext i
  change mul q ![a,0,b,c,d,0,0,t,j,0] (ell q z) i = _
  fin_cases i <;> simp [mul, ell, ce] <;> ring

end Tachikawa.C

namespace Tachikawa.C
variable {k : Type*} [Field k] [CharP k 2] (q : k)

lemma rhoEll_comp_zero (z : k) (y : Ce q) :
    rhoEll q z (rhoEll q (q*z) y) = 0 := by
  rw [← ce_eta q y, rhoEll_ce, rhoEll_ce]
  simp only [mul_zero, CharTwo.add_self_eq_zero, ce_eq_zero, and_self]

lemma rhoU_comp_zero (y : Ce q) : rhoU q (rhoEll q 1 y) = 0 := by
  rw [← ce_eta q y, rhoEll_ce, rhoU_ce]
  simp only [one_mul, CharTwo.add_self_eq_zero, mul_zero, cf_eq_zero, and_self]

lemma exact_rhoEll (z : k) (hz : 1 + q^2 * z ≠ 0) (hz' : 1 + q^2 * (q*z) ≠ 0) :
    Function.Exact (rhoEll q (q*z)) (rhoEll q z) := by
  intro x
  constructor
  · intro h
    rw [← ce_eta q x, rhoEll_ce, ce_eq_zero] at h
    obtain ⟨_, ha, _, hb, _, ht⟩ := h
    have ht' : x.val 7 = 0 := (mul_eq_zero.mp ht).resolve_left hz
    have hc : x.val 3 = q*z*x.val 2 := by
      have := eq_neg_of_add_eq_zero_left hb
      simpa only [CharTwo.neg_eq] using this.symm
    refine ⟨ce q (x.val 2) 0 (x.val 4) 0 (x.val 8 / (1 + q^2 * (q*z))) 0, ?_⟩
    rw [rhoEll_ce]
    have hx := ce_eta q x
    rw [ha, ht', hc] at hx
    simpa only [mul_zero, zero_add, mul_div_cancel₀ _ hz'] using hx
  · rintro ⟨y, rfl⟩
    exact rhoEll_comp_zero q z y

lemma exact_rhoU (hq : 1 + q ≠ 0) (hq2 : 1 + q^2 ≠ 0) :
    Function.Exact (rhoEll q 1) (rhoU q) := by
  intro x
  constructor
  · intro h
    rw [← ce_eta q x, rhoU_ce, cf_eq_zero] at h
    obtain ⟨_, ha, hbc, ht⟩ := h
    have ht' : x.val 7 = 0 := (mul_eq_zero.mp ht).resolve_left hq
    have hc : x.val 3 = x.val 2 := by
      have := eq_neg_of_add_eq_zero_left hbc
      simpa only [CharTwo.neg_eq] using this.symm
    refine ⟨ce q (x.val 2) 0 (x.val 4) 0 (x.val 8 / (1 + q^2)) 0, ?_⟩
    rw [rhoEll_ce]
    have hx := ce_eta q x
    rw [ha, ht', hc] at hx
    simpa only [mul_zero, zero_add, mul_one, one_mul, mul_div_cancel₀ _ hq2] using hx
  · rintro ⟨y, rfl⟩
    exact rhoU_comp_zero q y

end Tachikawa.C



namespace Tachikawa

def RightCorner {R : Type*} [Ring R] (p : R) : Submodule Rᵐᵒᵖ R where
  carrier := {a | p * a = a}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb; change p*(a+b)=a+b; rw [mul_add, ha, hb]
  smul_mem' := by intro a b hb; change p*(b*a.unop)=b*a.unop; rw [← mul_assoc, hb]

@[simp] lemma mem_rightCorner {R : Type*} [Ring R] (p a : R) :
    a ∈ RightCorner p ↔ p*a=a := Iff.rfl

namespace RightCorner
variable {R : Type*} [Ring R] {p : R} (hp : p*p=p)

def projection : R →ₗ[Rᵐᵒᵖ] RightCorner p where
  toFun a := ⟨p*a, by change p*(p*a)=p*a; rw [← mul_assoc, hp]⟩
  map_add' a b := Subtype.ext (mul_add _ _ _)
  map_smul' a b := Subtype.ext (mul_assoc _ _ _).symm

lemma projection_comp_inclusion : (projection hp).comp (RightCorner p).subtype = LinearMap.id := by
  ext a
  exact a.property

include hp in
lemma projective : Module.Projective Rᵐᵒᵖ (RightCorner p) := by
  let : Module.Projective Rᵐᵒᵖ R := Module.Projective.of_equiv
    (MulOpposite.opLinearEquiv Rᵐᵒᵖ).symm
  exact Module.Projective.of_split (RightCorner p).subtype (projection hp) (projection_comp_inclusion hp)

def homEquiv : (LeftCorner p →ₗ[R] R) ≃ₗ[Rᵐᵒᵖ] RightCorner p where
  toFun f := ⟨f (LeftCorner.generator hp), LeftCorner.generator_fixed hp f⟩
  invFun a := LeftCorner.lift a.val a.property
  left_inv _f := LeftCorner.hom_ext hp (LeftCorner.lift_generator hp _ _)
  right_inv _a := Subtype.ext (LeftCorner.lift_generator hp _ _)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma homEquiv_apply (f : LeftCorner p →ₗ[R] R) :
    (homEquiv hp f : R) = f (LeftCorner.generator hp) := rfl

def mulLeft {q : R} (b : R) (hb : q*b=b) : RightCorner p →ₗ[Rᵐᵒᵖ] RightCorner q where
  toFun a := ⟨b*(a:R), by change q*(b*(a:R))=b*(a:R); rw [← mul_assoc, hb]⟩
  map_add' _ _ := Subtype.ext (mul_add _ _ _)
  map_smul' _ _ := Subtype.ext (mul_assoc _ _ _).symm

@[simp] lemma mulLeft_apply {q : R} (b : R) (hb : q*b=b) (a : RightCorner p) :
    (mulLeft b hb a : R) = b*(a:R) := rfl

lemma homEquiv_precomp {q : R} (hq : q*q=q) (b : R) (hpb : p*b=b) (hbq : b*q=b)
    (f : LeftCorner q →ₗ[R] R) :
    homEquiv hp (f.comp (LeftCorner.mulRight b hbq)) = mulLeft b hpb (homEquiv hq f) := by
  apply Subtype.ext
  change f ⟨p*b, _⟩ = b * f (LeftCorner.generator hq)
  rw [LeftCorner.hom_apply hq]
  change (p*b) * f (LeftCorner.generator hq) = _
  rw [hpb]

end RightCorner
end Tachikawa



namespace Tachikawa.RightCorner
variable {R : Type*} [Ring R] {p : R}
variable {N : Type*} [AddCommGroup N] [Module Rᵐᵒᵖ N]

def lift (n : N) (_hn : MulOpposite.op p • n = n) : RightCorner p →ₗ[Rᵐᵒᵖ] N where
  toFun a := MulOpposite.op a.val • n
  map_add' a b := by
    change MulOpposite.op (a.val + b.val) • n = MulOpposite.op a.val • n + MulOpposite.op b.val • n
    rw [MulOpposite.op_add, add_smul]
  map_smul' a b := by
    change MulOpposite.op (b.val * a.unop) • n = a • MulOpposite.op b.val • n
    rw [MulOpposite.op_mul, MulOpposite.op_unop, mul_smul]

end Tachikawa.RightCorner

namespace Tachikawa.C
variable {k : Type} [Field k] (q : k)

lemma e_mul (a : C k q) : e q * a = ![a 0,0,a 2,a 3,a 4,a 5,a 6,0,0,0] := by
  ext i
  change mul q (e q) a i = _
  fin_cases i <;> simp [mul, e]

lemma f_mul (a : C k q) : f q * a = ![0,a 1,0,0,0,0,0,a 7,a 8,a 9] := by
  ext i
  change mul q (f q) a i = _
  fin_cases i <;> simp [mul, f]

lemma e_mul_u : e q * u q = u q := by rw [e_mul]; rfl
lemma e_mul_ell (c : k) : e q * ell q c = ell q c := by rw [e_mul]; rfl

abbrev eC := RightCorner (e q)
abbrev fC := RightCorner (f q)

instance instProjectiveMulOppositeSubtypeMemSubmoduleEC : Module.Projective (C k q)ᵐᵒᵖ (eC q) := RightCorner.projective (e_idempotent q)
instance instProjectiveMulOppositeSubtypeMemSubmoduleFC : Module.Projective (C k q)ᵐᵒᵖ (fC q) := RightCorner.projective (f_idempotent q)

def ec (a b c d u v : k) : eC q := ⟨![a,0,b,c,d,u,v,0,0,0], by
  exact e_mul q ![a,0,b,c,d,u,v,0,0,0]⟩
def fc (a t j n : k) : fC q := ⟨![0,a,0,0,0,0,0,t,j,n], by
  exact f_mul q ![0,a,0,0,0,0,0,t,j,n]⟩

lemma ec_eta (a : eC q) : ec q (a.val 0) (a.val 2) (a.val 3) (a.val 4) (a.val 5) (a.val 6) = a := by
  apply Subtype.ext
  exact (e_mul q a.val).symm.trans a.property

lemma fc_eta (a : fC q) : fc q (a.val 1) (a.val 7) (a.val 8) (a.val 9) = a := by
  apply Subtype.ext
  exact (f_mul q a.val).symm.trans a.property

@[simp] lemma ec_eq_zero (a b c d u v : k) : ec q a b c d u v = 0 ↔
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ u = 0 ∧ v = 0 := by
  constructor
  · intro h
    have hv := congrArg Subtype.val h
    exact ⟨congrFun hv 0, congrFun hv 2, congrFun hv 3, congrFun hv 4,
      congrFun hv 5, congrFun hv 6⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    apply Subtype.ext
    ext i
    fin_cases i <;> rfl

@[simp] lemma fc_eq_zero (a t j n : k) : fc q a t j n = 0 ↔
    a = 0 ∧ t = 0 ∧ j = 0 ∧ n = 0 := by
  constructor
  · intro h
    have hv := congrArg Subtype.val h
    exact ⟨congrFun hv 1, congrFun hv 7, congrFun hv 8, congrFun hv 9⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    apply Subtype.ext
    ext i
    fin_cases i <;> rfl

def lambdaU : fC q →ₗ[(C k q)ᵐᵒᵖ] eC q := RightCorner.mulLeft (u q) (e_mul_u q)
def lambdaEll (c : k) : eC q →ₗ[(C k q)ᵐᵒᵖ] eC q :=
  RightCorner.mulLeft (ell q c) (e_mul_ell q c)

lemma lambdaU_fc (a t j n : k) :
    lambdaU q (fc q a t j n) = ec q 0 (q*t) t j a n := by
  apply Subtype.ext
  ext i
  change mul q (u q) ![0,a,0,0,0,0,0,t,j,n] i = _
  fin_cases i <;> simp [mul, u, ec]

lemma lambdaEll_ec (z a b c d u v : k) :
    lambdaEll q z (ec q a b c d u v) = ec q 0 a (z*a) (z*b+q*c) 0 ((1+z)*u) := by
  apply Subtype.ext
  ext i
  change mul q (ell q z) ![a,0,b,c,d,u,v,0,0,0] i = _
  fin_cases i <;> simp [mul, ell, ec] <;> ring

lemma lambdaU_injective : Function.Injective (lambdaU q) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  rw [← fc_eta q x, lambdaU_fc, ec_eq_zero] at hx
  obtain ⟨_, _, ht, hj, ha, hn⟩ := hx
  rw [← fc_eta q x, fc_eq_zero]
  exact ⟨ha, ht, hj, hn⟩

variable [CharP k 2]

lemma exact_lambdaU : Function.Exact (lambdaU q) (lambdaEll q 1) := by
  intro x
  constructor
  · intro hh
    rw [← ec_eta q x, lambdaEll_ec, ec_eq_zero] at hh
    obtain ⟨_, ha, _, hbc, _, _⟩ := hh
    have hb : x.val 2 = q*x.val 3 := by
      have he := eq_neg_of_add_eq_zero_left hbc
      simpa only [one_mul, CharTwo.neg_eq] using he
    refine ⟨fc q (x.val 5) (x.val 3) (x.val 4) (x.val 6), ?_⟩
    rw [lambdaU_fc]
    have hx := ec_eta q x
    rw [ha, hb] at hx
    exact hx
  · rintro ⟨z, rfl⟩
    rw [← fc_eta q z, lambdaU_fc, lambdaEll_ec, ec_eq_zero]
    simp only [mul_zero, one_mul, CharTwo.add_self_eq_zero, zero_mul, and_self]

lemma exact_lambdaEll (hq : q ≠ 0) (z : k) (hz : 1+z ≠ 0) (hz' : 1+q*z ≠ 0) :
    Function.Exact (lambdaEll q z) (lambdaEll q (q*z)) := by
  intro x
  constructor
  · intro hh
    rw [← ec_eta q x, lambdaEll_ec, ec_eq_zero] at hh
    obtain ⟨_, ha, _, hbc, _, hu⟩ := hh
    have hu' : x.val 5 = 0 := (mul_eq_zero.mp hu).resolve_left hz'
    have hc : x.val 3 = z*x.val 2 := by
      have he : q * (z*x.val 2 + x.val 3) = 0 := by
        simpa only [_root_.mul_assoc, _root_.mul_add] using hbc
      have he' := (mul_eq_zero.mp he).resolve_left hq
      simpa only [CharTwo.neg_eq] using (eq_neg_of_add_eq_zero_right he')
    refine ⟨ec q (x.val 2) 0 (x.val 4/q) 0 (x.val 6/(1+z)) 0, ?_⟩
    rw [lambdaEll_ec]
    have hx := ec_eta q x
    rw [ha, hu', hc] at hx
    simpa only [mul_zero, zero_add, mul_div_cancel₀ _ hq, mul_div_cancel₀ _ hz] using hx
  · rintro ⟨y, rfl⟩
    rw [← ec_eta q y, lambdaEll_ec, lambdaEll_ec, ec_eq_zero]
    simp only [mul_zero, and_true, true_and]
    rw [_root_.mul_assoc, CharTwo.add_self_eq_zero]

end Tachikawa.C



namespace Tachikawa
open scoped TensorProduct

variable {k : Type*} [Field k] (q : k)

abbrev B := (C k q) ⊗[k] (C k q)

def pf : B q := C.f q ⊗ₜ[k] C.f q

end Tachikawa



namespace Tachikawa
open scoped TensorProduct
variable {k : Type*} [Field k] (q : k)

namespace C

def character : C k q →ₐ[k] k where
  toFun a := a 1
  map_one' := rfl
  map_mul' a b := rfl
  map_zero' := rfl
  map_add' a b := rfl
  commutes' r := by
    change (r • C.unit q) 1 = r
    rw [C.smul_apply]
    simp [C.unit]

@[simp] lemma character_f : character q (f q) = 1 := rfl
end C

def characterB : B q →ₐ[k] k := Algebra.TensorProduct.productMap (C.character q) (C.character q)

@[simp] lemma characterB_pf : characterB q (pf q) = 1 := by
  simp [characterB, pf, Algebra.TensorProduct.productMap]

end Tachikawa



namespace Tachikawa.C
variable {k : Type*} [Field k] (q : k)

def Simple (_q : k) := k
instance instAddCommGroupSimple : AddCommGroup (Simple q) := inferInstanceAs (AddCommGroup k)
instance instModuleSimple : Module k (Simple q) := inferInstanceAs (Module k k)
instance instModuleSimple_1 : Module (C k q) (Simple q) := Module.compHom (Simple q) (character q).toRingHom
instance instIsScalarTowerSimple : IsScalarTower k (C k q) (Simple q) :=
  IsScalarTower.of_algebraMap_smul fun r x => by
    change (character q (algebraMap k (C k q) r)) • x = r • x
    rw [AlgHom.commutes]
    rfl
instance instFiniteDimensionalSimple : FiniteDimensional k (Simple q) := inferInstanceAs (FiniteDimensional k k)

@[simp] lemma simple_smul (a : C k q) (x : Simple q) : a • x = (a 1 : k) • x := rfl

@[simp] lemma e_smul_simple (x : Simple q) : e q • x = 0 := by
  change (0 : k) • x = 0
  exact zero_smul k x

@[simp] lemma f_smul_simple (x : Simple q) : f q • x = x := by
  change (1 : k) • x = x
  exact one_smul k x

def augmentation : Cf q →ₗ[C k q] Simple q where
  toFun a := a.val 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma augmentation_cf (a u v n : k) : augmentation q (cf q a u v n) = a := rfl

lemma augmentation_surjective : Function.Surjective (augmentation q) :=
  fun x => ⟨cf q x 0 0 0, rfl⟩

lemma augmentation_rhoU : (augmentation q).comp (rhoU q) = 0 := by
  ext x
  rw [LinearMap.comp_apply, ← ce_eta q x, rhoU_ce]
  rfl

lemma exact_augmentation (hq : 1+q ≠ 0) : Function.Exact (rhoU q) (augmentation q) := by
  intro x
  constructor
  · intro h
    refine ⟨ce q (x.val 5) (x.val 6) 0 0 (x.val 9 / (1+q)) 0, ?_⟩
    rw [rhoU_ce]
    have hx := cf_eta q x
    change x.val 1 = 0 at h
    rw [h] at hx
    simpa only [add_zero, mul_div_cancel₀ _ hq] using hx
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun (augmentation_rhoU q) y

lemma homCeSimple_zero (F : Ce q →ₗ[C k q] Simple q) : F = 0 := by
  apply LeftCorner.hom_ext (e_idempotent q)
  have h := LeftCorner.generator_fixed (e_idempotent q) F
  rw [e_smul_simple] at h
  exact h.symm

instance instSubsingletonLinearMapIdSubtypeMemSubmoduleCeSimple : Subsingleton (Ce q →ₗ[C k q] Simple q) :=
  ⟨fun F G => (homCeSimple_zero q F).trans (homCeSimple_zero q G).symm⟩

end Tachikawa.C



namespace Tachikawa.C
open CategoryTheory
variable {k : Type*} [Field k] [CharP k 2] (q : k)

def resObj : ℕ → ModuleCat (C k q)
  | 0 => ModuleCat.of (C k q) (Cf q)
  | _+1 => ModuleCat.of (C k q) (Ce q)

def resD : ∀ n, resObj q (n+1) ⟶ resObj q n
  | 0 => ModuleCat.ofHom (rhoU q)
  | n+1 => ModuleCat.ofHom (rhoEll q (q^n))

lemma resD_exact (hq : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (n : ℕ) :
    Function.Exact (resD q (n+1)) (resD q n) := by
  cases n with
  | zero =>
    change Function.Exact (rhoEll q (q^0)) (rhoU q)
    simpa only [pow_zero] using exact_rhoU q (by simpa only [pow_one] using hq 1 (by omega))
      (hq 2 (by omega))
  | succ n =>
    change Function.Exact (rhoEll q (q^(n+1))) (rhoEll q (q^n))
    rw [pow_succ']
    apply exact_rhoEll
    · rw [← pow_add]
      exact hq (2+n) (by omega)
    · rw [← pow_succ', ← pow_add]
      exact hq (2+(n+1)) (by omega)

end Tachikawa.C



namespace Tachikawa.C
open CategoryTheory
variable {k : Type} [Field k] [CharP k 2] (q : k)

lemma dualTwoCycle_coords (hq : q ≠ 0) (hq1 : 1+q ≠ 0)
    (a : LinearMap.ker (lambdaEll q q)) :
    a.val.val 0 = 0 ∧ a.val.val 3 = a.val.val 2 ∧ a.val.val 5 = 0 := by
  have h : lambdaEll q q a.val = 0 := a.property
  rw [← ec_eta q a.val, lambdaEll_ec, ec_eq_zero] at h
  obtain ⟨_, h0, _, h23, _, h5⟩ := h
  refine ⟨h0, ?_, (mul_eq_zero.mp h5).resolve_left hq1⟩
  have h23' : a.val.val 2 + a.val.val 3 = 0 := by
    apply (mul_eq_zero.mp _).resolve_left hq
    simpa only [_root_.mul_add] using h23
  simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_right h23'

local instance instHasQuotientSubtypeMemSubmoduleMulOppositeECKerLambdaEll_r037161_1 : HasQuotient (LinearMap.ker (lambdaEll q q))
    (Submodule (C k q)ᵐᵒᵖ (LinearMap.ker (lambdaEll q q))) :=
  @Submodule.hasQuotient (C k q)ᵐᵒᵖ (LinearMap.ker (lambdaEll q q))
    inferInstance inferInstance inferInstance
lemma dualComplex_exact (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (n : ℕ) :
    Function.Exact (lambdaEll q (q^(n+1))) (lambdaEll q (q^(n+2))) := by
  have he : q^(n+2) = q*q^(n+1) := pow_succ' q (n+1)
  rw [he]
  exact exact_lambdaEll q hq (q^(n+1)) (hp _ (by omega)) (by
    rw [← pow_succ']
    exact hp _ (by omega))

end Tachikawa.C



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Period
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
open CategoryTheory
open CategoryTheory.Abelian
variable {C : Type*} [Category C] [Abelian C] [HasExt C]
variable (k : Type*) [CommRing k] [Linear k C]

def extShiftEquiv {S : ShortComplex C} (hS : S.ShortExact) (Y : C) (n : ℕ)
    [Subsingleton (Ext S.X₂ Y n)] [Subsingleton (Ext S.X₂ Y (n+1))] :
    Ext S.X₁ Y n ≃ₗ[k] Ext S.X₃ Y (n+1) :=
  LinearEquiv.ofBijective (hS.extClass.precompOfLinear k Y (by omega)) (by
    constructor
    · apply LinearMap.ker_eq_bot.mp
      apply LinearMap.ker_eq_bot'.mpr
      intro x hx
      obtain ⟨y,hy⟩ := Ext.contravariant_sequence_exact₁ hS Y x (by omega) hx
      rw [Subsingleton.elim y 0, Ext.comp_zero] at hy
      exact hy.symm
    · intro x
      exact Ext.contravariant_sequence_exact₃ hS Y x (Subsingleton.elim _ _) (by omega))

def extQuotientEquiv {S : ShortComplex C} (hS : S.ShortExact) (Y : C)
    (h : ∀ n : ℕ, Subsingleton (Ext S.X₁ Y n)) (n : ℕ) :
    Ext S.X₃ Y n ≃ₗ[k] Ext S.X₂ Y n :=
  LinearEquiv.ofBijective ((Ext.mk₀ S.g).precompOfLinear k Y (zero_add n)) (by
    constructor
    · cases n with
      | zero =>
        let : Epi S.g := hS.epi_g
        exact Ext.precomp_mk₀_injective_of_epi Y S.g
      | succ n =>
        apply LinearMap.ker_eq_bot.mp
        apply LinearMap.ker_eq_bot'.mpr
        intro x hx
        obtain ⟨y,hy⟩ := Ext.contravariant_sequence_exact₃ hS Y x hx (n₀ := n) (by omega)
        let := h n
        rw [Subsingleton.elim y 0, Ext.comp_zero] at hy
        exact hy.symm
    · intro x
      let := h n
      exact Ext.contravariant_sequence_exact₂ hS Y x (Subsingleton.elim _ _))

end Tachikawa



namespace Tachikawa
open CategoryTheory
universe u v
variable {R : Type u} [Ring R]
variable {M N P : Type v} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module R M] [Module R N] [Module R P]

def linearShortComplex (f : M →ₗ[R] N) (g : N →ₗ[R] P) (h : Function.Exact f g) :
    ShortComplex (ModuleCat R) :=
  ShortComplex.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g)
    (ModuleCat.hom_ext h.linearMap_comp_eq_zero)

lemma linearShortExact (f : M →ₗ[R] N) (g : N →ₗ[R] P) (h : Function.Exact f g)
    (hf : Function.Injective f) (hg : Function.Surjective g) :
    (linearShortComplex f g h).ShortExact := by
  have hm : Mono (linearShortComplex f g h).f := (ModuleCat.mono_iff_injective _).mpr hf
  have he : Epi (linearShortComplex f g h).g := (ModuleCat.epi_iff_surjective _).mpr hg
  exact ⟨(ShortComplex.moduleCat_exact_iff _).mpr (fun x => (h x).mp)⟩

end Tachikawa



namespace Tachikawa.RightCorner
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {p : R} (hp : p*p=p)

def homEquivScalar : (LeftCorner p →ₗ[R] R) ≃ₗ[k] RightCorner p where
  toEquiv := (homEquiv hp).toEquiv
  map_add' := (homEquiv hp).map_add
  map_smul' _ _ := Subtype.ext rfl

end Tachikawa.RightCorner



namespace Tachikawa.C
variable {k : Type} [Field k] [CharP k 2] (q : k)

def v : C k q := ![0,0,0,0,0,0,1,0,0,0]
omit [CharP k 2] in
lemma e_mul_v : e q * v q = v q := by rw [e_mul]; rfl

def vHom : Ce q →ₗ[C k q] C k q := LeftCorner.lift (v q) (e_mul_v q)

omit [CharP k 2] in
lemma vHom_generator : vHom q (LeftCorner.generator (e_idempotent q)) = v q :=
  LeftCorner.lift_generator (e_idempotent q) _ _

lemma lambdaEll_one_six (a : eC q) : (lambdaEll q 1 a).val 6 = 0 := by
  rw [← ec_eta q a, lambdaEll_ec]
  change (1+1:k) * _ = 0
  rw [CharTwo.add_self_eq_zero, zero_mul]

end Tachikawa.C



namespace Tachikawa.C
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

lemma exact_rhoEll_one (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    Function.Exact (rhoEll q q) (rhoEll q 1) := by
  have h := resD_exact q hp 1
  change Function.Exact (rhoEll q (q^1)) (rhoEll q (q^0)) at h
  simpa only [pow_one, pow_zero] using h

end Tachikawa.C



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Socle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa
open scoped TensorProduct
namespace Construction
variable {k : Type*} [Field k] (q : k)

def X (_q : k) := k
instance instAddCommGroupX : AddCommGroup (X q) := inferInstanceAs (AddCommGroup k)
instance instModuleX : Module k (X q) := inferInstanceAs (Module k k)

end Construction
end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_ReverseResolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.C
open CategoryTheory
variable {k : Type} [Field k] (q : k)

lemma one_add_inv_power_ne_zero (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
    (n : ℕ) (hn : 0 < n) : 1+(q^n)⁻¹ ≠ 0 := by
  intro h
  have he : (q^n)⁻¹ = -1 := eq_neg_of_add_eq_zero_right h
  have he' := congrArg Inv.inv he
  simp only [inv_inv, inv_neg, inv_one] at he'
  exact hp n hn (by rw [he', add_neg_cancel])

end Tachikawa.C



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
variable {R : Type*} [Ring R]

lemma shortComplex_quasiIso_of_cycles {S T : ShortComplex (ModuleCat R)} (φ : S ⟶ T)
    (hinj : ∀ x : S.X₂, S.g x = 0 →
      (∃ z : T.X₁, T.f z = φ.τ₂ x) → ∃ z : S.X₁, S.f z = x)
    (hsurj : ∀ y : T.X₂, T.g y = 0 →
      ∃ x : S.X₂, S.g x = 0 ∧ ∃ z : T.X₁, T.f z = φ.τ₂ x-y) :
    ShortComplex.QuasiIso φ := by
  let f : LinearMap.ker S.g.hom →ₗ[R] LinearMap.ker T.g.hom :=
    (φ.τ₂.hom.comp (LinearMap.ker S.g.hom).subtype).codRestrict _ (by
      intro x
      change T.g (φ.τ₂ x.val) = 0
      rw [← ModuleCat.comp_apply, φ.comm₂₃, ModuleCat.comp_apply, x.property, map_zero])
  have hf : LinearMap.range S.moduleCatToCycles ≤
      (LinearMap.range T.moduleCatToCycles).comap f := by
    rintro x ⟨a,rfl⟩
    refine ⟨φ.τ₁ a, ?_⟩
    apply Subtype.ext
    exact congrArg (fun t : S.X₁ ⟶ T.X₂ => t a) φ.comm₁₂
  let fq := Submodule.mapQ (LinearMap.range S.moduleCatToCycles)
    (LinearMap.range T.moduleCatToCycles) f hf
  let γ : ShortComplex.LeftHomologyMapData φ S.moduleCatLeftHomologyData
      T.moduleCatLeftHomologyData := {
    φK := ModuleCat.ofHom f
    φH := ModuleCat.ofHom fq
    commi := rfl
    commf' := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact (congrArg (fun t : S.X₁ ⟶ T.X₂ => t x) φ.comm₁₂).symm
    commπ := rfl }
  rw [γ.quasiIso_iff]
  apply (ConcreteCategory.isIso_iff_bijective _).2
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    obtain ⟨x,rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change Submodule.Quotient.mk (f x) = 0 at hx
    obtain ⟨z,hz⟩ := (Submodule.Quotient.mk_eq_zero _).mp hx
    have hz' : T.f z = φ.τ₂ x.val := congrArg Subtype.val hz
    obtain ⟨a,ha⟩ := hinj x.val x.property ⟨z,hz'⟩
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact ⟨a, Subtype.ext ha⟩
  · intro y
    obtain ⟨y,rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨x,hx,z,hz⟩ := hsurj y.val y.property
    refine ⟨Submodule.Quotient.mk ⟨x,hx⟩, ?_⟩
    change Submodule.Quotient.mk (f ⟨x,hx⟩) = Submodule.Quotient.mk y
    apply (Submodule.Quotient.eq _).mpr
    exact ⟨z, Subtype.ext hz⟩

lemma shortComplex_cycles_of_quasiIso {S T : ShortComplex (ModuleCat R)} (φ : S ⟶ T)
    (hφ : ShortComplex.QuasiIso φ) :
    (∀ x : S.X₂, S.g x = 0 →
      (∃ z : T.X₁, T.f z = φ.τ₂ x) → ∃ z : S.X₁, S.f z = x) ∧
    (∀ y : T.X₂, T.g y = 0 →
      ∃ x : S.X₂, S.g x = 0 ∧ ∃ z : T.X₁, T.f z = φ.τ₂ x-y) := by
  let f : LinearMap.ker S.g.hom →ₗ[R] LinearMap.ker T.g.hom :=
    (φ.τ₂.hom.comp (LinearMap.ker S.g.hom).subtype).codRestrict _ (by
      intro x
      change T.g (φ.τ₂ x.val) = 0
      rw [← ModuleCat.comp_apply, φ.comm₂₃, ModuleCat.comp_apply, x.property, map_zero])
  have hf : LinearMap.range S.moduleCatToCycles ≤
      (LinearMap.range T.moduleCatToCycles).comap f := by
    rintro x ⟨a,rfl⟩
    refine ⟨φ.τ₁ a, ?_⟩
    apply Subtype.ext
    exact congrArg (fun t : S.X₁ ⟶ T.X₂ => t a) φ.comm₁₂
  let fq := Submodule.mapQ (LinearMap.range S.moduleCatToCycles)
    (LinearMap.range T.moduleCatToCycles) f hf
  let γ : ShortComplex.LeftHomologyMapData φ S.moduleCatLeftHomologyData
      T.moduleCatLeftHomologyData := {
    φK := ModuleCat.ofHom f
    φH := ModuleCat.ofHom fq
    commi := rfl
    commf' := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact (congrArg (fun t : S.X₁ ⟶ T.X₂ => t x) φ.comm₁₂).symm
    commπ := rfl }
  have hbij : Function.Bijective fq := by
    have : IsIso γ.φH := γ.quasiIso_iff.mp hφ
    exact (ConcreteCategory.isIso_iff_bijective γ.φH).mp this
  constructor
  · intro x hx hbd
    have hz : fq (Submodule.Quotient.mk (⟨x,hx⟩ : LinearMap.ker S.g.hom)) = 0 := by
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      obtain ⟨z,hz⟩ := hbd
      exact ⟨z, Subtype.ext hz⟩
    have hz' := hbij.1 (hz.trans (map_zero fq).symm)
    obtain ⟨z,hz⟩ := (Submodule.Quotient.mk_eq_zero _).mp hz'
    exact ⟨z, congrArg Subtype.val hz⟩
  · intro y hy
    obtain ⟨x,hx⟩ := hbij.2 (Submodule.Quotient.mk (⟨y,hy⟩ : LinearMap.ker T.g.hom))
    obtain ⟨x,rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change Submodule.Quotient.mk (f x) = Submodule.Quotient.mk ⟨y,hy⟩ at hx
    obtain ⟨z,hz⟩ := (Submodule.Quotient.eq _).mp hx
    exact ⟨x.val, x.property, z, congrArg Subtype.val hz⟩

end Tachikawa



end


namespace Tachikawa

instance downIntTensorSigns : ComplexShape.TensorSigns (ComplexShape.down ℤ) where
  ε' := MonoidHom.mk' Int.negOnePow Int.negOnePow_add
  rel_add p q r (hpq : q+1=p) := by
    change q + r + 1 = p + r
    omega
  add_rel p q r (hpq : q+1=p) := by
    change r + q + 1 = r + p
    omega
  ε'_succ := by
    rintro _ q rfl
    change Int.negOnePow q = -Int.negOnePow (q + 1)
    rw [Int.negOnePow_succ, neg_neg]
end Tachikawa



noncomputable section



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
variable {R : Type} [Ring R] {ι : Type}

def coproductSupportIso (F : ι → ModuleCat R) (p : ι → Prop)
    (hz : ∀ i, ¬p i → IsZero (F i)) : (∐ F) ≅ ∐ (fun i : {i // p i} => F i.val) := by
  classical
  refine {
    hom := Sigma.desc fun i => if h : p i then Sigma.ι (fun i : {i // p i} => F i.val) ⟨i,h⟩ else 0
    inv := Sigma.desc fun i => Sigma.ι F i.val
    hom_inv_id := ?_
    inv_hom_id := ?_ }
  · apply Sigma.hom_ext
    intro i
    rw [Sigma.ι_desc_assoc]
    by_cases h : p i
    · simp only [dite_eq_left h, Sigma.ι_desc, Category.comp_id]
    · simp only [dite_eq_right h, zero_comp, Category.comp_id]
      exact (hz i h).eq_of_src _ _
  · apply Sigma.hom_ext
    intro i
    simp only [Sigma.ι_desc_assoc, Sigma.ι_desc, dite_eq_left i.property, Category.comp_id]

lemma coproduct_finite_of_support (F : ι → ModuleCat R) (p : ι → Prop)
    [Finite {i // p i}] (hz : ∀ i, ¬p i → IsZero (F i))
    (hf : ∀ i, Module.Finite R (F i)) : Module.Finite R (∐ F : ModuleCat R) := by
  let (i : {i // p i}) : Module.Finite R (F i.val) := hf i.val
  let J := fun i : {i // p i} => F i.val
  exact Module.Finite.equiv (((coproductSupportIso F p hz) ≪≫
    (biproduct.isoCoproduct J).symm ≪≫ ModuleCat.biproductIsoPi J).toLinearEquiv.symm)

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Bimodule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa
open CategoryTheory HomologicalComplex
variable {R : Type} [Ring R]

namespace ModuleFiber
variable {K L : ChainComplex (ModuleCat R) ℤ} (f : K ⟶ L)

def obj (_f : K ⟶ L) (j : ℤ) : ModuleCat R := ModuleCat.of R (L.X (j+1) × K.X j)

def differential (j : ℤ) : obj f (j+1) ⟶ obj f j :=
  ModuleCat.ofHom <|
    (((L.d (j+1+1) (j+1)).hom.comp (LinearMap.fst R _ _) +
        (f.f (j+1)).hom.comp (LinearMap.snd R _ _)).prod
      (-((K.d (j+1) j).hom.comp (LinearMap.snd R _ _))))

lemma differential_comp (j : ℤ) : differential f (j+1) ≫ differential f j = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · change L.d (j+1+1) (j+1) (L.d (j+1+1+1) (j+1+1) x.1 +
        f.f (j+1+1) x.2) + f.f (j+1) (-K.d (j+1+1) (j+1) x.2) = 0
    rw [map_add, map_neg]
    have hz := congrArg (fun a : L.X (j+1+1+1) ⟶ L.X (j+1) => a x.1)
      (L.d_comp_d (j+1+1+1) (j+1+1) (j+1))
    have hc := congrArg (fun a : K.X (j+1+1) ⟶ L.X (j+1) => a x.2)
      (f.comm (j+1+1) (j+1))
    change L.d (j+1+1) (j+1) (L.d (j+1+1+1) (j+1+1) x.1) = 0 at hz
    change L.d (j+1+1) (j+1) (f.f (j+1+1) x.2) =
      f.f (j+1) (K.d (j+1+1) (j+1) x.2) at hc
    rw [hz, zero_add, hc, add_neg_cancel]
  · change -K.d (j+1) j (-K.d (j+1+1) (j+1) x.2) = 0
    rw [map_neg, neg_neg]
    exact congrArg (fun a : K.X (j+1+1) ⟶ K.X j => a x.2)
      (K.d_comp_d (j+1+1) (j+1) j)

def complex : ChainComplex (ModuleCat R) ℤ :=
  ChainComplex.of (obj f) (differential f) (differential_comp f)

@[simp] lemma complex_d (j : ℤ) : (complex f).d (j+1) j = differential f j :=
  ChainComplex.of_d _ _ j

lemma differential_exact [QuasiIso f] (j : ℤ) :
    Function.Exact (differential f (j+1)) (differential f j) := by
  have hqi (n : ℤ) := (quasiIsoAt_iff' f (n+1) n (n-1) (by simp) (by simp)).mp
    (inferInstance : QuasiIsoAt f n)
  have hc (n : ℤ) := shortComplex_cycles_of_quasiIso _ (hqi n)
  intro x
  constructor
  · intro hx
    have hx₁ : L.d (j+1+1) (j+1) x.1 + f.f (j+1) x.2 = 0 := congrArg Prod.fst hx
    have hx₂ : K.d (j+1) j x.2 = 0 := neg_eq_zero.mp (congrArg Prod.snd hx)
    have hx₂' : K.d (j+1) (j+1-1) x.2 = 0 := by
      rw [show j+1-1 = j by omega]
      exact hx₂
    obtain ⟨s,hs⟩ := (hc (j+1)).1 x.2 hx₂' ⟨-x.1, by
      change L.d (j+1+1) (j+1) (-x.1) = f.f (j+1) x.2
      rw [map_neg]
      exact (eq_neg_of_add_eq_zero_right hx₁).symm⟩
    change K.X (j+1+1) at s
    change K.d (j+1+1) (j+1) s = x.2 at hs
    have hy : L.d (j+1+1) (j+1+1-1) (x.1 + f.f (j+1+1) s) = 0 := by
      rw [show j+1+1-1 = j+1 by omega, map_add]
      have hh := congrArg (fun a : K.X (j+1+1) ⟶ L.X (j+1) => a s)
        (f.comm (j+1+1) (j+1))
      change L.d (j+1+1) (j+1) (f.f (j+1+1) s) =
        f.f (j+1) (K.d (j+1+1) (j+1) s) at hh
      rw [hh, hs]
      exact hx₁
    obtain ⟨t,ht,u,hu⟩ := (hc (j+1+1)).2 (x.1 + f.f (j+1+1) s) hy
    change K.X (j+1+1) at t
    change L.X (j+1+1+1) at u
    change K.d (j+1+1) (j+1+1-1) t = 0 at ht
    rw [show j+1+1-1 = j+1 by omega] at ht
    change L.d (j+1+1+1) (j+1+1) u =
      f.f (j+1+1) t - (x.1 + f.f (j+1+1) s) at hu
    refine ⟨(-u,-s+t), ?_⟩
    apply Prod.ext
    · change L.d (j+1+1+1) (j+1+1) (-u) + f.f (j+1+1) (-s+t) = x.1
      rw [map_neg, map_add, map_neg, hu]
      abel
    · change -K.d (j+1+1) (j+1) (-s+t) = x.2
      rw [map_add,map_neg,hs,ht,add_zero,neg_neg]
  · rintro ⟨y,rfl⟩
    exact congrArg (fun a : obj f (j+1+1) ⟶ obj f j => a y) (differential_comp f j)

lemma exact [QuasiIso f] : ComplexExact (complex f) := by
  intro j
  obtain ⟨i,rfl⟩ : ∃ i : ℤ, j = i+1 := ⟨j-1, by omega⟩
  rw [show i+1-1 = i by omega, complex_d, complex_d]
  exact differential_exact f i

lemma totallyAcyclic [QuasiIso f] [Module.Injective R R] : TotallyAcyclic (complex f) := by
  refine ⟨exact f, ?_⟩
  intro j g hg
  obtain ⟨h,hh⟩ := Module.Injective.extension_property R R
    (CokerAt (complex f) j) ((complex f).X (j-1))
    (CokerAt.ι (complex f) j) (CokerAt.ι_injective _ _ (exact f j))
    (CokerAt.descend _ _ g hg)
  refine ⟨h, ?_⟩
  have hh' := congrArg (fun a => a.comp (CokerAt.π (complex f) j)) hh
  simpa only [LinearMap.comp_assoc, CokerAt.ι_comp_π, CokerAt.descend_comp_π] using hh'

end ModuleFiber
end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex
variable {R : Type} [Ring R]

namespace NatCoker
variable (P : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
abbrev C := P.X (n+1) ⧸ LinearMap.range (P.d (n+2) (n+1)).hom

def π : P.X (n+1) →ₗ[R] C P n := (LinearMap.range (P.d (n+2) (n+1)).hom).mkQ

end NatCoker
end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_RightInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
open CategoryTheory
variable {R : Type} [Ring R]

lemma exact_prodMap {A B C D E F : Type} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [AddCommGroup D] [AddCommGroup E] [AddCommGroup F]
    [Module R A] [Module R B] [Module R C] [Module R D] [Module R E] [Module R F]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (f' : D →ₗ[R] E) (g' : E →ₗ[R] F)
    (h : Function.Exact f g) (h' : Function.Exact f' g') :
    Function.Exact (f.prodMap f') (g.prodMap g') := by
  rintro ⟨b,e⟩
  change (g b,g' e) = (0,0) ↔ _
  rw [Prod.mk.injEq]
  constructor
  · rintro ⟨hb,he⟩
    obtain ⟨a,rfl⟩ := (h b).mp hb
    obtain ⟨d,rfl⟩ := (h' e).mp he
    exact ⟨(a,d),rfl⟩
  · rintro ⟨⟨a,d⟩,hh⟩
    cases hh
    exact ⟨h.apply_apply_eq_zero a,h'.apply_apply_eq_zero d⟩

namespace ProjectiveResolution
variable {M N : ModuleCat.{0} R} (P : CategoryTheory.ProjectiveResolution M)
    (Q : CategoryTheory.ProjectiveResolution N)

lemma function_exact_succ (n : ℕ) :
    Function.Exact (P.complex.d (n+2) (n+1)) (P.complex.d (n+1) n) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (P.exact_succ n)

lemma function_exact_zero : Function.Exact (P.complex.d 1 0) (P.π.f 0) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp P.exact₀

end ProjectiveResolution
end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

namespace ProjectiveResolution
variable (M : ModuleCat.{0} R) [Projective M]

def simpleTerm : ℕ → ModuleCat R
  | 0 => M
  | _+1 => ModuleCat.of R PUnit

def simpleAug : simpleTerm M 0 ⟶ M := 𝟙 M

end ProjectiveResolution
end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Perfect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.NatCoker
open CategoryTheory HomologicalComplex
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {P Q S : ChainComplex (ModuleCat.{0} R) ℕ}

def map (f : P ⟶ Q) (n : ℕ) : C P n →ₗ[R] C Q n :=
  (LinearMap.range (P.d (n+2) (n+1)).hom).liftQ ((π Q n).comp (f.f (n+1)).hom) (by
    rintro _ ⟨x,rfl⟩
    change π Q n (f.f (n+1) (P.d (n+2) (n+1) x)) = 0
    have h := congrArg (fun g : P.X (n+2) ⟶ Q.X (n+1) => g x) (f.comm (n+2) (n+1)).symm
    change f.f (n+1) (P.d (n+2) (n+1) x) = Q.d (n+2) (n+1) (f.f (n+2) x) at h
    rw [h]
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨_,rfl⟩)

end Tachikawa.NatCoker



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_DownHom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
namespace CompleteTranslate

abbrev complex (P : ChainComplex (ModuleCat.{0} R) ℤ) (a : ℤ) :
    ChainComplex (ModuleCat.{0} R) ℤ where
  X i := P.X (i+a)
  d i j := P.d (i+a) (j+a)
  shape i j h := P.shape _ _ (by
    intro he
    apply h
    change j+1=i
    change j+a+1=i+a at he
    omega)
  d_comp_d' i j l _ _ := P.d_comp_d _ _ _

end CompleteTranslate
end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Cone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
variable {R : Type} [Ring R]
namespace CompleteCone
variable {A B : ChainComplex (ModuleCat.{0} R) ℤ} (v : B ⟶ A)
abbrev complex := HomologicalComplex.homotopyCofiber v
lemma rel (j : ℤ) : (ComplexShape.down ℤ).Rel j (j-1) := by
  change j-1+1=j; omega
abbrev left (j : ℤ) : (complex v).X j ⟶ B.X (j-1) :=
  HomologicalComplex.homotopyCofiber.fstX v j (j-1) (rel j)
abbrev right (j : ℤ) : (complex v).X j ⟶ A.X j :=
  HomologicalComplex.homotopyCofiber.sndX v j
abbrev inLeft (j : ℤ) : B.X (j-1) ⟶ (complex v).X j :=
  HomologicalComplex.homotopyCofiber.inlX v (j-1) j (rel j)
abbrev inRight (j : ℤ) : A.X j ⟶ (complex v).X j :=
  HomologicalComplex.homotopyCofiber.inrX v j

@[simp] lemma inLeft_left (j : ℤ) : inLeft v j ≫ left v j = 𝟙 _ := by
  apply HomologicalComplex.homotopyCofiber.inlX_fstX
@[simp] lemma inLeft_right (j : ℤ) : inLeft v j ≫ right v j = 0 := by
  apply HomologicalComplex.homotopyCofiber.inlX_sndX
@[simp] lemma inRight_left (j : ℤ) : inRight v j ≫ left v j = 0 := by
  apply HomologicalComplex.homotopyCofiber.inrX_fstX
@[simp] lemma inRight_right (j : ℤ) : inRight v j ≫ right v j = 𝟙 _ := by
  apply HomologicalComplex.homotopyCofiber.inrX_sndX

def termEquiv (j : ℤ) : (complex v).X j ≃ₗ[R] (B.X (j-1) × A.X j) :=
  (HomologicalComplex.homotopyCofiber.XIsoBiprod v j (j-1) (rel j) ≪≫
    ModuleCat.biprodIsoProd (B.X (j-1)) (A.X j)).toLinearEquiv

end CompleteCone
end Tachikawa



namespace Tachikawa.DownCone
open CategoryTheory CategoryTheory.Preadditive CategoryTheory.Limits HomologicalComplex
open scoped ModuleCat.Algebra
open CompleteCone
variable {k R : Type} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable {A B : ChainComplex (ModuleCat.{0} R) ℤ} (v : B ⟶ A)
abbrev C := complex v

end Tachikawa.DownCone



end

end OAI
end


