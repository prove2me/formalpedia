-- Prove2me | Definitions.Def_AlgebraicGeometry_FilteredColimitExtDetection
-- name    : AlgebraicGeometry_FilteredColimitExtDetection
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-26T07:42:31.011012+00:00
-- url     : https://prove2.me/theorems/6ab32915-4239-4ea3-b9ce-889d969973b6
-- title:
--   Lifting and detecting Ext through filtered colimits
-- statement:
--   Under degree-zero lifting on slice Homs and acyclicity for filtered colimits of injectives, higher Ext classes lift to finite stages and equality is detected at a later stage.
-- source:
--   Stacks Project, Section 59.83, https://stacks.math.columbia.edu/tag/03SB.

import Definitions.Def_AlgebraicGeometry_EtaleCohomologyRestriction
import Definitions.Def_AlgebraicGeometry_EtaleOpenCoefficientComparison
import Definitions.Def_AlgebraicGeometry_EtaleStrictLocalSectionGerms
import Definitions.Def_AlgebraicGeometry_FreeEtaleChartSheaves
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.FiveLemma
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ColimCoyoneda
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.ObjectProperty.Ind
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Presentable.Finite
import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.Tactic.FinCases

noncomputable section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian

universe siteU

local instance (priority := 2000) filteredColimitExtDetectionHasSheafify (X : Scheme.{siteU}) :
    HasSheafify X.smallEtaleTopology AddCommGrpCat.{siteU} := inferInstance

local instance (priority := 2000) filteredColimitExtDetectionHasExt (X : Scheme.{siteU}) :
    HasExt.{siteU} (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

local instance (priority := 2000) filteredColimitExtDetectionEnoughInjectives (X : Scheme.{siteU}) :
    EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits


namespace PhilipponFilteredColimitExtLifting

universe u v w

variable {J : Type u} [Category.{u} J] {C : Type w} [Category.{v} C]

/-- Every diagram embeds in a diagram of injective objects. At each index,
take the product of injective extensions at the targets of its outgoing arrows. -/
theorem exists_stagewise_injective_extension [EnoughInjectives C] [HasProducts.{u} C]
    (F : J ⥤ C) : ∃ (G : J ⥤ C) (f : F ⟶ G), (∀ i, Mono (f.app i)) ∧ ∀ i, Injective (G.obj i) := by
  let I (i : J) := Classical.choice (EnoughInjectives.presentation (F.obj i))
  let K (i : J) (a : Σ j : J, i ⟶ j) : C := (I a.1).J
  let proj (i j : J) (a : i ⟶ j) : (∏ᶜ K i) ⟶ (I j).J := Pi.π (K i) ⟨j, a⟩
  let G : J ⥤ C :=
    { obj := fun i => ∏ᶜ K i
      map := fun {i j} p => Pi.lift (f := K j) fun a => proj i a.1 (p ≫ a.2)
      map_id := fun i => Pi.hom_ext _ _ fun ⟨j, a⟩ => by
        simp only [Pi.lift_π, Category.id_comp]
        rfl
      map_comp := fun {i j _} p q => Pi.hom_ext _ _ fun a => by
        simp only [Category.assoc, Pi.lift_π]
        change proj i a.1 (p ≫ q ≫ a.2) =
          (Pi.lift (f := K j) fun b => proj i b.1 (p ≫ b.2)) ≫ Pi.π (K j) ⟨a.1, q ≫ a.2⟩
        rw [Pi.lift_π] }
  let f : F ⟶ G :=
    { app := fun i => Pi.lift fun a => F.map a.2 ≫ (I a.1).f
      naturality := fun _ _ p => Pi.hom_ext _ _ fun a => by simp [G, proj, Category.assoc] }
  refine ⟨G, f, fun i => ?_, fun i => ?_⟩
  · have hi : f.app i ≫ Pi.π (K i) ⟨i, 𝟙 i⟩ = (I i).f := by
      simp [f]
    exact mono_of_mono_fac hi
  · let (a : Σ j : J, i ⟶ j) : Injective (K i a) := (I a.1).injective
    change Injective (∏ᶜ K i)
    infer_instance

variable [Abelian C] [HasExt.{u} C] [EnoughInjectives C] [HasProducts.{u} C]
  [HasColimitsOfShape J C] [HasExactColimitsOfShape J C]

/-- If degree-zero classes lift to a stage and colimits of stagewise
injectives are acyclic, the same lifting holds in every degree. -/
theorem exists_preimage (P : C)
    (h₀ : ∀ (F : J ⥤ C) (x : Ext P (colimit F) 0),
      ∃ (i : J) (y : Ext P (F.obj i) 0), y.comp (Ext.mk₀ (colimit.ι F i)) rfl = x)
    (hA : ∀ (F : J ⥤ C) (_ : ∀ j, Injective (F.obj j)) (n : ℕ),
      Subsingleton (Ext P (colimit F) (n + 1)))
    (F : J ⥤ C) (n : ℕ) (x : Ext P (colimit F) n) :
    ∃ (i : J) (y : Ext P (F.obj i) n), y.comp (Ext.mk₀ (colimit.ι F i)) (add_zero n) = x := by
  induction n generalizing F with
  | zero => exact h₀ F x
  | succ n ih =>
    obtain ⟨G, f, hMono, hInjective⟩ := exists_stagewise_injective_extension F
    let : Mono f := NatTrans.mono_of_mono_app f
    let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
    let hS : S.ShortExact := ⟨ShortComplex.exact_cokernel f⟩
    let L : (J ⥤ C) ⥤ C := colim
    let T := S.map L
    let hT := hS.map_of_exact L
    have hx : x.comp (Ext.mk₀ T.f) (add_zero (n + 1)) = 0 :=
      (hA G hInjective n).elim _ _
    obtain ⟨v, hv⟩ := Ext.covariant_sequence_exact₁ P hT x hx rfl
    obtain ⟨j, w, hw⟩ := ih S.X₃ v
    let E := (evaluation J C).obj j
    let U := S.map E
    let hU := hS.map_of_exact E
    let ρ : U ⟶ T :=
      { τ₁ := colimit.ι S.X₁ j
        τ₂ := colimit.ι S.X₂ j
        τ₃ := colimit.ι S.X₃ j
        comm₁₂ := colimit.ι_map S.f j
        comm₂₃ := colimit.ι_map S.g j }
    refine ⟨j, w.comp hU.extClass rfl, ?_⟩
    change (w.comp hU.extClass rfl).comp (Ext.mk₀ ρ.τ₁) (add_zero (n + 1)) = x
    rw [Ext.comp_assoc_of_third_deg_zero, hU.extClass_naturality hT ρ,
      ← Ext.comp_assoc_of_second_deg_zero, show w.comp (Ext.mk₀ ρ.τ₃) (add_zero n) = v from hw]
    exact hv

omit [EnoughInjectives C] [HasProducts.{u} C] in
private theorem comp_mk₀_assoc {P A B D : C} (n : ℕ)
    (x : Ext P A n) (f : A ⟶ B) (g : B ⟶ D) :
    (x.comp (Ext.mk₀ f) (add_zero n)).comp (Ext.mk₀ g) (add_zero n) =
      x.comp (Ext.mk₀ (f ≫ g)) (add_zero n) := by
  rw [Ext.comp_assoc_of_third_deg_zero, ← Ext.mk₀_comp_mk₀]

/-- Under the same acyclicity hypothesis as lifting, an Ext class that
vanishes in the filtered colimit vanishes at a later stage. -/
theorem exists_transition_eq_zero [IsFiltered J] (P : C) [IsFinitelyPresentable.{u} P]
    (h₀ : ∀ (F : J ⥤ C) (x : Ext P (colimit F) 0),
      ∃ (i : J) (y : Ext P (F.obj i) 0), y.comp (Ext.mk₀ (colimit.ι F i)) rfl = x)
    (hA : ∀ (F : J ⥤ C) (_ : ∀ j, Injective (F.obj j)) (n : ℕ),
      Subsingleton (Ext P (colimit F) (n + 1)))
    (F : J ⥤ C) (n : ℕ) (i : J) (x : Ext P (F.obj i) n)
    (hx : x.comp (Ext.mk₀ (colimit.ι F i)) (add_zero n) = 0) :
    ∃ (j : J) (a : i ⟶ j), x.comp (Ext.mk₀ (F.map a)) (add_zero n) = 0 := by
  induction n generalizing F i with
  | zero =>
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).surjective x
    have hf : f ≫ colimit.ι F i = (0 : P ⟶ F.obj i) ≫ colimit.ι F i := by
      apply (Ext.mk₀_bijective _ _).injective
      rw [← Ext.mk₀_comp_mk₀, hx, zero_comp, Ext.mk₀_zero]
    obtain ⟨j, a, b, hab⟩ := IsFinitelyPresentable.exists_eq_of_isColimit
      (colimit.isColimit F) f 0 hf
    refine ⟨j, a, ?_⟩
    rw [Ext.mk₀_comp_mk₀, hab, zero_comp, Ext.mk₀_zero]
  | succ n ih =>
    obtain ⟨G, f, hMono, hInjective⟩ := exists_stagewise_injective_extension F
    let : Mono f := NatTrans.mono_of_mono_app f
    let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
    let hS : S.ShortExact := ⟨ShortComplex.exact_cokernel f⟩
    let T := S.map (colim : (J ⥤ C) ⥤ C)
    let hT := hS.map_of_exact (colim : (J ⥤ C) ⥤ C)
    let U (j : J) := S.map ((evaluation J C).obj j)
    let hU (j : J) := hS.map_of_exact ((evaluation J C).obj j)
    let ρ (j : J) : U j ⟶ T :=
      { τ₁ := colimit.ι S.X₁ j
        τ₂ := colimit.ι S.X₂ j
        τ₃ := colimit.ι S.X₃ j
        comm₁₂ := colimit.ι_map S.f j
        comm₂₃ := colimit.ι_map S.g j }
    let σ {j k : J} (a : j ⟶ k) : U j ⟶ U k :=
      { τ₁ := S.X₁.map a
        τ₂ := S.X₂.map a
        τ₃ := S.X₃.map a
        comm₁₂ := S.f.naturality a
        comm₂₃ := S.g.naturality a }
    let : Injective ((U i).X₂) := hInjective i
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ P (hU i) x
      (Ext.eq_zero_of_injective _) (n₀ := n) rfl
    have hd : (y.comp (Ext.mk₀ (ρ i).τ₃) (add_zero n)).comp hT.extClass rfl = 0 := by
      rw [Ext.comp_assoc_of_second_deg_zero, ← (hU i).extClass_naturality hT (ρ i),
        ← Ext.comp_assoc_of_third_deg_zero, hy]
      exact hx
    obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₃ P hT _ rfl hd
    obtain ⟨k, w, hw⟩ := exists_preimage P h₀ hA S.X₂ n z
    let a := IsFiltered.leftToMax i k
    let b := IsFiltered.rightToMax i k
    let l := IsFiltered.max i k
    let y' := y.comp (Ext.mk₀ (σ a).τ₃) (add_zero n)
    let w' := w.comp (Ext.mk₀ (σ b).τ₂) (add_zero n)
    let v := (Ext.mk₀ (U l).g).postcomp P (add_zero n) w'
    have hv : (y' - v).comp (Ext.mk₀ (colimit.ι S.X₃ l)) (add_zero n) = 0 := by
      change (Ext.mk₀ (colimit.ι S.X₃ l)).postcomp P (add_zero n) (y' - v) = 0
      rw [map_sub, sub_eq_zero]
      change (y.comp (Ext.mk₀ (S.X₃.map a)) (add_zero n)).comp
          (Ext.mk₀ (colimit.ι S.X₃ l)) (add_zero n) =
        ((w.comp (Ext.mk₀ (S.X₂.map b)) (add_zero n)).comp (Ext.mk₀ (U l).g)
          (add_zero n)).comp (Ext.mk₀ (colimit.ι S.X₃ l)) (add_zero n)
      rw [comp_mk₀_assoc, colimit.w, comp_mk₀_assoc]
      change y.comp (Ext.mk₀ (ρ i).τ₃) (add_zero n) =
        (w.comp (Ext.mk₀ (S.X₂.map b)) (add_zero n)).comp
          (Ext.mk₀ ((U l).g ≫ (ρ l).τ₃)) (add_zero n)
      rw [← (ρ l).comm₂₃, ← comp_mk₀_assoc n (w.comp (Ext.mk₀ (S.X₂.map b)) (add_zero n)),
        comp_mk₀_assoc n w]
      change y.comp (Ext.mk₀ (ρ i).τ₃) (add_zero n) =
        (w.comp (Ext.mk₀ (S.X₂.map b ≫ colimit.ι S.X₂ l)) (add_zero n)).comp
          (Ext.mk₀ T.g) (add_zero n)
      rw [colimit.w, hw, hz]
    obtain ⟨m, c, hc⟩ := ih S.X₃ l (y' - v) hv
    have hc' : y'.comp (Ext.mk₀ (σ c).τ₃) (add_zero n) =
        v.comp (Ext.mk₀ (σ c).τ₃) (add_zero n) := by
      change (Ext.mk₀ (σ c).τ₃).postcomp P (add_zero n) (y' - v) = 0 at hc
      rwa [map_sub, sub_eq_zero] at hc
    refine ⟨m, a ≫ c, ?_⟩
    change x.comp (Ext.mk₀ (σ (a ≫ c)).τ₁) (add_zero (n + 1)) = 0
    rw [← hy, Ext.comp_assoc_of_third_deg_zero, (hU i).extClass_naturality (hU m) (σ (a ≫ c)),
      ← Ext.comp_assoc_of_second_deg_zero]
    have hmove : y.comp (Ext.mk₀ (σ (a ≫ c)).τ₃) (add_zero n) =
        y'.comp (Ext.mk₀ (σ c).τ₃) (add_zero n) := by
      change y.comp (Ext.mk₀ (S.X₃.map (a ≫ c))) (add_zero n) =
        (y.comp (Ext.mk₀ (S.X₃.map a)) (add_zero n)).comp
          (Ext.mk₀ (S.X₃.map c)) (add_zero n)
      rw [comp_mk₀_assoc, Functor.map_comp]
    rw [hmove, hc']
    change ((w'.comp (Ext.mk₀ (U l).g) (add_zero n)).comp (Ext.mk₀ (σ c).τ₃)
      (add_zero n)).comp (hU m).extClass rfl = 0
    rw [comp_mk₀_assoc, ← (σ c).comm₂₃, ← comp_mk₀_assoc]
    rw [Ext.comp_assoc_of_second_deg_zero (w'.comp (Ext.mk₀ (σ c).τ₂) (add_zero n)),
      (hU m).comp_extClass, Ext.comp_zero]

/-- With a finitely presentable source and acyclicity of filtered colimits
of injectives, Ext commutes with the filtered colimit. -/
noncomputable def isColimit_ext [IsFiltered J] (P : C) [IsFinitelyPresentable.{u} P]
    (hA : ∀ (F : J ⥤ C) (_ : ∀ j, Injective (F.obj j)) (n : ℕ),
      Subsingleton (Ext P (colimit F) (n + 1))) (F : J ⥤ C) (n : ℕ) :
    IsColimit ((extFunctorObj P n).mapCocone (colimit.cocone F)) := by
  have h₀ (G : J ⥤ C) (x : Ext P (colimit G) 0) :
      ∃ (j : J) (y : Ext P (G.obj j) 0), y.comp (Ext.mk₀ (colimit.ι G j)) rfl = x := by
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).surjective x
    obtain ⟨j, g, hg⟩ := IsFinitelyPresentable.exists_hom_of_isColimit (colimit.isColimit G) f
    exact ⟨j, Ext.mk₀ g, (Ext.mk₀_comp_mk₀ g _).trans (congrArg Ext.mk₀ hg)⟩
  let : ReflectsColimit (F ⋙ extFunctorObj P n) (forget AddCommGrpCat.{u}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  apply isColimitOfReflects (forget AddCommGrpCat.{u})
  refine Types.FilteredColimit.isColimitOf' _ _ ?_ ?_
  · intro x
    obtain ⟨j, y, hy⟩ := exists_preimage P h₀ hA F n x
    exact ⟨j, y, hy.symm⟩
  · intro i x y h
    change Ext P (F.obj i) n at x y
    let t := (Ext.mk₀ (colimit.ι F i)).postcomp P (add_zero n)
    change t x = t y at h
    have hz : t (x - y) = 0 := by rw [map_sub, h, sub_self]
    obtain ⟨j, a, ha⟩ := exists_transition_eq_zero P h₀ hA F n i (x - y) hz
    let s := (Ext.mk₀ (F.map a)).postcomp P (add_zero n)
    change s (x - y) = 0 at ha
    rw [map_sub, sub_eq_zero] at ha
    exact ⟨j, a, ha⟩

end PhilipponFilteredColimitExtLifting

end

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite


namespace PhilipponFilteredHomDetection

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

open IsGrothendieckAbelian.IsPresentable.injectivity₀

attribute [local instance] IsFiltered.isConnected

/-- If maps out of an object lift along filtered colimits, a map that
vanishes in a filtered colimit already vanishes after a transition. -/
theorem exists_transition_eq_zero (X : C)
    (hLift : ∀ {J : Type w} [SmallCategory J] [IsFiltered J] (F : J ⥤ C) (d : Cocone F),
      IsColimit d → ∀ x : X ⟶ d.pt, ∃ (j : J) (y : X ⟶ F.obj j), y ≫ d.ι.app j = x)
    {J : Type w} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ C) (d : Cocone F) (hd : IsColimit d)
    (i : J) (x : X ⟶ F.obj i) (hx : x ≫ d.ι.app i = 0) :
    ∃ (j : J) (a : i ⟶ j), x ≫ F.map a = 0 := by
  let K := kernel (g x)
  let b := kernel.ι (g x)
  let D := (Functor.const (Under i)).obj X
  let c := constCocone (Under i) X
  let e : colimit D ≅ X := (colimit.isColimit D).coconePointUniqueUpToIso (isColimitConstCocone (Under i) X)
  have hf' : colim.map b ≫ e.hom = f x := by
    apply colimit.hom_ext
    intro j
    have h : colimit.ι D j ≫ e.hom = 𝟙 X := (colimit.isColimit D).fac c j
    calc
      _ = b.app j ≫ colimit.ι D j ≫ e.hom := colimit.ι_map_assoc b j e.hom
      _ = b.app j ≫ 𝟙 X := congrArg (fun a : X ⟶ X => b.app j ≫ a) h
      _ = b.app j := Category.comp_id _
      _ = _ := (hf x j).symm
  let : Mono (f x) := hf' ▸ inferInstanceAs (Mono (colim.map b ≫ e.hom))
  let : Epi (f x) := epi_f hd hx
  let : IsIso (f x) := isIso_of_mono_of_epi (f x)
  obtain ⟨j, y, hy⟩ := hLift K (colimit.cocone K) (colimit.isColimit K) (inv (f x))
  change y ≫ colimit.ι K j = inv (f x) at hy
  have hs : y ≫ b.app j = 𝟙 X := by
    have hfac : colimit.ι K j ≫ f x = b.app j := hf x j
    rw [← hfac, ← Category.assoc, hy, IsIso.inv_hom_id]
  have hz : b.app j ≫ x ≫ F.map j.hom = 0 :=
    NatTrans.congr_app (kernel.condition (g x)) j
  refine ⟨j.right, j.hom, ?_⟩
  calc
    x ≫ F.map j.hom = y ≫ b.app j ≫ x ≫ F.map j.hom := by
      rw [← Category.assoc y, hs, Category.id_comp]
    _ = 0 := by rw [hz, comp_zero]

/-- In a Grothendieck abelian category, surjectivity of the Hom comparison
for every filtered diagram already implies finite presentability. -/
theorem isFinitelyPresentable_of_lifting (X : C)
    (hLift : ∀ {J : Type w} [SmallCategory J] [IsFiltered J] (F : J ⥤ C) (d : Cocone F),
      IsColimit d → ∀ x : X ⟶ d.pt, ∃ (j : J) (y : X ⟶ F.obj j), y ≫ d.ι.app j = x) :
    IsFinitelyPresentable.{w} X := by
  apply isFinitelyPresentable_iff_preservesFilteredColimitsOfSize.mpr
  constructor
  intro J _ _
  constructor
  intro F
  constructor
  intro d hd
  let H := coyoneda.obj (op X)
  refine ⟨Types.FilteredColimit.isColimitOf' _ (H.mapCocone d) ?_ ?_⟩
  · intro x
    obtain ⟨j, y, hy⟩ := hLift F d hd x
    exact ⟨j, y, hy.symm⟩
  · intro i x y h
    change X ⟶ F.obj i at x y
    change x ≫ d.ι.app i = y ≫ d.ι.app i at h
    obtain ⟨j, a, ha⟩ := exists_transition_eq_zero X hLift F d hd i (x - y) (by
      rw [Preadditive.sub_comp, h, sub_self])
    refine ⟨j, a, ?_⟩
    change x ≫ F.map a = y ≫ F.map a
    exact sub_eq_zero.mp (by simpa only [Preadditive.sub_comp] using ha)

/-- A binary direct sum of finitely presentable objects is finitely presentable. -/
theorem isFinitelyPresentable_biprod (A B : C)
    [IsFinitelyPresentable.{w} A] [IsFinitelyPresentable.{w} B] :
    IsFinitelyPresentable.{w} (A ⊞ B) := by
  apply isFinitelyPresentable_of_lifting
  intro J _ _ F d hd x
  obtain ⟨i, a, ha⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hd (biprod.inl ≫ x)
  obtain ⟨j, b, hb⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hd (biprod.inr ≫ x)
  let p := IsFiltered.leftToMax i j
  let q := IsFiltered.rightToMax i j
  refine ⟨IsFiltered.max i j, biprod.desc (a ≫ F.map p) (b ≫ F.map q), ?_⟩
  apply biprod.hom_ext'
  · rw [biprod.inl_desc_assoc, Category.assoc, d.w p, ha]
  · rw [biprod.inr_desc_assoc, Category.assoc, d.w q, hb]

/-- The cokernel of a map between finitely presentable objects is finitely presentable. -/
theorem isFinitelyPresentable_of_shortExact (S : ShortComplex C) (hS : S.ShortExact)
    [IsFinitelyPresentable.{w} S.X₁] [IsFinitelyPresentable.{w} S.X₂] :
    IsFinitelyPresentable.{w} S.X₃ := by
  apply isFinitelyPresentable_of_lifting
  intro J _ _ F d hd x
  let : Epi S.g := hS.epi_g
  let hCokernel := hS.exact.gIsCokernel
  obtain ⟨i, a, ha⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hd (S.g ≫ x)
  have hz : (S.f ≫ a) ≫ d.ι.app i = (0 : S.X₁ ⟶ F.obj i) ≫ d.ι.app i := by
    simp only [Category.assoc, ha, S.zero_assoc, zero_comp]
  obtain ⟨j, p, q, hpq⟩ := IsFinitelyPresentable.exists_eq_of_isColimit hd _ _ hz
  have hp : S.f ≫ a ≫ F.map p = 0 := by
    rw [← Category.assoc, hpq, zero_comp]
  let c := CokernelCofork.ofπ (a ≫ F.map p) hp
  refine ⟨j, hCokernel.desc c, ?_⟩
  have hc : S.g ≫ hCokernel.desc c = a ≫ F.map p := hCokernel.fac c WalkingParallelPair.one
  apply (cancel_epi S.g).mp
  rw [← Category.assoc, hc, Category.assoc, d.w p, ha]

end PhilipponFilteredHomDetection

end


