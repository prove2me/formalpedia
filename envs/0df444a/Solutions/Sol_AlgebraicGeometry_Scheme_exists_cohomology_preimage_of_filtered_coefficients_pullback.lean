-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_cohomology_preimage_of_filtered_coefficients_pullback
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-25T20:19:45.57124+00:00
-- url     : https://prove2.me/submissions/29ab30e6-354b-4a6d-8eba-176c87c7f84d

import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_etale_H_zero_preimage_of_filtered_coefficients
import Theorems.Thm_AlgebraicGeometry_Scheme_filtered_colimit_of_injectives_etale_H_succ_subsingleton

noncomputable section

section

section

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

end PhilipponFilteredColimitExtLifting

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)

namespace PhilipponEtaleFilteredColimitDimensionShift

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

/-- Following pullback to an affine scheme, class lifting for filtered
coefficients follows from degree zero and acyclicity for stagewise injectives. -/
theorem exists_preimage_pullback {J : Type u} [Category.{u} J] [IsFiltered J]
    {X Z : Scheme.{u}} (i : Z ⟶ X)
    (h₀ : ∀ (G : J ⥤ Ab Z) (e : Cocone G) (_ : IsColimit e) (y : e.pt.H 0),
      ∃ (j : J) (z : (G.obj j).H 0), Sheaf.H.map (e.ι.app j) 0 z = y)
    (hA : ∀ (G : J ⥤ Ab Z) (_ : ∀ j, Injective (G.obj j))
      (e : Cocone G) (_ : IsColimit e) (q : ℕ), Subsingleton (e.pt.H (q + 1)))
    (F : J ⥤ Ab X) (d : Cocone F) (hd : IsColimit d) (q : ℕ)
    (x : ((pullbackSheaves i).obj d.pt).H q) :
    ∃ (j : J) (z : ((pullbackSheaves i).obj (F.obj j)).H q),
      Sheaf.H.map ((pullbackSheaves i).map (d.ι.app j)) q z = x := by
  let P := pullbackSheaves i
  let : P.IsLeftAdjoint := (pullbackAdjunction i).isLeftAdjoint
  let G := F ⋙ P
  let e := P.mapCocone d
  let he := isColimitOfPreserves P hd
  let w := (colimit.isColimit G).coconePointUniqueUpToIso he
  let wH := ((Sheaf.functorH Z.smallEtaleTopology q).mapIso w).addCommGroupIsoToAddEquiv
  obtain ⟨y, hy⟩ := wH.surjective x
  let P₀ := (constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ))
  obtain ⟨j, z, hz⟩ := PhilipponFilteredColimitExtLifting.exists_preimage (J := J) P₀
    (fun H z => h₀ H (colimit.cocone H) (colimit.isColimit H) z)
    (fun H h n => hA H h (colimit.cocone H) (colimit.isColimit H) n) G q y
  refine ⟨j, z, ?_⟩
  have hfac : colimit.ι G j ≫ w.hom = P.map (d.ι.app j) :=
    (colimit.isColimit G).fac e j
  change Sheaf.H.map (P.map (d.ι.app j)) q z = x
  calc
    _ = Sheaf.H.map (colimit.ι G j ≫ w.hom) q z :=
      congrArg (fun m => Sheaf.H.map m q z) hfac.symm
    _ = Sheaf.H.map w.hom q (Sheaf.H.map (colimit.ι G j) q z) := Sheaf.H.map_comp_apply _ _ _
    _ = x := (congrArg (Sheaf.H.map w.hom q) hz).trans hy

end PhilipponEtaleFilteredColimitDimensionShift

end

section

open PhilipponEtaleSmallSite (pullbackSheaves)
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution
    {J : Type u} [Category.{u} J] [IsFiltered J] {X Z : Scheme.{u}} [IsAffine Z] (i : Z ⟶ X)
    (F : J ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (d : Cocone F) (hd : IsColimit d)
    (q : ℕ) (x : ((pullbackSheaves i).obj d.pt).H q) :
    ∃ (j : J) (y : ((pullbackSheaves i).obj (F.obj j)).H q),
      Sheaf.H.map ((pullbackSheaves i).map (d.ι.app j)) q y = x := by
  exact
    PhilipponEtaleFilteredColimitDimensionShift.exists_preimage_pullback i
      (AlgebraicGeometry.Scheme.exists_etale_H_zero_preimage_of_filtered_coefficients Z)
      (fun G h e he n => by
        let : ∀ j, Injective (G.obj j) := h
        exact AlgebraicGeometry.Scheme.filtered_colimit_of_injectives_etale_H_succ_subsingleton Z G e he n) F d hd q x

end

end
