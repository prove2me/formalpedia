-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIndepSections
-- name    : Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIndepSections
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:37:57.5008+00:00
-- url     : https://prove2.me/theorems/4d794bda-9edb-4ebb-a4e0-2e179b03ebef
-- title:
--   Exists Indep Sections
-- statement:
--   Definitions and structural lemmas for Exists Indep Sections, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsIndepSections.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
namespace GlobalTheory.PowSec
section Transport
variable {X Y : Scheme.{0}} (L : LB X) (σ : Y ⟶ X) (ρ : X ⟶ Y) (e : ρ ≫ σ = 𝟙 X) (n : ℤ)
include e in
theorem chart_eq (j : PUnit → L.ι) :
    LB.wchart L (fun _ : PUnit => 𝟙 X) j = ρ ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => σ) (fun _ => j PUnit.unit) := by
  ext y
  have h : σ (ρ y) = y := by rw [← Scheme.Hom.comp_apply, e]; rfl
  constructor
  · intro hy
    refine Set.mem_iInter.2 fun _ => ?_
    have := Set.mem_iInter.1 hy PUnit.unit
    show σ (ρ y) ∈ L.U (j PUnit.unit)
    rw [h]; exact this
  · intro hy
    refine Set.mem_iInter.2 fun _ => ?_
    have : σ (ρ y) ∈ L.U (j PUnit.unit) := Set.mem_iInter.1 hy 0
    rw [h] at this; exact this
theorem appLE_congr {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens) (h₁ : V ≤ f ⁻¹ᵁ U) (h₂ : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V h₁ = g.appLE U V h₂ := by subst h; rfl
def down (b : (LB.LinComb L (K := Fin 1) (fun _ => σ) (fun _ => n)).Sec) :
    (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) (fun _ => n)).Sec where
  f j := (ρ.appLE _ _ (chart_eq L σ ρ e j).le).hom (b.f (fun _ => j PUnit.unit))
  compat i j := by
    have hle : LB.wchart L (fun _ : PUnit => 𝟙 X) i ⊓ LB.wchart L (fun _ : PUnit => 𝟙 X) j ≤
      ρ ⁻¹ᵁ (LB.wchart L (fun _ : Fin 1 => σ) (fun _ => i PUnit.unit) ⊓
        LB.wchart L (fun _ : Fin 1 => σ) (fun _ => j PUnit.unit)) :=
      inf_le_inf (chart_eq L σ ρ e i).le (chart_eq L σ ρ e j).le
    have := congrArg (ρ.appLE _ _ hle).hom (b.compat (fun _ => i PUnit.unit) (fun _ => j PUnit.unit))
    replace this := this.trans (map_mul _ _ _)
    refine Eq.trans ?_ (this.trans (congrArg₂ (· * ·) ?_ ?_))
    · exact (congrArg (fun φ => φ.hom (b.f fun _ => i PUnit.unit))
        ((Scheme.Hom.appLE_map ρ _ _).trans (Scheme.Hom.map_appLE ρ hle _).symm) :)
    · simp only [LB.LinComb, Fintype.prod_unique]
      refine (congrArg Units.val ((map_zpow (Units.map (ρ.appLE _ _ hle).hom.toMonoidHom) _ n).trans
        (congrArg (· ^ n) (Units.ext ?_))) :)
      have h1 : (σ.app (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) ≫ Y.presheaf.map (homOfLE (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : Fin 1 => σ) (fun _ => i PUnit.unit) 0))
          (inf_le_right.trans (LB.wchart_le L (fun _ : Fin 1 => σ) (fun _ => j PUnit.unit) 0)))).op) ≫ ρ.appLE _ _ hle =
          (𝟙 X : X ⟶ X).app (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) ≫ X.presheaf.map (homOfLE (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : PUnit => 𝟙 X) i PUnit.unit))
          (inf_le_right.trans (LB.wchart_le L (fun _ : PUnit => 𝟙 X) j PUnit.unit)))).op :=
        (Scheme.Hom.appLE_comp_appLE ρ σ _ _ _ _ hle).trans (appLE_congr e _ _ _ _)
      exact congrArg (fun φ => φ.hom (L.g (i PUnit.unit) (j PUnit.unit)).val) h1
    · exact (congrArg (fun φ => φ.hom (b.f fun _ => j PUnit.unit))
        ((Scheme.Hom.map_appLE ρ hle _).trans (Scheme.Hom.appLE_map ρ _ _).symm) :)
end Transport
attribute [local instance] Over.cartesianMonoidalCategory
end GlobalTheory.PowSec


