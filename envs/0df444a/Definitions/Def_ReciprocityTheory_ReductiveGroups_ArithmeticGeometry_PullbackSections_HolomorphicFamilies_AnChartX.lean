-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnChartX
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnChartX
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T17:43:59.757435+00:00
-- url     : https://prove2.me/theorems/d0f1b5f3-dd55-577e-bf9a-61a7c28417b5
-- title:
--   An Chart X
-- statement:
--   Definitions and structural lemmas for An Chart X, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/AnChartX.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetF
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetPt_over

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
def anE (F : FamilyUnif Xo σ' ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) :
    (Fin g → ℂ) → (Sp ℂ ⟶ Xo.univ.t.G.left) :=
  fun z => (F.ex i P z).left
theorem anHol (F : FamilyUnif Xo σ' ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i) ty P) : IsHolFam (anE F i P) := by
  have hper : IsHolPeriods (F.Di i) ty (Set.univ : Set (Fin 0 → ℂ)) (fun _ => P) :=
    ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩
  have h2 := (F.hol i 0 Set.univ (fun _ => P) isOpen_univ hper).2
  intro U f
  obtain ⟨ho, hd⟩ := h2 U f
  have hι : Differentiable ℂ (fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) := by fun_prop
  have hc := hd.comp hι.differentiableOn (Set.mapsTo_preimage _ _)
  refine ⟨?_, ?_⟩
  · convert ho.preimage hι.continuous using 1
    ext z
    simp [anE]
  · convert hc using 1
    all_goals
      ext z
      simp [anE]
variable [Algebra c.F ℂ]
def anX (F : FamilyUnif Xo σ' ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P)
    (y : FrPt Xo c ℂ) (hy : y.x = F.u i P) (m : ℕ) : jO y g m 1 ⟶ Xo.univ.t.G :=
  Over.homMk (jetPt (anE F i P) (anHol F i P hP) m) (by
    rw [jetPt_over (anE F i P) (anHol F i P hP) Xo.univ.t.G.hom (F.u i P) (fun z => Over.w (F.ex i P z)) m, ← hy]
    rfl)
variable (F : FamilyUnif Xo σ' ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P)
  (y : FrPt Xo c ℂ) (hy : y.x = F.u i P)
def anAct (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) : Fin g → MvPowerSeries (Fin 1 × Fin g) ℂ :=
  fun k => MvPowerSeries.C (ty k (a : E)) * MvPowerSeries.X ((0 : Fin 1), k)
theorem epsMul_algebraMap (cc : ℂ) (a : ℂ) : epsMul cc (algebraMap ℂ (DualNumber ℂ) a) = algebraMap ℂ _ a := by
  ext <;> simp [epsMul]
def epsHom (x : Sp ℂ ⟶ Xo.X) (cc : ℂ) : tEps x ⟶ tEps x :=
  Over.homMk (spMap (epsMul cc)) (by
    show spMap (epsMul cc) ≫ spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x
    rw [← Category.assoc, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    exact RingHom.ext fun a => epsMul_algebraMap cc a)
end ReciprocityTheory.ChartRestriction.G.PullbackSections


