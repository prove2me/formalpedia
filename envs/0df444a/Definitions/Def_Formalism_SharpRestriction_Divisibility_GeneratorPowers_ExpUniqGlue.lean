-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqGlue
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqGlue
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T13:31:02.342867+00:00
-- url     : https://prove2.me/theorems/ea3913be-0720-4da8-91c4-eb81be8a7b86
-- title:
--   Exp Uniq Glue
-- statement:
--   Definitions and structural lemmas for Exp Uniq Glue, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpUniqGlue.lean

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_JetGlue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet
attribute [local instance] Over.cartesianMonoidalCategory
section BC
variable {S T : Type} [CommRing S] [CommRing T] (f : S →+* T)
def bcJ (κ : Type) (m : ℕ) : Jet S κ m →+* Jet T κ m :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (MvPolynomial.map f)) (fun P hP => by
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    have h1 : orig S κ ≤ (orig T κ).comap (MvPolynomial.map f) := by
      unfold orig
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      rw [SetLike.mem_coe, Ideal.mem_comap, map_X]
      exact Ideal.subset_span ⟨j, rfl⟩
    exact ((Ideal.pow_right_mono h1 _).trans (Ideal.le_comap_pow _ _)) hP)
theorem bcJ_C {κ : Type} (m : ℕ) (s : S) :
    bcJ f κ m (algebraMap S (Jet S κ m) s) = algebraMap T (Jet T κ m) (f s) := by
  show Ideal.Quotient.mk _ (MvPolynomial.map f (C s)) = Ideal.Quotient.mk _ (C (f s))
  rw [MvPolynomial.map_C]
theorem bcJ_comp (κ : Type) (m : ℕ) :
    (bcJ f κ m).comp (algebraMap S (Jet S κ m)) = (algebraMap T (Jet T κ m)).comp f := RingHom.ext fun s => bcJ_C f (κ := κ) m s
variable {X : Scheme.{0}} (x0 : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp S ⟶ X)
abbrev x0T : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp T ⟶ X := Spec.map (CommRingCat.ofHom f) ≫ x0
def bcO {A A' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra T A'] (bA : A →+* A')
    (hA : bA.comp (algebraMap S A) = (algebraMap T A').comp f) : overAt (x0T f x0) A' ⟶ overAt x0 A :=
  Over.homMk (Spec.map (CommRingCat.ofHom bA)) (by
    dsimp
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hA])
end BC
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
section Transfer
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {S T : Type} [CommRing S] [CommRing T] (f : S →+* T) (x0 : Sp S ⟶ Xo.X) {d : ℕ}
def xT (x : ∀ m, overAt x0 (Jet S (Fin 1 × Fin d) m) ⟶ Xo.univ.t.G) (m : ℕ) :
    overAt (x0T f x0) (Jet T (Fin 1 × Fin d) m) ⟶ Xo.univ.t.G :=
  bcO f x0 (bcJ f (Fin 1 × Fin d) m) (bcJ_comp f _ m) ≫ x m
end Transfer
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue


