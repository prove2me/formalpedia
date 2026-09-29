-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.fppfAmitsurTrivial_constantZModSheaf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/3c5be88a-37f7-5053-9fb0-a80d2288475e

import Definitions.Def_AlgebraicGeometry_FppfKummerProp17
import Definitions.Def_AlgebraicGeometry_FppfAmitsurTrivial
import Definitions.Def_Algebra_DescentCofaces
import Theorems.Thm_Algebra_DescentCofaces_exists_finite_flat_unramified_nonempty_ringHom_iff_isCoboundary
import Theorems.Thm_Algebra_FormallyUnramified_nonempty_ringHom_int
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_fppfAmitsurTrivial_constantZModSheaf

set_option autoImplicit false

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.topMap Spec Spec.map Scheme FormallyUnramified Scheme.FppfAmitsurTrivial"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "FppfAmitsurTrivial"
namespace ConstCob
p2m_open "AlgebraicGeometry.Scheme AlgebraicGeometry"
p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_fppfAmitsurTrivial_constantZModSheaf.AlgebraicGeometry Opposite Algebra.DescentCofaces"
open FppfRepresentableGroupSchemeSheaf FppfKummerSES

variable (p : ℕ)

local instance topZMod : TopologicalSpace (ZMod p) := ⊥
local instance discZMod : DiscreteTopology (ZMod p) := ⟨rfl⟩

noncomputable abbrev F := (sheafULift.{0}.obj (constantZModSheaf.{0} p)).obj

def toCM {R : CommRingCat.{0}} (s : ToType ((F p).obj (op (Spec R)))) : C(PrimeSpectrum R, ZMod p) :=
  s.down

def toLC {R : CommRingCat.{0}} (s : ToType ((F p).obj (op (Spec R)))) :
    LocallyConstant (PrimeSpectrum R) (ZMod p) where
  toFun x := toCM p s x
  isLocallyConstant := (IsLocallyConstant.iff_continuous _).2 (toCM p s).continuous

def ofLC {R : CommRingCat.{0}} (g : LocallyConstant (PrimeSpectrum R) (ZMod p)) :
    ToType ((F p).obj (op (Spec R))) :=
  ULift.up (show C(PrimeSpectrum R, ZMod p) from ⟨g, g.isLocallyConstant.continuous⟩)

theorem toLC_ofLC {R : CommRingCat.{0}} (g : LocallyConstant (PrimeSpectrum R) (ZMod p)) :
    toLC p (ofLC p g) = g := by
  ext x; rfl

theorem ofLC_toLC {R : CommRingCat.{0}} (s : ToType ((F p).obj (op (Spec R)))) :
    ofLC p (toLC p s) = s := by
  rfl

theorem toLC_injective {R : CommRingCat.{0}} : Function.Injective (toLC p (R := R)) := by
  intro s t h
  rw [← ofLC_toLC p s, ← ofLC_toLC p t, h]

theorem toLC_add {R : CommRingCat.{0}} (s t : ToType ((F p).obj (op (Spec R)))) :
    toLC p (s + t) = toLC p s + toLC p t := by
  ext x; rfl

theorem toLC_sub {R : CommRingCat.{0}} (s t : ToType ((F p).obj (op (Spec R)))) :
    toLC p (s - t) = toLC p s - toLC p t := by
  ext x; rfl

theorem toLC_map {R S : CommRingCat.{0}} (φ : R ⟶ S) (s : ToType ((F p).obj (op (Spec R)))) :
    toLC p ((F p).map (Spec.map φ).op s) = (toLC p s).comap (Spec.topMap φ).hom := by
  ext x; rfl

end AlgebraicGeometry.Scheme.ConstCob

open CategoryTheory _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_fppfAmitsurTrivial_constantZModSheaf.AlgebraicGeometry Opposite Algebra.DescentCofaces AlgebraicGeometry.Scheme.ConstCob in
theorem solution (p : ℕ) (hp : p ≠ 0) (A : Type) [CommRing A] [Module.FaithfullyFlat ℤ A] :
    Scheme.FppfAmitsurTrivial
      (FppfKummerSES.sheafULift.{0}.obj (FppfRepresentableGroupSchemeSheaf.constantZModSheaf.{0} p)) A := by
  intro c hc
  have hc' := congrArg (toLC p) hc
  rw [toLC_add, toLC_map, toLC_map, toLC_map] at hc'
  obtain ⟨B, _, _, _, _, _, _, hiff⟩ :=
    Algebra.DescentCofaces.exists_finite_flat_unramified_nonempty_ringHom_iff_isCoboundary
      p hp A (toLC p c) hc'
  obtain ⟨b, hb⟩ := hiff.mp (Algebra.FormallyUnramified.nonempty_ringHom_int B)
  refine ⟨ofLC p b, toLC_injective p ?_⟩
  rw [toLC_sub, toLC_map, toLC_map, toLC_ofLC]
  exact hb

end S_AlgebraicGeometry_Scheme_fppfAmitsurTrivial_constantZModSheaf
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_fppfAmitsurTrivial_constantZModSheaf (solution)
