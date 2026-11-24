-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteCover
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteCover
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T22:16:06.647094+00:00
-- url     : https://prove2.me/theorems/49f1303a-bf86-40f8-a0f1-6075a8cc7790
-- title:
--   Exists Finite Cover
-- statement:
--   Definitions and structural lemmas for Exists Finite Cover, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteCover.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_smul
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_smul

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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
namespace GlobalTheory.CompanionTheory.Descent
variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)
variable {C D E : Type} [Category.{0} C] [Category.{0} D] [Category.{0} E]
def rm (f : C ⥤ AffOp X) (g : D ⥤ AffOp X) (σ : D ⥤ C)
    (h : ∀ T, (g.obj T).unop.1 ≤ (f.obj (σ.obj T)).unop.1) :
    CoefMap (RingHom.id R) (f ⋙ OAff s) (g ⋙ OAff s) where
  G := σ
  α T := (Sec.res s (h T)).toRingHom
  naturality {T T'} φ b := by
    have h1 := Sec.res_res s (leOfHom (f.map (σ.map φ)).unop) (h T') b
    have h2 := Sec.res_res s (h T) (leOfHom (g.map φ).unop) b
    exact h1.symm.trans h2
  smul T r b := map_smul (Sec.res s (h T)) r b
def aug (f : E ⥤ AffOp X) (W : X.Opens) (hle : ∀ T, (f.obj T).unop.1 ≤ W) :
    Sec s W →ₗ[R] Cn (f ⋙ OAff s) 0 :=
  LinearMap.pi fun c ↦ (Sec.res s (hle (c.obj (Fin.last 0)))).toLinearMap
def Acyc (f : E ⥤ AffOp X) (W : X.Opens) (hle : ∀ T, (f.obj T).unop.1 ≤ W) : Prop :=
  Function.Injective (aug s f W hle) ∧ Function.Exact (aug s f W hle) (dn (f ⋙ OAff s) 0) ∧
    ∀ n, Function.Exact (dn (f ⋙ OAff s) n) (dn (f ⋙ OAff s) (n + 1))
section Calculus
variable {F : C ⥤ CommAlgCat.{0} R} {G : D ⥤ CommAlgCat.{0} R}
end Calculus
section Opens
def v₀ (W : X.affineOpens) : Fin 1 →o X.affineOpens := ⟨fun _ ↦ W, monotone_const⟩
def pt (W : X.affineOpens) : (Fin 1)ᵒᵖ ⥤ AffOp X := (v₀ W).monotone.functor.op
def pj (f : C ⥤ AffOp X) (w : C × D ⥤ AffOp X) (h : ∀ T, (w.obj T).unop.1 ≤ (f.obj T.1).unop.1) :
    Proj (f ⋙ OAff s) (w ⋙ OAff s) where
  α T := Sec.res s (h T)
  naturality {T T'} φ b := by
    have h1 := Sec.res_res s (leOfHom (f.map φ.1).unop) (h T') b
    have h2 := Sec.res_res s (h T) (leOfHom (w.map φ).unop) b
    exact h1.symm.trans h2
end Opens
section Meet
variable (hi : ∀ U V : X.affineOpens, IsAffineOpen (U.1 ⊓ V.1))
def meet (U V : X.affineOpens) : X.affineOpens := ⟨U.1 ⊓ V.1, hi U V⟩
def wFun (f : C ⥤ AffOp X) (g : D ⥤ AffOp X) : C × D ⥤ AffOp X where
  obj T := op (meet hi (f.obj T.1).unop (g.obj T.2).unop)
  map {T T'} φ := (homOfLE (show meet hi (f.obj T'.1).unop (g.obj T'.2).unop ≤
    meet hi (f.obj T.1).unop (g.obj T.2).unop by
      change (f.obj T'.1).unop.1 ⊓ (g.obj T'.2).unop.1 ≤ (f.obj T.1).unop.1 ⊓ (g.obj T.2).unop.1
      exact inf_le_inf (leOfHom (f.map φ.1).unop) (leOfHom (g.map φ.2).unop))).op
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _
end Meet
end GlobalTheory.CompanionTheory.Descent


