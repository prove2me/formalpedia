-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExactOfSpan
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExactOfSpan
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T22:16:42.781382+00:00
-- url     : https://prove2.me/theorems/80c6ee13-d6ac-474a-bce8-59e96b64cd42
-- title:
--   Exact Of Span
-- statement:
--   Definitions and structural lemmas for Exact Of Span, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExactOfSpan.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_smul
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_smul
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp

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
namespace GlobalTheory.CompanionTheory.AffAcyc
section Cochains
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C]
def sc (F : C ⥤ CommAlgCat.{0} R) (g : ∀ T, F.obj T) (n : ℕ) (z : Cn F n) : Cn F n :=
  fun c ↦ g (c.obj (Fin.last n)) * z c
end Cochains
section Pointed
variable {R : Type} [CommRing R] {P : Type} [SemilatticeInf P]
def G1 (a₀ : P) : Pᵒᵖ ⥤ Pᵒᵖ :=
  (show Monotone fun a : P ↦ a ⊓ a₀ from fun _ _ h ↦ inf_le_inf_right a₀ h).functor.op
def th (a₀ : P) : 𝟭 Pᵒᵖ ⟶ G1 a₀ where
  app T := (homOfLE inf_le_left : T.unop ⊓ a₀ ⟶ T.unop).op
  naturality _ _ _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
def th' (a₀ : P) : (Functor.const Pᵒᵖ).obj (op a₀) ⟶ G1 a₀ where
  app T := (homOfLE inf_le_right : T.unop ⊓ a₀ ⟶ a₀).op
  naturality _ _ _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
variable (F : Pᵒᵖ ⥤ CommAlgCat.{0} R) (a₀ : P)
  (hb : ∀ T : Pᵒᵖ, Function.Bijective (mp F ((th a₀).app T)))
def io (T : Pᵒᵖ) : F.obj T ≃ₐ[R] F.obj ((G1 a₀).obj T) :=
  AlgEquiv.ofBijective (mp F ((th a₀).app T)) (hb T)
theorem io_nat {T T' : Pᵒᵖ} (φ : T ⟶ T') (b : F.obj ((G1 a₀).obj T)) :
    (io F a₀ hb T').symm (mp F ((G1 a₀).map φ) b) = mp F φ ((io F a₀ hb T).symm b) := by
  apply (io F a₀ hb T').injective
  rw [AlgEquiv.apply_symm_apply]
  change _ = mp F ((th a₀).app T') (mp F φ ((io F a₀ hb T).symm b))
  rw [← mp_comp]
  have e : φ ≫ (th a₀).app T' = (th a₀).app T ≫ (G1 a₀).map φ :=
    Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  rw [e, mp_comp]
  change _ = mp F ((G1 a₀).map φ) (io F a₀ hb T ((io F a₀ hb T).symm b))
  rw [AlgEquiv.apply_symm_apply]
def m1 : CoefMap (RingHom.id R) F F where
  G := G1 a₀
  α T := ((io F a₀ hb T).symm : _ →ₐ[R] _).toRingHom
  naturality φ b := io_nat F a₀ hb φ b
  smul T r b := map_smul (io F a₀ hb T).symm r b
def m2 : CoefMap (RingHom.id R) F F where
  G := (Functor.const Pᵒᵖ).obj (op a₀)
  α T := (((io F a₀ hb T).symm : F.obj ((G1 a₀).obj T) →ₐ[R] F.obj T).comp
    (mp F ((th' a₀).app T))).toRingHom
  naturality {T T'} φ b := by
    change (io F a₀ hb T').symm (mp F ((th' a₀).app T') (mp F (𝟙 (op a₀)) b)) =
      mp F φ ((io F a₀ hb T).symm (mp F ((th' a₀).app T) b))
    rw [← io_nat, ← mp_comp, ← mp_comp]
    congr 2
  smul T r b := map_smul (((io F a₀ hb T).symm : F.obj ((G1 a₀).obj T) →ₐ[R] F.obj T).comp
    (mp F ((th' a₀).app T))) r b
def E (n : ℕ) (t : F.obj (op a₀)) : Cn F n := fun c ↦ (m2 F a₀ hb).α (c.obj (Fin.last n)) t
end Pointed
section Transfer
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C]
def nat {F F' : C ⥤ CommAlgCat.{0} R} (ρ : ∀ T, F.obj T →ₐ[R] F'.obj T)
    (hρ : ∀ {T T' : C} (φ : T ⟶ T') (b : F.obj T), ρ T' (mp F φ b) = mp F' φ (ρ T b)) :
    CoefMap (RingHom.id R) F F' where
  G := 𝟭 C
  α T := (ρ T).toRingHom
  naturality φ b := hρ φ b
  smul T r b := map_smul (ρ T) r b
end Transfer
section Schemes
variable {R : Type} [CommRing R] {X : Scheme.{0}} {P : Type} [SemilatticeInf P]
variable (s : X ⟶ Sp R) (W : X.affineOpens) (u : P →o X.affineOpens) (hle : ∀ a, (u a).1 ≤ W.1)
abbrev FF (s : X ⟶ Sp R) (u : P →o X.affineOpens) : Pᵒᵖ ⥤ CommAlgCat.{0} R :=
  u.monotone.functor.op ⋙ OAff s
def rf (f : Γ(X, W.1)) (a : P) : Γ(X, (u a).1) := Sec.res s (hle a) f
theorem basicOpen_rf (f : Γ(X, W.1)) (a : P) :
    X.basicOpen (rf s W u hle f a) = (u a).1 ⊓ X.basicOpen f :=
  Scheme.basicOpen_res X f (homOfLE (hle a)).op
def uf (f : Γ(X, W.1)) : P →o X.affineOpens where
  toFun a := ⟨X.basicOpen (rf s W u hle f a), IsAffineOpen.basicOpen (u a).2 _⟩
  monotone' a b h := by
    change X.basicOpen _ ≤ X.basicOpen _
    rw [basicOpen_rf, basicOpen_rf]
    exact inf_le_inf_right _ (u.monotone h)
def rho (f : Γ(X, W.1)) (T : Pᵒᵖ) : (FF s u).obj T →ₐ[R] (FF s (uf s W u hle f)).obj T :=
  Sec.res s (X.basicOpen_le _)
def gF (f : Γ(X, W.1)) (T : Pᵒᵖ) : (FF s u).obj T := rf s W u hle f T.unop
end Schemes
section Degree0
variable {R : Type} [CommRing R] {P : Type} [SemilatticeInf P] (F : Pᵒᵖ ⥤ CommAlgCat.{0} R)
end Degree0
end GlobalTheory.CompanionTheory.AffAcyc


