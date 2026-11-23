-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:35:06.986229+00:00
-- url     : https://prove2.me/theorems/a9409a0b-172a-401d-9886-cf87edf27782
-- title:
--   CInd BC
-- statement:
--   Definitions and structural lemmas for CInd BC, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/CIndBC.lean

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndRaw
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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
open MvPolynomial (X C)
attribute [local instance] Over.cartesianMonoidalCategory
section Jet
variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S')
theorem orig_pow_le_comap (κ : Type) (m : ℕ) :
    orig S κ ^ (m + 1) ≤ (orig S' κ ^ (m + 1)).comap (MvPolynomial.map ψ) := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow, orig, Ideal.map_span, ← Set.range_comp]
  apply le_of_eq
  congr 2
  ext i
  simp
def jetBC (κ : Type) (m : ℕ) : Jet S κ m →+* Jet S' κ m :=
  Ideal.quotientMap _ (MvPolynomial.map ψ) (orig_pow_le_comap ψ κ m)
theorem jetBC_algebraMap (κ : Type) (m : ℕ) (s : S) :
    jetBC ψ κ m (algebraMap S (Jet S κ m) s) = algebraMap S' (Jet S' κ m) (ψ s) := by
  simp [jetBC, MvPolynomial.algebraMap_eq]
  rfl
end Jet
section Over
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X)
def rjBC (d m n : ℕ) : rjO (spMap ψ ≫ x0) d m n ⟶ rjO x0 d m n :=
  Over.homMk (spMap (jetBC ψ (Fin n × Fin d) m)) (by
    dsimp
    simp only [spMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    ext s
    exact jetBC_algebraMap ψ _ m s)
def ptBC : ptO Xo (spMap ψ ≫ x0) ⟶ ptO Xo x0 := Over.homMk (spMap ψ) rfl
end Over
def RawBCSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]
    (S S' : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] [CommRing S'] [Algebra c.F S'] [Algebra ℚ S']
    (ψ : S →ₐ[c.F] S') (x0 : Sp S ⟶ Xo.X)
    (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left))
    (C : RChartAt Xo c x0 u),
    ∃ (B' : Germ.FB S' C.d (𝓞 E)) (x' : ∀ m, rjO (spMap (ψ : S →+* S') ≫ x0) C.d m 1 ⟶ Xo.univ.t.G)
      (e' : ∀ m, RFrTy (spMap (ψ : S →+* S') ≫ x0) C.d x' m),
      (∀ m, x' m = rjBC (ψ : S →+* S') x0 C.d m 1 ≫ C.x m) ∧
      (∀ i, B'.G.F i = MvPowerSeries.map (ψ : S →+* S') (C.B.G.F i)) ∧
      (∀ a i, B'.A.act a i = MvPowerSeries.map (ψ : S →+* S') (C.B.A.act a i)) ∧
      B'.ph1 = MvPowerSeries.map (ψ : S →+* S') C.B.ph1 ∧ B'.ph2 = MvPowerSeries.map (ψ : S →+* S') C.B.ph2 ∧
      B'.sy = MvPowerSeries.map (ψ : S →+* S') C.B.sy ∧
      (∀ a, B'.ad a = MvPowerSeries.map (ψ : S →+* S') (C.B.ad a)) ∧
      RIsChart (spMap (ψ : S →+* S') ≫ x0) (fun τ i => spMap (dualMap (ψ : S →+* S')) ≫ u τ i) C.d B'.G.F B'.A.act
        (fun ℓ j => ψ (C.uvec ℓ j)) x' ∧
      RIsFrame (spMap (ψ : S →+* S') ≫ x0) C.d x' B'.G.F B'.A.act B'.ph1 B'.ph2 B'.sy B'.ad e' ∧
      B'.IsCanonGauge S' (MvPowerSeries.map (ψ : S →+* S') C.h) ∧
      LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
        (LB.pullGen Xo.univ.t.PP.L _ _ (reL (spMap (ψ : S →+* S') ≫ x0) C.d x' B'.A.act e' C.wP 0)
          (homAt (spMap (ψ : S →+* S') ≫ x0) (jetAug : Jet S' (Fin 1 × Fin C.d) 0 →ₐ[S'] S')).left)
        (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt (spMap (ψ : S →+* S') ≫ x0) S') 1) ∧
      ∀ (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo x0)))
        (F' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo (spMap (ψ : S →+* S') ≫ x0))))
        (f : MvPowerSeries (Fin 1 × Fin C.d) S),
        IsPullSec Xo.univ.t.G Xo.univ.t.PP.L k (ptBC (ψ : S →+* S') x0 ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F F' →
        RIsGerm x0 C.d C.x C.B.A.act C.e C.wP k F f →
        RIsGerm (spMap (ψ : S →+* S') ≫ x0) C.d x' B'.A.act e' C.wP k F' (MvPowerSeries.map (ψ : S →+* S') f)
def NabMapSt : Prop :=
  ∀ (S S' : Type) [CommRing S] [Algebra ℚ S] [CommRing S'] [Algebra ℚ S'] (ψ : S →+* S') (d : ℕ)
    (O : Type) [CommRing O] [StarRing O] (B : Germ.FB S d O) (B' : Germ.FB S' d O),
    (∀ i, B'.G.F i = MvPowerSeries.map ψ (B.G.F i)) →
    (∀ a i, B'.A.act a i = MvPowerSeries.map ψ (B.A.act a i)) →
    ∀ (h : Germ.PS S 2 d), B.IsCanonGauge S h →
    ∀ (w0 : O) (m : ℕ) (f : Germ.PS S 1 d) (κ : Type) [Fintype κ] (u : κ → Fin d → S) (P : MvPolynomial κ S),
      B'.nabVal S' (MvPowerSeries.map ψ h) w0 m (MvPowerSeries.map ψ f) (fun l j => ψ (u l j)) (MvPolynomial.map ψ P) =
        ψ (B.nabVal S h w0 m f u P)
end Formalism.MainNotions.ModuliIntegralCharts.H1


