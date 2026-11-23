-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:56:02.762154+00:00
-- url     : https://prove2.me/theorems/94d833c0-97f4-46b7-adf4-1b3883864bd0
-- title:
--   Frame Charts
-- statement:
--   Definitions and structural lemmas for Frame Charts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/FrameCharts.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnitIndepOfCharts
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
namespace Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
section Generic
variable {K : Type} [Field K] {ι : Type}
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)
variable (borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop)
def MapTrans : Prop :=
  ∀ (S T U : Type) [CommRing S] [Algebra K S] [CommRing T] [Algebra K T] [CommRing U] [Algebra K U]
    (φ : S →ₐ[K] T) (ψ : T →ₐ[K] U) (y : pts S) (z : pts T) (w : pts U),
    mapR φ y z → mapR ψ z w → mapR (ψ.comp φ) y w
def MapCancel : Prop :=
  ∀ (S T U : Type) [CommRing S] [Algebra K S] [CommRing T] [Algebra K T] [CommRing U] [Algebra K U]
    (φ : S →ₐ[K] T) (ψ : T →ₐ[K] U) (y : pts S) (z : pts T) (w : pts U),
    mapR φ y z → mapR (ψ.comp φ) y w → mapR ψ z w
def BorBC : Prop :=
  ∀ (S T : Type) [CommRing S] [Algebra K S] [CommRing T] [Algebra K T] (φ : S →ₐ[K] T) (t : ι → Sˣ)
    (y y' : pts S) (z z' : pts T), borR t y y' → mapR φ y z → mapR φ y' z' →
    borR (fun i => Units.map (φ : S →* T) (t i)) z z'
def IsMonoPt {A : Type} [CommRing A] [Algebra K A] (u : pts A) : Prop :=
  ∀ (T : Type) [CommRing T] [Algebra K T] (a a' : A →ₐ[K] T) (z : pts T), mapR a u z → mapR a' u z → a = a'
def AwayLift {P P' : Type} [CommRing P] [Algebra K P] [CommRing P'] [Algebra K P'] (lam : P →ₐ[K] P') (g : P) : Prop :=
  ∀ (T : Type) [CommRing T] [Algebra K T] (ψ : P →ₐ[K] T), IsUnit (ψ g) → ∃ μ : P' →ₐ[K] T, μ.comp lam = ψ
def ChartCls {S : Type} [CommRing S] [Algebra K S] (w : pts S) (m : Ideal S) [m.IsPrime] {A : Type} [CommRing A]
    [Algebra K A] (u : pts A) (c : A →ₐ[K] Localization.AtPrime m) : Prop :=
  ∃ wm : pts (Localization.AtPrime m), mapR (locM K m) w wm ∧ mapR c u wm
def ChartLoc {S : Type} [CommRing S] [Algebra K S] (w : pts S) (m : Ideal S) (A : TRing K) (u : pts A.R) : Prop :=
  ∀ (p : TRing K) (φ : p.R →ₐ[K] S) (y : pts p.R), mapR φ y w →
    ∃ g : p.R, φ g ∉ m ∧ ∃ (p' : TRing K) (lam : p.R →ₐ[K] p'.R) (y' : pts p'.R) (a : A.R →ₐ[K] p'.R),
      AwayLift lam g ∧ mapR lam y y' ∧ mapR a u y'
def BorOver (A : TRing K) (u : pts A.R) : Prop :=
  ∃ (B : TRing K) (uB uB' : pts B.R) (tB : ι → (B.R)ˣ) (π π' : A.R →ₐ[K] B.R),
    mapR π u uB ∧ mapR π' u uB' ∧ borR tB uB uB' ∧
    ∀ (T : Type) [CommRing T] [Algebra K T] (a a' : A.R →ₐ[K] T) (z z' : pts T) (t : ι → Tˣ),
      mapR a u z → mapR a' u z' → borR t z z' →
      ∃ b : B.R →ₐ[K] T, b.comp π = a ∧ b.comp π' = a' ∧ ∀ i, b (tB i : B.R) = (t i : T)
variable {pts mapR borR}
end Generic
section Frames
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
variable {c : Coeff l}
end Frames
section Clauses
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
def ChartCoverF : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (w w' : FrPt Xo c S), w'.x = w.x → ∀ (m : Ideal S) [m.IsMaximal],
    ∃ (A : TRing c.F) (u : FrPt Xo c A.R) (cw cw' : A.R →ₐ[c.F] Localization.AtPrime m),
      IsMonoPt (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) u ∧
      BorOver (K := c.F) (ι := Ix Dw) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)
        (fun t y y' => FrBor t y y') A u ∧
      ChartCls (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) w m u cw ∧
      ChartLoc (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) w m A u ∧
      ChartCls (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) w' m u cw' ∧
      ChartLoc (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) w' m A u
def FrBorBCF : Prop :=
  BorBC (K := c.F) (ι := Ix Dw) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun t y y' => FrBor t y y')
variable {Xo c}
end Clauses
section BorBCProof
open MonObj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
end BorBCProof
end Formalism.L2.Pj


