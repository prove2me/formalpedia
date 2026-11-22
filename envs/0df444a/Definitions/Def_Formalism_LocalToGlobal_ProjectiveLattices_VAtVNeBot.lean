-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:51:33.917503+00:00
-- url     : https://prove2.me/theorems/9c419e13-b09c-4cb7-950f-31567edb40c7
-- title:
--   VAt VNe Bot
-- statement:
--   Definitions and structural lemmas for VAt VNe Bot, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/VAtVNeBot.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
section Bundles
variable {X Y : Scheme.{0}}
def IsoMaps {L M : LB X} (w : LB.Iso L M) (s : LB.Sec L) (s' : LB.Sec M) : Prop :=
  ∀ (i : M.ι) (k : L.ι),
    (X.presheaf.map (homOfLE (inf_le_left : M.U i ⊓ L.U k ≤ M.U i)).op).hom (s'.f i) =
      (show Γ(X, M.U i ⊓ L.U k) from (w.s (i, k) : Γ(X, (LB.div M L).U (i, k)))) *
        (X.presheaf.map (homOfLE (inf_le_right : M.U i ⊓ L.U k ≤ L.U k)).op).hom (s.f k)
def PullSec {L : LB X} (f : Y ⟶ X) (s : LB.Sec L) (s' : LB.Sec (L.pull f)) : Prop :=
  ∀ j (h : (L.pull f).U j ≤ f ⁻¹ᵁ L.U (j PUnit.unit)), s'.f j = (f.appLE _ _ h).hom (s.f (j PUnit.unit))
end Bundles
section Sab
variable {S S' : Scheme.{0}}
def RigIso {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f)
    (w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)) : Prop :=
  w.IsGen ∧ LB.Gen.Maps (LB.linCombIso w (K := PUnit.{1}) (fun _ => eSec t'.G) (fun _ => 1)) t'.PP.rig
    (m.cm.rigPull t.PP.L t.PP.rig)
end Sab
section Integral
variable (Xo : Moduli Dw l) (c : Coeff l)
def IsEigV {V Fr : Type} [CommRing V] [Field Fr] [Algebra V Fr] (io : c.F →+* Fr) (G : SAB H (Sp V))
    (τ : E →+* ℂ) (v : epsOver V V ⟶ G.G) : Prop :=
  ∀ (a : 𝓞 E) (z : V), algebraMap V Fr z = io (embK c τ a) →
    (v ≫ G.act.act a).left = spMap (epsMul z) ≫ v.left
variable {Xo c}
def Integral (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) : Prop :=
  letI := io.toAlgebra
  ∃ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (m1 : SABMap t' Xo.univ.t y.x)
    (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))),
    (∃ ub : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G.G),
      (∀ τ i, IsTan (ub τ i)) ∧ (∀ τ i, IsEigV c io G τ (ub τ i)) ∧
      (∀ τ (w : epsOver T.V T.V ⟶ G.G), IsTan w → IsEigV c io G τ w →
        ∃! a : Fin (Dw.mult τ) → T.V, IsComb (ub τ) a w) ∧
      ∀ τ i, ∃ u' : Sp (DualNumber T.Fr) ⟶ t'.G.left, u' ≫ m1.φ = y.u τ i ∧
        u' ≫ m2.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (ub τ i).left) ∧
    ∃ θ : LB.Sec G.PP.L,
      (∀ σ : LB.Sec G.PP.L, ∃! a : T.V, ∀ i,
        σ.f i = resG G.G.left le_top ((G.G.hom).appTop.hom (toΓ T.V a)) * θ.f i) ∧
      ∃ (w1 : LB.Iso t'.PP.L (Xo.univ.t.PP.L.pull m1.φ)) (w2 : LB.Iso t'.PP.L (G.PP.L.pull m2.φ))
        (σ : LB.Sec t'.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull m1.φ)) (θ2 : LB.Sec (G.PP.L.pull m2.φ)),
        RigIso m1 w1 ∧ RigIso m2 w2 ∧ IsoMaps w1 σ s1 ∧ IsoMaps w2 σ θ2 ∧ PullSec m2.φ θ θ2 ∧
        ∀ g : t'.G.left ⟶ Gx y.x, g ≫ (CartesianMonoidalCategory.snd (Over.mk y.x) Xo.univ.t.G).left = m1.φ →
          g ≫ (CartesianMonoidalCategory.fst (Over.mk y.x) Xo.univ.t.G).left = t'.G.hom →
          ∀ j (h : (Xo.univ.t.PP.L.pull m1.φ).U j ≤ g ⁻¹ᵁ (PPx y.x).U (fun _ => j PUnit.unit)),
            s1.f j = (g.appLE _ _ h).hom (y.s.f (fun _ => j PUnit.unit))
variable (Xo c)
def IntFr (T : CDVR) (io : c.F →+* T.Fr) : Type :=
  letI := io.toAlgebra
  {y : FrPt Xo c T.Fr // FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y ∧
    Integral T io y}
variable {Xo c}
def IntFr.IsAlg {T : CDVR} {io : c.F →+* T.Fr} (_y : IntFr Xo c T io) : Prop := T.FinRes
def evI {T : CDVR} {io : c.F →+* T.Fr} (y : IntFr Xo c T io) (f : Rul Xo c) : T.Fr :=
  letI := io.toAlgebra
  evR Xo c f y.1
section Points
variable (Xo c)
variable (cls : ∀ (T : CDVR) (io : c.F →+* T.Fr), IntFr Xo c T io → Prop) (PY : Type)
  (lies : ∀ (T : CDVR) (io : c.F →+* T.Fr), IntFr Xo c T io → PY → Prop)
def profI {T : CDVR} {io : c.F →+* T.Fr} (e : ℕ) (y : IntFr Xo c T io) (eta : PY) : (Rul Xo c → EReal) × PY :=
  (fun f => nval T.V e (evI y f), eta)
def PtV (la : HeightOneSpectrum (𝓞 c.F)) : Type :=
  {q : (Rul Xo c → EReal) × PY //
    ∃ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (_ : OverLa la T.V io e) (y : IntFr Xo c T io) (_ : cls T io y)
      (eta : PY) (_ : lies T io y eta), q = profI Xo c PY e y eta}
variable {Xo c cls PY lies}
def vAtV {la : HeightOneSpectrum (𝓞 c.F)} (y : PtV Xo c cls PY lies la) (f : Rul Xo c) : EReal := y.1.1 f
def imgV {la : HeightOneSpectrum (𝓞 c.F)} (y : PtV Xo c cls PY lies la) : PY := y.1.2
def PtV.mk (la : HeightOneSpectrum (𝓞 c.F)) {T : CDVR} {io : c.F →+* T.Fr} {e : ℕ} (ho : OverLa la T.V io e)
    (y : IntFr Xo c T io) (hy : cls T io y) (eta : PY) (heta : lies T io y eta) : PtV Xo c cls PY lies la :=
  ⟨profI Xo c PY e y eta, T, io, e, ho, y, hy, eta, heta, rfl⟩
variable {la : HeightOneSpectrum (𝓞 c.F)}
def PtV.widen {cls' : ∀ (T : CDVR) (io : c.F →+* T.Fr), IntFr Xo c T io → Prop}
    (h : ∀ T io y, cls T io y → cls' T io y) (y : PtV Xo c cls PY lies la) : PtV Xo c cls' PY lies la :=
  ⟨y.1, by
    obtain ⟨T, io, e, ho, z, hz, eta, heta, hq⟩ := y.2
    exact ⟨T, io, e, ho, z, h T io z hz, eta, heta, hq⟩⟩
end Points
section Open
variable (Xo c)
def UnitIndep : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (y y' : IntFr Xo c T io) (t : Ix Dw → T.Frˣ),
      (letI := io.toAlgebra; FrBor t y.1 y'.1) → ∀ e : ℕ, nval T.V e (evI y f) = nval T.V e (evI y' f)
def IntFrNe (cls : ∀ (T : CDVR) (io : c.F →+* T.Fr), IntFr Xo c T io → Prop) : Prop :=
  ∀ la : HeightOneSpectrum (𝓞 c.F), ∃ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (_ : OverLa la T.V io e)
    (y : IntFr Xo c T io), cls T io y
end Open
end Integral
end Formalism.L2.Pj


