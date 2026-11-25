-- Prove2me | Definitions.Def_CompanionTheory_AutomorphicTheory_NumberFieldModels_NFTieProv
-- name    : CompanionTheory_AutomorphicTheory_NumberFieldModels_NFTieProv
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T04:56:19.161627+00:00
-- url     : https://prove2.me/theorems/d6569735-94ad-51a7-bddc-96ce46061395
-- title:
--   NFTie Prov
-- statement:
--   Definitions and structural lemmas for NFTie Prov, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/NumberFieldModels/NFTieProv.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGaugeCut
import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_StatementTL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.CutMP.Gauge
namespace Formalism.MainStatements.NFTie
noncomputable section
section defs
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
def GaugeQQ (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), FamR P Bs Dc Φ →
    ∀ (Y : ℝ) (a b : Fin 2) (ρ : M.Ty P),
      MA.toSm P (rawR P Bs.μsec e (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b Φ) ρ) =
        MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b) (fun ρ' => MA.toSm P (rawR P Bs.μsec e Φ ρ')) ρ
def tr (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : M.Ty P → MA.SmQ P.r P.TT :=
  fun ρ => MA.toSm P (rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ)
def Tied (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (a : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (am : MA.A P (MA.DQ P)) : Prop :=
  ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π', tr P Bs e (a.1 Φ) = MA.actA P am (tr P Bs e Φ)
end defs
structure GenRel {A A' : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Ring A'] [StarRing A'] [Algebra ℂ A'] {r : ℕ}
    (Rl : Subalgebra ℂ (A × A')) (L : R.LevelData A r) (st : Fr.Start A) (L' : R.LevelData A' r) (st' : Fr.Start A') :
    Prop where
  p : ∀ l, (L.p l, L'.p l) ∈ Rl ∧ (star (L.p l), star (L'.p l)) ∈ Rl
  c : ∀ l, (L.c l, L'.c l) ∈ Rl ∧ (star (L.c l), star (L'.c l)) ∈ Rl
  ci : ∀ l, (L.ci l, L'.ci l) ∈ Rl ∧ (star (L.ci l), star (L'.ci l)) ∈ Rl
  ζ : (L.ζ, L'.ζ) ∈ Rl
  ζi : (L.ζi, L'.ζi) ∈ Rl
  ζb : (L.ζb, L'.ζb) ∈ Rl
  ζbi : (L.ζbi, L'.ζbi) ∈ Rl
  GG : (L.GG, L'.GG) ∈ Rl
  GGi : (L.GGi, L'.GGi) ∈ Rl
  QQ : ∀ Y : ℂ, star Y = Y → ∀ a b, (st.QQ Y a b, st'.QQ Y a b) ∈ Rl
  xi : ∀ Y : ℂ, star Y = Y → Y ∈ st.inv → Y ∈ st'.inv → (st.xi Y, st'.xi Y) ∈ Rl
def AlgTie : Prop :=
  ∀ (A A' S : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Ring A'] [StarRing A'] [Algebra ℂ A']
    [StarModule ℂ A'] [Fintype S] [DecidableEq S] (r : ℕ) (Rl : Subalgebra ℂ (A × A'))
    (L : R.LevelData A r) (st : Fr.Start A) (L' : R.LevelData A' r) (st' : Fr.Start A') (w : List (Wd.Letter ℂ S)),
    GenRel Rl L st L' st' → Fr.IsStarLevel L → Fr.IsLevelStart L st → Fr.IsStarLevel L' → Fr.IsLevelStart L' st' →
    Fr.admitted st w → Fr.admitted st' w →
    ∀ e e' : Wd.Ix S, (((Fr.ofWord L st w).F * TL.bTA L w) e e', ((Fr.ofWord L' st' w).F * TL.bTA L' w) e e') ∈ Rl
def NFTieProv : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (Lm : R.LevelData (MA.A P (MA.DQ P)) P.r),
    IsFrameB P p.T.base e → GaugeQQ P p.T.base e → MA.IsModelLevel P (MA.DQ P) Lm →
    ∀ w : List C.Letter, KB.CutWord P p.l0 w → ∀ (a : Wd.Ix (Fin w.length)) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)),
      KB.CptCoef p.T.base F →
      trJB P p.T.base e (B.JF p.T.base (p.Θ.Θ w a F)) =
        MA.actA P (((Fr.ofWord Lm (MA.startM P (MA.DQ P) p.l0) (D.positionted w)).F * TL.bTA Lm (D.positionted w)) a Wd.e1)
          (trJB P p.T.base e (B.JF p.T.base F))
end
end Formalism.MainStatements.NFTie


