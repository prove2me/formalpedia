-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreCut
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreCut
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T17:10:00.232304+00:00
-- url     : https://prove2.me/theorems/bebd7248-e3d2-47e7-9a84-2c64e5562c5d
-- title:
--   Cut GCore Cut
-- statement:
--   Definitions and structural lemmas for Cut GCore Cut, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreCut.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGaugeCut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
noncomputable section
def CSec (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μ0 : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Prop :=
  IsSection k r z z' μ0 ∧ ∀ ζ ζ' : ℂ, Tz k r z * Tz k r z' < Complex.normSq ζ → Tz k r z * Tz k r z' < Complex.normSq ζ' →
    NF.Stab k r z z' μ0 ζ = NF.Stab k r z z' μ0 ζ'
def GCoreSec : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → CSec P.k P.r Bs.z Bs.z' Bs.μsec →
    ∃ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e ∧
      ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), FamR P Bs Dc Φ →
        ∀ (Y : ℝ) (a b : Fin 2) (ρ : M.Ty P),
          MA.toSm P (rawR P Bs.μsec e (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b Φ) ρ) =
            MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b) (fun ρ' => MA.toSm P (rawR P Bs.μsec e Φ ρ')) ρ
def SecExists : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∃ μ0, CSec P.k P.r Bs.z Bs.z' μ0
def SecMove : Prop := SecExists → GCoreSec → GCore
def trR {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : M.Ty P → MA.SmQ P.r P.TT :=
  fun ρ => MA.toSm P (rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ)
def FamLocal : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r))
      (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), FamR P Bs Dc Φ →
    ∀ q : MA.Qp P.r P.TT, ∃ Φt : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π', ∃ V ∈ nhds q.1.2,
      ∀ ζ' ∈ V, (Φt : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec ζ') = Φ q.1.1 (NF.muZ P.k P.r Bs.μsec ζ') ∧
        ∀ (Y : ℂ) (a b : Fin 2), (X.t Y a b Φt : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec ζ') =
          Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) Y a b Φ q.1.1 (NF.muZ P.k P.r Bs.μsec ζ')
def GenTransfer : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → CSec P.k P.r Bs.z Bs.z' Bs.μsec →
    ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
      Q.IsActualLevel X d.L → Fr.IsStarLevel d.L → d.Rel → (∀ Y : ℂ, X.QQ Y = d.QQ Y) →
      ∃ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e ∧
        ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
          trR P Bs e (d.L.ζ.1 Φ) = MA.actA P (MA.zA P (MA.DQ P)) (trR P Bs e Φ) ∧
          trR P Bs e (d.L.ζi.1 Φ) = MA.actA P (MA.ziA P (MA.DQ P)) (trR P Bs e Φ) ∧
          trR P Bs e (d.L.ζb.1 Φ) = MA.actA P (MA.zbA P (MA.DQ P)) (trR P Bs e Φ) ∧
          trR P Bs e (d.L.ζbi.1 Φ) = MA.actA P (MA.zbiA P (MA.DQ P)) (trR P Bs e Φ) ∧
          trR P Bs e (d.L.GG.1 Φ) = MA.actA P (MA.ggA P (MA.DQ P)) (trR P Bs e Φ) ∧
          trR P Bs e (d.L.GGi.1 Φ) = MA.actA P (MA.ggiA P (MA.DQ P)) (trR P Bs e Φ) ∧
          trR P Bs e (d.L.nab.1 Φ) = MA.actA P (MA.nabA P (MA.DQ P)) (trR P Bs e Φ) ∧
          trR P Bs e (d.L.nabs.1 Φ) = MA.actA P (MA.nabsA P (MA.DQ P)) (trR P Bs e Φ) ∧
          (∀ f : M.Ty P → ℂ, trR P Bs e ((d.κ f).1 Φ) = MA.actA P (MA.kap P (MA.DQ P) f) (trR P Bs e Φ)) ∧
          (∀ l ∈ Finset.Icc 1 (P.k - 1),
            trR P Bs e ((d.SS l).1 Φ) = MA.actA P (MA.SS P (MA.DQ P) l) (trR P Bs e Φ)) ∧
          ∀ l ∈ Finset.Icc 1 (P.k - 1),
            trR P Bs e ((star (d.SS l)).1 Φ) = MA.actA P (star (MA.SS P (MA.DQ P) l)) (trR P Bs e Φ)
def GenTransferQQ : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → CSec P.k P.r Bs.z Bs.z' Bs.μsec →
    ∀ X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π',
      ∃ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e ∧
        ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (Y : ℂ) (a b : Fin 2),
          trR P Bs e (X.t Y a b Φ) = MA.actA P (MA.QQr P (MA.DQ P) Y a b) (trR P Bs e Φ)
def ModelLocal : Prop :=
  ∀ (P : M.Par) (f g : M.Ty P → MA.SmQ P.r P.TT) (c : Fin P.r → ℂ) (V : Set ℂ), IsOpen V →
    (∀ ρ (q : MA.Qp P.r P.TT), q.1.1 = c → q.1.2 ∈ V → (f ρ : MA.Qp P.r P.TT → ℂ) q = (g ρ : MA.Qp P.r P.TT → ℂ) q) →
    ∀ (Y : ℂ) (a b : Fin 2) ρ (q : MA.Qp P.r P.TT), q.1.1 = c → q.1.2 ∈ V →
      (MA.actA P (MA.QQr P (MA.DQ P) Y a b) f ρ : MA.Qp P.r P.TT → ℂ) q =
        (MA.actA P (MA.QQr P (MA.DQ P) Y a b) g ρ : MA.Qp P.r P.TT → ℂ) q
def RadSpSmooth : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e →
    ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') ρ,
      rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ ∈ MA.smSub P.r P.TT
def GenToQQ : Prop := RadSpSmooth → GenTransfer → GenTransferQQ
def AsmSec : Prop := FamLocal → GenTransferQQ → ModelLocal → RadSpSmooth → GRawSmooth → GQLFam → GCoreSec
def GCoreOfCut : Prop :=
  SecExists → SecMove → FamLocal → GenTransfer → GenToQQ → ModelLocal → RadSpSmooth → GRawSmooth → GQLFam → AsmSec → GCore
end
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC


