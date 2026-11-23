-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementC
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:27.643612+00:00
-- url     : https://prove2.me/theorems/1387b90a-fece-4b49-b762-4283fbbcc0e7
-- title:
--   Statement C
-- statement:
--   Definitions and structural lemmas for Statement C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/StatementC.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_CompInv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
namespace Formalism.L2.Th1.A
abbrev curveS {R : Type u} [CommRing R] (W : WeierstrassCurve R) : WeierstrassCurve R⟦X⟧ :=
  W.map (C : R →+* R⟦X⟧)
abbrev curveL {R : Type u} [CommRing R] (W : WeierstrassCurve R) :
    WeierstrassCurve (LaurentSeries R) :=
  W.map (HahnSeries.C : R →+* LaurentSeries R)
def WSerSpec : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    Formalism.ELL.WFixed W (wSer W) ∧ ∀ w : R⟦X⟧, Formalism.ELL.WFixed W w → w = wSer W
def WSerFactor : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    wSer W = X ^ 3 * wU W ∧ constantCoeff (wU W) = 1 ∧ wU W * xS W = 1 ∧
    constantCoeff (xS W) = 1 ∧ constantCoeff (yS W) = -1
def UnitSpec : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    constantCoeff (fw W) = 1 ∧ fw W * om W = 1 ∧ constantCoeff (om W) = 1 ∧
    coeff 1 (om W) = W.a₁ ∧ coeff 2 (om W) = W.a₁ ^ 2 + W.a₂ ∧
    constantCoeff (iDen W) = -1 ∧ iDen W * invOfUnit (iDen W) (-1) = 1
def SeriesMap : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] (φ : R →+* S) (W : WeierstrassCurve R),
    PowerSeries.map φ (wSer W) = wSer (W.map φ) ∧ PowerSeries.map φ (wU W) = wU (W.map φ) ∧
    PowerSeries.map φ (xS W) = xS (W.map φ) ∧ PowerSeries.map φ (yS W) = yS (W.map φ) ∧
    PowerSeries.map φ (fw W) = fw (W.map φ) ∧ PowerSeries.map φ (fu W) = fu (W.map φ) ∧
    PowerSeries.map φ (om W) = om (W.map φ) ∧ PowerSeries.map φ (iSer W) = iSer (W.map φ)
def FlowU : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    IsDer (D W) ∧ ConstCurve (D W) (curveS W) ∧ IsFlowUW (curveS W) (D W) X (wSer W) ∧
    fwAt (curveS W) X (wSer W) = fw W ∧ fuAt (curveS W) X (wSer W) = fu W ∧
    ∀ f : R⟦X⟧, om W * D W f = derivative R f
def DLSpec : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    IsDer (DL W) ∧ ConstCurve (DL W) (curveL W) ∧ (∀ r : R, DL W (HahnSeries.C r) = 0) ∧
    ∀ f : R⟦X⟧, DL W (toL f) = toL (D W f)
def FlowL : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    IsFlow (curveL W) (DL W) (xL W) (yL W) ∧
    toL X * yL W = -xL W ∧ toL (wSer W) * yL W = -1 ∧ toL (wSer W) * xL W = toL X
def XLSq : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    DL W (xL W) ^ 2 = 4 * xL W ^ 3 + HahnSeries.C W.b₂ * xL W ^ 2 + 2 * HahnSeries.C W.b₄ * xL W
      + HahnSeries.C W.b₆ ∧
    DL W (DL W (xL W)) = 6 * xL W ^ 2 + HahnSeries.C W.b₂ * xL W + HahnSeries.C W.b₄
def ISerSpec : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    constantCoeff (iSer W) = 0 ∧ coeff 1 (iSer W) = -1 ∧ (iSer W).subst (iSer W) = X ∧
    (wSer W).subst (iSer W) = wSer W * invOfUnit (iDen W) (-1) ∧
    (xS W).subst (iSer W) = invOfUnit (iDen W) (-1) ^ 2 * xS W ∧
    (yS W).subst (iSer W) = invOfUnit (iDen W) (-1) ^ 3 *
      (-yS W - C W.a₁ * X * xS W - C W.a₃ * X ^ 3) ∧
    D W (iSer W) = -(fw W).subst (iSer W) ∧
    (om W).subst (iSer W) * derivative R (iSer W) = -om W
end Formalism.L2.Th1.A


