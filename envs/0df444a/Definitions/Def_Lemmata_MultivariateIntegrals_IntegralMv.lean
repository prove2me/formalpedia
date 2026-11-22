-- Prove2me | Definitions.Def_Lemmata_MultivariateIntegrals_IntegralMv
-- name    : Lemmata_MultivariateIntegrals_IntegralMv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:06:57.955597+00:00
-- url     : https://prove2.me/theorems/59a76529-0662-49f9-9c95-f8ecf302a91e
-- title:
--   Integral Mv
-- statement:
--   Definitions and structural lemmas for Integral Mv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/MultivariateIntegrals/IntegralMv.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v w
noncomputable def Bl.ProductIntegralBounds.IntegralMv :
  {K : Type u} → [NormedField.{u} K] → {ι : Type v} → MvPowerSeries.{v, u} ι K → Prop :=
  fun {K : Type u} [NormedField.{u} K] {ι : Type v} (F : MvPowerSeries.{v, u} ι K) ↦
    ∀ (d : Finsupp.{v, 0} ι Nat),
      LE.le.{0}
        (Norm.norm.{u} (DFunLike.coe.{max (v + 1) (u + 1), max (v + 1) (u + 1), u + 1} (MvPowerSeries.coeff.{v, u} d) F))
        1
noncomputable def Bl.ProductIntegralBounds.Bd :
  {K : Type u} → [NormedField.{u} K] → {τ : Type w} → Real → MvPowerSeries.{w, u} τ K → Prop :=
  fun {K : Type u} [NormedField.{u} K] {τ : Type w} (C : Real) (F : MvPowerSeries.{w, u} τ K) ↦
    ∀ (d : Finsupp.{w, 0} τ Nat),
      LE.le.{0}
        (Norm.norm.{u} (DFunLike.coe.{max (u + 1) (w + 1), max (u + 1) (w + 1), u + 1} (MvPowerSeries.coeff.{w, u} d) F))
        C
namespace Bl.ProductIntegralBounds
end Bl.ProductIntegralBounds


