-- Prove2me | Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_WindowCount
-- name    : Formalism_WeaklyAdmissibleFiltrations_WindowCount
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:29:43.850442+00:00
-- url     : https://prove2.me/theorems/2e507f5c-93ab-49fd-8616-5d70324f0ab1
-- title:
--   Window Count
-- statement:
--   Definitions and structural lemmas for Window Count, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/WindowCount.lean

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.WeaklyAdmissibleFiltrations
open Module
def WindowCount : Prop :=
  ∀ (G : Type) [Group G] (Qp K₀ K : Type) [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    (B BdR : Type) [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B]
    [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR]
    [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) (LL : Type) [Field LL] [Algebra Qp LL]
    (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (lo hi : ℤ), lo ≤ hi →
    ∑ a ∈ Finset.Ico lo hi, multV PD ρ τ a =
      (finrank LL ↥(FildR PD ρ τ lo) : ℤ) - finrank LL ↥(FildR PD ρ τ hi)
end Formalism.WeaklyAdmissibleFiltrations


