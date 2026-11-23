-- Prove2me | Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_TrivCrys
-- name    : Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_TrivCrys
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:03.822326+00:00
-- url     : https://prove2.me/theorems/e0982de1-f37f-41ed-9b11-b3b8016651fc
-- title:
--   Triv Crys
-- statement:
--   Definitions and structural lemmas for Triv Crys, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/TrivCrys.lean

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
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
open Module TensorProduct
section TrivCrysProof
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B]
    [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR]
    [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
def trivCrysIncl : K₀ →ₗ[Qp] B := (Algebra.linearMap K₀ B).restrictScalars Qp
def trivCrysMap : LL ⊗[Qp] K₀ →ₗ[LL] LL ⊗[Qp] B :=
  AlgebraTensorModule.lTensor LL LL (trivCrysIncl (Qp := Qp) (K₀ := K₀) (B := B))
variable [FiniteDimensional Qp LL]
def trivCrysCoord (b : Basis (Fin (finrank Qp LL)) Qp LL) (i : Fin (finrank Qp LL)) :
    LL ⊗[Qp] B →ₗ[Qp] B :=
  (TensorProduct.lid Qp B).toLinearMap ∘ₗ LinearMap.rTensor B (b.coord i)
end TrivCrysProof
end Formalism.WeaklyAdmissibleFiltrations


