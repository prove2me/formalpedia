-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PeriodDataComparison
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PeriodDataComparison
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:04:17.249402+00:00
-- url     : https://prove2.me/theorems/b6f7a971-ccdb-4885-b1c6-f72ca01ab692
-- title:
--   Period Data Comparison
-- statement:
--   Definitions and structural lemmas for Period Data Comparison, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PeriodDataComparison.lean

import Mathlib
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
open Formalism.WeaklyAdmissibleFiltrations
namespace GlobalTheory.SplitJump
open Module TensorProduct
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) {n : ℕ} (e : Basis (Fin n) Qp V)
def coord (BdR : Type) [CommRing BdR] [Algebra Qp BdR] : V ⊗[Qp] BdR ≃ₗ[Qp] (Fin n → BdR) :=
  (TensorProduct.comm Qp V BdR).trans ((Algebra.TensorProduct.basis BdR e).equivFun.restrictScalars Qp)
end GlobalTheory.SplitJump


