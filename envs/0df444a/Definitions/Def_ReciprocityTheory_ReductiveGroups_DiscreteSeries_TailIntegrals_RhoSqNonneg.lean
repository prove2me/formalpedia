-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RhoSqNonneg
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RhoSqNonneg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:30:39.094493+00:00
-- url     : https://prove2.me/theorems/c4d7625e-a115-48b5-8aeb-9cbd6061ed0e
-- title:
--   Rho Sq Nonneg
-- statement:
--   Definitions and structural lemmas for Rho Sq Nonneg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/RhoSqNonneg.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace OSAux
def gL (τ : ℝ) (p : ℕ) (i : Fin (p + 1)) : ℂ →ₗ[ℝ] ℂ :=
  if i = 0 then τ • LinearMap.id else LinearMap.id
def fL (τ : ℝ) (p : ℕ) : (Fin (p + 1) → ℂ) →ₗ[ℝ] (Fin (p + 1) → ℂ) :=
  LinearMap.pi (fun i => (gL τ p i).comp (LinearMap.proj i))
def sclL (τ : ℝ) (p m : ℕ) : Xp (p + 1) m →ₗ[ℝ] Xp (p + 1) m :=
  LinearMap.prodMap (fL τ p) (LinearMap.prodMap (fL τ⁻¹ p) LinearMap.id)
end OSAux
end ReciprocityTheory.ChartRestriction.DS.Xi


