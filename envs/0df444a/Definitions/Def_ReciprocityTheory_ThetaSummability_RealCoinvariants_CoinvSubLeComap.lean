-- Prove2me | Definitions.Def_ReciprocityTheory_ThetaSummability_RealCoinvariants_CoinvSubLeComap
-- name    : ReciprocityTheory_ThetaSummability_RealCoinvariants_CoinvSubLeComap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:01.249633+00:00
-- url     : https://prove2.me/theorems/089a139e-1875-4554-b262-e9d672972dc4
-- title:
--   Coinv Sub Le Comap
-- statement:
--   Definitions and structural lemmas for Coinv Sub Le Comap, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaSummability/RealCoinvariants/CoinvSubLeComap.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaSummability_RealCoinvariants_GlRelZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ThetaSummability.Real
variable {M : Type*} [AddCommGroup M] [Module ℂ M] {ι : Type*}
def coinvSub (Y : ι → Module.End ℂ M) (μ : ι → ℂ) : Submodule ℂ M :=
  ⨆ i, LinearMap.range (Y i - μ i • 1)
def jointEig (Y : ι → Module.End ℂ M) (μ : ι → ℂ) : Submodule ℂ M :=
  ⨅ i, LinearMap.ker (Y i - μ i • 1)
abbrev Coinv (Y : ι → Module.End ℂ M) (μ : ι → ℂ) := M ⧸ coinvSub Y μ
theorem coinvSub_le_comap {Y : ι → Module.End ℂ M} (μ : ι → ℂ) {T : Module.End ℂ M}
    (hT : ∀ i, Commute T (Y i)) : coinvSub Y μ ≤ (coinvSub Y μ).comap T := by
  unfold coinvSub
  apply iSup_le
  intro i
  rintro x ⟨y, rfl⟩
  rw [Submodule.mem_comap]
  apply Submodule.mem_iSup_of_mem i
  refine ⟨T y, ?_⟩
  have hc : T (Y i y) = Y i (T y) := by
    rw [← Module.End.mul_apply, (hT i).eq, Module.End.mul_apply]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, hc]
def coinvOp {Y : ι → Module.End ℂ M} (μ : ι → ℂ) (T : Module.End ℂ M)
    (hT : ∀ i, Commute T (Y i)) : Module.End ℂ (Coinv Y μ) :=
  (coinvSub Y μ).mapQ (coinvSub Y μ) T (coinvSub_le_comap μ hT)
end ReciprocityTheory.ThetaSummability.Real


