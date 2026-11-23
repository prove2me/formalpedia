-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_InvOmega
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_InvOmega
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:00:16.605053+00:00
-- url     : https://prove2.me/theorems/cf3b1347-6f42-4958-ae09-6d6c55dff3f0
-- title:
--   Inv Omega
-- statement:
--   Definitions and structural lemmas for Inv Omega, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/InvOmega.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JetsPhW
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InverseOmegaHolds
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTerTer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
namespace PI.JetsPhW.Inv
variable {p : ℕ} [Fact p.Prime]
noncomputable def intS (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] :=
  _root_.UpperTheory.Reformulated.B.PadicComplexValuationRing.intS p
theorem coeff_mul_memS {S : Subring ℂ_[p]} {f g : PowerSeries ℂ_[p]} {m : ℕ}
    (hf : ∀ i ≤ m, PowerSeries.coeff i f ∈ S) (hg : ∀ i ≤ m, PowerSeries.coeff i g ∈ S) :
    PowerSeries.coeff m (f * g) ∈ S := by
  rw [PowerSeries.coeff_mul]
  refine S.sum_mem fun x hx => S.mul_mem (hf _ ?_) (hg _ ?_)
  · have := Finset.HasAntidiagonal.mem_antidiagonal.mp hx; omega
  · have := Finset.HasAntidiagonal.mem_antidiagonal.mp hx; omega
def serS (S : Subring ℂ_[p]) : Subring (PowerSeries ℂ_[p]) where
  carrier := {f | ∀ n, PowerSeries.coeff n f ∈ S}
  mul_mem' {f g} hf hg n := coeff_mul_memS (fun i _ => hf i) (fun i _ => hg i)
  one_mem' n := by
    rw [PowerSeries.coeff_one]
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  add_mem' {f g} hf hg n := by
    rw [map_add]; exact S.add_mem (hf n) (hg n)
  zero_mem' n := by simp
  neg_mem' {f} hf n := by
    rw [map_neg]; exact S.neg_mem (hf n)
def vInv (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : PowerSeries ℂ_[p] :=
  1 - (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * PowerSeries.X +
    algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₂ * PowerSeries.X ^ 2 +
    2 * algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * (PowerSeries.X ^ 3 * wq) +
    2 * algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₄ * PowerSeries.X * (PowerSeries.X ^ 3 * wq) +
    3 * algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₆ * (PowerSeries.X ^ 3 * wq) ^ 2)
end PI.JetsPhW.Inv


