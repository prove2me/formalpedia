-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DedekindZetaEqSumRealEisenstein
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DedekindZetaEqSumRealEisenstein
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:20:36.100502+00:00
-- url     : https://prove2.me/theorems/c46b878a-3e4e-4925-bebc-906ecbd5a15d
-- title:
--   Dedekind Zeta Eq Sum Real Eisenstein
-- statement:
--   Definitions and structural lemmas for Dedekind Zeta Eq Sum Real Eisenstein, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/DedekindZetaEqSumRealEisenstein.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoRealEisensteinSubPole
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module FractionalIdeal Filter Topology
open scoped nonZeroDivisors UpperHalfPlane Real
namespace GlobalTheory
open QuadraticZeta
namespace QuadraticZeta
end QuadraticZeta
variable {K : Type*} [Field K] [NumberField K] {d : ℕ}
def IsIdealClassPoint (σ : K →+* ℂ) (c : ClassGroup (𝓞 K)) (τ : ℍ) : Prop :=
  ∃ (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (ω : ℂ), ClassGroup.mk K 𝔞 = c ∧
    ∀ z, z ∈ σ '' 𝔞.1 ↔ ∃ m n : ℤ, ω * (m * (τ : ℂ) + n) = z
noncomputable def latticeLogPeriod (L : PeriodPair) : ℝ :=
  Real.log (ZLattice.covolume L.lattice / π) + Real.log ‖L.g₂ ^ 3 - 27 * L.g₃ ^ 2‖ / 6
section
variable [NeZero d] (h2 : finrank ℚ K = 2) (hD : discr K = -d) (hd : 4 < d)
  {χ : DirichletCharacter ℂ d} (hχ : IsKroneckerChar χ) (σ : K →+* ℂ)
include h2 hD hd hχ
variable {𝔞 : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ}
  (h𝔞 : ∀ c, ClassGroup.mk K (𝔞 c) = c) {L : ClassGroup (𝓞 K) → PeriodPair}
  (hL : ∀ c, ((L c).lattice : Set ℂ) = σ '' (𝔞 c).1)
include h𝔞 hL
end
end GlobalTheory


