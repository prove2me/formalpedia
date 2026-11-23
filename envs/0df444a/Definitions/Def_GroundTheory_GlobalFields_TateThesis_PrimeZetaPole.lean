-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
-- name    : GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:37.181807+00:00
-- url     : https://prove2.me/theorems/39011b88-079b-4907-a4f4-23f187eb1fe8
-- title:
--   Prime Zeta Pole
-- statement:
--   Definitions and structural lemmas for Prime Zeta Pole, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/PrimeZetaPole.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Global
open NumberField IsDedekindDomain Filter Topology Set Ideal
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
def dedekindZetaTerm (s : ℝ) (n : ℕ) : ℝ :=
  (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℝ) * (n : ℝ) ^ (-s)
def dedekindZetaReal (s : ℝ) : ℝ :=
  ∑' n, dedekindZetaTerm K s n
theorem finite_absNorm_lt (N : ℕ) : {I : Ideal (𝓞 K) | absNorm I < N}.Finite := by
  have : {I : Ideal (𝓞 K) | absNorm I < N} = ⋃ n ∈ Set.Iio N, {I | absNorm I = n} := by
    ext I
    simp
  rw [this]
  exact (Set.finite_Iio N).biUnion fun n _ => Ideal.finite_setOfPred_absNorm_eq n
variable {K}
def heightOneOfPrime {p : Ideal (𝓞 K)} (hp : Prime p) : HeightOneSpectrum (𝓞 K) :=
  ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
end
end GroundTheory.Global


