-- Prove2me | Definitions.Def_dusart_mesh_dusart_submission_glue
-- name    : dusart_mesh_dusart_submission_glue
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T18:26:11.933547+00:00
-- url     : https://prove2.me/theorems/f7a2716c-80b0-4152-a59d-392fb562a33f
-- title:
--   Dusart finite mesh: DusartSubmissionGlue
-- statement:
--   The DusartSubmissionGlue component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_full_lower
import Definitions.Def_dusart_mesh_upper_seed_tight
import Definitions.Def_dusart_mesh_large_upper_numerical
import Definitions.Def_dusart_theta_mesh_soundness
set_option maxHeartbeats 0
namespace DusartFiniteMesh
theorem finite_mesh_of_upper_chain_complete
    (hc : DusartMeshUpper.Literal.Spec 100000000 10000064768 99989691935170 10000013784295984)
    (n : ℕ) (hn : 32 ≤ n) (hcap : n ≤ Nat.ceil (16 * Real.exp 23)) :
    let a : ℝ := (n : ℝ) / 16
    let b : ℝ := ((n : ℝ) + 1) / 16
    |Chebyshev.theta a - a| ≤ (1513 / 10 : ℝ) * a / (Real.log b)^4 ∧
      |Chebyshev.theta a - b| ≤ (1513 / 10 : ℝ) * a / (Real.log b)^4 := by
  by_cases hs : n < 1600000000
  · exact finite_mesh_through_hundred_million n hn hs
  have hn' : (1600000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1600000000 ≤ n by omega)
  have ha : (100000000 : ℝ) ≤ (n : ℝ)/16 := by linarith
  have hA := mesh_cap n hcap
  have hupper := (hc DusartMeshUpper.theta_seed_tight).2 ((n : ℝ)/16) ha (by norm_num; linarith only [hA])
  have hU := large_upper_transfer ((n : ℝ)/16) ha hA hupper
  have hL := full_mesh_lower_errors n hn hcap
  dsimp only at hL ⊢
  rw [show ((n : ℝ)+1)/16=(n : ℝ)/16+1/16 by ring] at hL ⊢
  constructor <;> apply abs_le.2 <;> constructor <;> linarith only [hU.1,hU.2,hL.1,hL.2]
end DusartFiniteMesh


