-- Prove2me | Definitions.Def_dusart_mesh_to_hundred_million
-- name    : dusart_mesh_to_hundred_million
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T18:17:48.610685+00:00
-- url     : https://prove2.me/theorems/4f7ee09a-5745-4080-8b71-0987545a047e
-- title:
--   Dusart finite mesh: ToHundredMillion
-- statement:
--   The ToHundredMillion component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Definitions.Def_dusart_mesh_mid_small_cases
import Definitions.Def_dusart_mesh_lower
import Definitions.Def_dusart_mesh_axler_transfer
import Definitions.Def_dusart_mesh_critical
import Definitions.Def_dusart_mesh_upper_cases_all
set_option maxHeartbeats 0

namespace DusartFiniteMesh

lemma both_endpoints_of_lower (a : ℝ) (ha : 0 ≤ a)
    (hu : Chebyshev.theta a ≤ a)
    (hl : a-Chebyshev.theta a ≤ (1513/10 : ℝ)*a/(Real.log (a+1/16))^4 ∧
      a+1/16-Chebyshev.theta a ≤ (1513/10 : ℝ)*a/(Real.log (a+1/16))^4) :
    |Chebyshev.theta a-a| ≤ (1513/10 : ℝ)*a/(Real.log (a+1/16))^4 ∧
      |Chebyshev.theta a-(a+1/16)| ≤ (1513/10 : ℝ)*a/(Real.log (a+1/16))^4 := by
  have hr : 0 ≤ (1513/10 : ℝ)*a/(Real.log (a+1/16))^4 := by positivity
  constructor <;> apply abs_le.2 <;> constructor <;> linarith [hl.1,hl.2]

theorem finite_mesh_through_hundred_million (n : ℕ) (hn : 32 ≤ n) (hcap : n < 1600000000) :
    let a : ℝ := (n : ℝ)/16
    let b : ℝ := ((n : ℝ)+1)/16
    |Chebyshev.theta a-a| ≤ (1513/10 : ℝ)*a/(Real.log b)^4 ∧
      |Chebyshev.theta a-b| ≤ (1513/10 : ℝ)*a/(Real.log b)^4 := by
  by_cases hsmall : n ≤ 4080
  · by_cases h512 : n ≤ 512
    · exact small_mesh n hn h512
    · exact medium_small_mesh n (by omega) hsmall
  by_cases hbig : 1121776 ≤ n
  · exact axler_mesh_range n hbig hcap
  have h255 : (255 : ℝ) ≤ (n : ℝ)/16 := by
    have hh : (4080 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 4080 ≤ n by omega)
    linarith
  have h70111 : (n : ℝ)/16 ≤ 70111 := by
    have hh : (n : ℝ) ≤ (1121776 : ℝ) := by exact_mod_cast (show n ≤ 1121776 by omega)
    linarith
  have hu := UpperScan.real_theta_upper ((n : ℝ)/16) h255 h70111
  have hl : (n : ℝ)/16-Chebyshev.theta ((n : ℝ)/16) ≤
      (1513/10 : ℝ)*((n : ℝ)/16)/(Real.log ((n : ℝ)/16+1/16))^4 ∧
      (n : ℝ)/16+1/16-Chebyshev.theta ((n : ℝ)/16) ≤
      (1513/10 : ℝ)*((n : ℝ)/16)/(Real.log ((n : ℝ)/16+1/16))^4 := by
    by_cases hlow : n ≤ 22720
    · have hh := lower_mesh_standard_ranges n (Or.inl ⟨by omega,hlow⟩)
      simpa only [show ((n : ℝ)+1)/16=(n : ℝ)/16+1/16 by ring] using hh
    by_cases hhigh : 22768 ≤ n
    · have hh := lower_mesh_standard_ranges n (Or.inr ⟨hhigh,by omega⟩)
      simpa only [show ((n : ℝ)+1)/16=(n : ℝ)/16+1/16 by ring] using hh
    have hL : (22720 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 22720 ≤ n by omega)
    have hU : (n : ℝ) ≤ (22767 : ℝ) := by exact_mod_cast (show n ≤ 22767 by omega)
    exact critical_lower_endpoints _ (by linarith) (by linarith)
  dsimp only
  simpa only [show ((n : ℝ)+1)/16=(n : ℝ)/16+1/16 by ring] using
    both_endpoints_of_lower ((n : ℝ)/16) (by positivity) hu hl

end DusartFiniteMesh


