-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankGoodPrimesEdges
-- name    : IntMul_Kappa_R8_Data_BitOppbankGoodPrimesEdges
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T17:06:20.449449+00:00
-- url     : https://prove2.me/theorems/1d643808-0620-4af1-8e31-96d56945737b
-- title:
--   R8 Oppbank EdgesOK_large for net0P (good_primes EdgeOK half)
-- statement:
--   For the densified opp-bank network $\mathrm{net0P}$, there exists $q_0$ such that for every prime $q>q_0$ and every $f$, $\mathrm{EdgesOK}(\mathrm{net0P},q^f)$. Proof: every program edge lies in the finite family $E_0$ (GoodPrimes), each member admits $\mathrm{EdgeQ}$, and R6 $\mathrm{good\_edges}$ lifts this to $\mathrm{EdgeOK}$ at large prime powers. Together with proved $\mathrm{RunsOK}(\mathrm{net0P})$ this is the RunsOK∧EdgesOK half of $\mathrm{net0\_ok}$; FormalOK remains.
-- source:
--   GoodPrimes E0/E0_Q/runsOK0; R6 good_edges 3935173d.

-- EdgesOK half of densified good_primes / net0_ok on net0P.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankGoodPrimes
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNet0P
import Theorems.Thm_IntMul_Kappa_R6_Bit_NB_good_edges
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# EdgesOK for `net0P` via GoodPrimes `E0` + R6 `good_edges`

Discharges the EdgesOK conjunct of `net0_ok` / `good_primes` EdgeOK half.
FormalOK remains open (needs `FB0_ex` / `EOK`).
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.GoodPrimesEdges

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.NB
open IntMul.Kappa.R6.Bit.QHNet (RunsOK EdgesOK FormalOK)
open IntMul.Kappa.R8.Bit.Oppbank.GoodPrimes
open IntMul.Kappa.R8.Bit.Oppbank.Net0P

theorem edges_good :
    ∃ q₀ : ℕ, ∀ q, q.Prime → q₀ < q → ∀ f : ℕ, ∀ e ∈ E0, EdgeOK (q ^ f) e :=
  good_edges E0 E0_Q

theorem EdgesOK_large :
    ∃ q₀ : ℕ, ∀ q, q.Prime → q₀ < q → ∀ f, EdgesOK (m := 529) net0P (q ^ f) := by
  obtain ⟨q₀, h⟩ := edges_good
  refine ⟨q₀, fun q hq hlt f e he => h q hq hlt f e (edges_E0 e he)⟩

theorem net0_runs_edges :
    ∃ q₀ : ℕ,
      RunsOK (m := 529) net0P ∧
        (∀ q, q.Prime → q₀ < q → ∀ f, EdgesOK (m := 529) net0P (q ^ f)) := by
  obtain ⟨q₀, hE⟩ := EdgesOK_large
  exact ⟨q₀, net0P_RunsOK, hE⟩

end IntMul.Kappa.R8.Bit.Oppbank.GoodPrimesEdges


