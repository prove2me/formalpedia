-- Prove2me | Definitions.Def_QPVEntanglement_Schedule_stretch
-- name    : QPVEntanglement_Schedule_stretch
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:30:24.410053+00:00
-- url     : https://prove2.me/theorems/83472467-e479-4f6d-9533-233271255bef
-- title:
--   The stretched schedule of Proposition 1 (eq. (100))
-- statement:
--   For a schedule with spacing $\Delta$ and a new spacing $\Delta^\star>0$, put $G=\Delta^\star-\Delta$. The **stretched schedule** delays slot $j$ of round $k$ by $k(s-1)G+jG$ (eq. (100): $g_{r,j}=(r-1)\delta_s+\delta_j$, $\delta_j=(j-1)G$, $1$-based in the paper), i.e. its round base times are $\tau_k+k(s-1)G$ and its spacing is $\Delta^\star$; the initial states are sent as before and the replenishment after round $k$ is delayed by $(k+1)(s-1)G$ ("delay $r\delta_s$ to actions between rounds $r$ and $r+1$"). It again satisfies (S1)–(S3).
--
--   It is the execution with the same locations and protocol actions and slot spacing $\Delta^\star$ in Proposition 1.
-- source:
--   Behera, Goyal, Breaking the Bounded Entanglement Barrier for Quantum Position Verification, arXiv:2609.39234 (sha256 bdf2928d…), proof of Proposition 1, eq. (100) and the paragraph after it, p.72

import Mathlib
import Definitions.Def_QPVEntanglement_Schedule

set_option autoImplicit false

namespace QPVEntanglement

namespace Schedule

variable {G : Geometry} {m RH s : ℕ}

/-- **The stretched schedule** of Proposition 1 (proof, App. C.1, eq. (100) and the paragraph
after it, p.72). Behera–Goyal, arXiv:2609.39234 (sha256 bdf2928d…), eq. (100), p.72.

With `G' := Δ⋆ − Δ`, slot `j` of round `k` (0-based) is delayed by `k(s−1)G' + jG'`
(`g_{r,j} = (r−1)δ_s + δ_j`, `δ_j = (j−1)G`, 1-based in the paper), i.e. the round base times
become `τ k + k(s−1)G'` and the spacing becomes `Δ⋆`; the initial states are sent as before and
the replenishment after round `k` is delayed by `(k+1)(s−1)G'` ("delay `rδ_s` to actions between
rounds `r` and `r+1`"). The stretched schedule again satisfies (S1)–(S3). -/
noncomputable def stretch (S : Schedule G m RH s) (Δstar : ℝ) (hΔ : 0 < Δstar) :
    Schedule G m RH s where
  Δ := Δstar
  Δ_pos := hΔ
  τ := fun k => S.τ k + (k : ℝ) * ((s : ℝ) - 1) * (Δstar - S.Δ)
  σ0 := S.σ0
  σ0_mono := S.σ0_mono
  σr := fun k => S.σr k + ((k : ℝ) + 1) * ((s : ℝ) - 1) * (Δstar - S.Δ)
  S1 := by
    intro h k hk
    have := S.S1 h k hk
    simp only [hk, Nat.cast_zero, zero_mul, add_zero]
    exact this
  S2 := by
    intro k
    have := S.S2 k
    simp only
    nlinarith
  S3 := by
    intro k
    have := S.S3 k
    simp only [Nat.cast_add, Nat.cast_one]
    nlinarith

end Schedule

end QPVEntanglement


