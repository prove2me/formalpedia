-- Prove2me | Definitions.Def_OffPlatformThreats_Leakage_IsParticipationEq
-- name    : OffPlatformThreats_Leakage_IsParticipationEq
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:34:47.357928+00:00
-- url     : https://prove2.me/theorems/e4c1f439-39e4-42bb-a45a-c57249207ee9
-- title:
--   Provider participation equilibrium (Definition 1, corrected)
-- statement:
--   For a payout ratio $\omega$, a pair $(N_p, N_o)$ of nonnegative integers (the numbers of $j$-type providers on and off the platform) is a **participation equilibrium** if
--
--   1. $N_p + N_o \le N$;
--   2. if $N_p > 0$: $U_p(\omega, N_p) \ge (U_o)^+$;
--   3. if $N_o > 0$: $U_o \ge (U_p(\omega, N_p))^+$ and $U_p(\omega, N_p + 1) < U_o$;
--   4. if $N_p + N_o < N$: $U_p(\omega, N_p + 1) < 0$ and $U_o < 0$,
--
--   where $x^+ = \max(x, 0)$. No provider, whether on the platform, off it, or outside, gains by unilaterally changing his participation decision.
--
--   The paper states Definition 1 for the 4-tuple $(N^h_p, N^l_p, N^h_o, N^l_o)$; its conditions are the conjunction of the per-type conditions above.
--
--   **Formalization Note** *Correction.* The printed first line also requires $U_o < U_p(\omega, N_p - 1)$. That clause is dropped: as printed it excludes the all-on-platform equilibrium $(N, 0)$ at the payout ratio $\omega^* = \hat K / g_2(N, v)$ of Proposition 2, contradicting Propositions 1 and 3 (for $c = \phi = \mu = K = 1$, $v = 10$, $N = 2$, $R_o = 0$ it leaves $(0, 2)$, leakage, as the only equilibrium). Every other inequality is as printed. $U_p(\omega, 0) = -K$.
-- source:
--   He, Savin, Goh, Teo, Off-Platform Threats in On-Demand Services, SSRN 3550646 (2021-03-25 version), Definition 1, (12), p. 13

import Mathlib
import Definitions.Def_OffPlatformThreats_Leakage_Market
import Definitions.Def_OffPlatformThreats_Leakage_Up
import Definitions.Def_OffPlatformThreats_Leakage_Uo

namespace OffPlatformThreats.Leakage

/-- **Provider participation equilibrium (Definition 1), for one type, corrected.**
He, Savin, Goh & Teo, SSRN 3550646 (2021-03-25 version), Definition 1, (12), p. 13: the numbers
`(N^j_p(ω^j), N^j_o(ω^j))` of `j`-type providers on and off the platform form a participation
equilibrium if (i) `N^j_p + N^j_o ≤ N^j`, and (ii)
* `U^j_p(ω^j, N^j_p) ≥ (U^j_o)^+` [and `U^j_o < U^j_p(ω^j, N^j_p − 1)`], if `N^j_p > 0`;
* `U^j_o ≥ (U^j_p(ω^j, N^j_p))^+` and `U^j_p(ω^j, N^j_p + 1) < U^j_o`, if `N^j_o > 0`;
* `U^j_p(ω^j, N^j_p + 1) < 0` and `U^j_o < 0`, if `N^j_p + N^j_o < N^j`,

where `x^+ = max(x, 0)`.

`IsParticipationEq m ω np no` is this condition with `np = N^j_p`, `no = N^j_o`.

**Formalization Note.**
1. *Correction.* The bracketed clause `U^j_o < U^j_p(ω^j, N^j_p(ω^j) − 1)` of the first line is
   dropped. As printed it makes the all-on-platform configuration `(N^j, 0)` fail at the payout
   ratio `ω^{j*} = K̂^j/g2(N^j, v^j)` whenever `U^j_o > U^j_p(ω^{j*}, N^j − 1)`, contradicting
   Proposition 1 (whose proof does not use the clause) and Proposition 3. Exact example:
   `c = φ = µ = K = 1, v = 10, N = 2, Ro = 0`: with the clause the only equilibrium at `ω^*` is
   `(0, 2)`, i.e. leakage, while `Ro = 0` lies below `a ≈ 6.80`. The remaining clause is the
   paper's "no on-platform provider gains by leaving" condition (p. 13, after (12)).
2. Definition 1 is stated for the 4-tuple over both types; its conditions are the conjunction
   of the per-type conditions, which is what is stated here.
3. `U^j_p(ω, 0) = −K^j` (see `Up`). Every other strict and weak inequality is as printed. -/
def IsParticipationEq (m : Market) (ω : ℝ) (np no : ℕ) : Prop :=
  np + no ≤ m.N ∧
  (0 < np → max (Uo m) 0 ≤ Up m ω np) ∧
  (0 < no → max (Up m ω np) 0 ≤ Uo m ∧ Up m ω (np + 1) < Uo m) ∧
  (np + no < m.N → Up m ω (np + 1) < 0 ∧ Uo m < 0)

end OffPlatformThreats.Leakage


