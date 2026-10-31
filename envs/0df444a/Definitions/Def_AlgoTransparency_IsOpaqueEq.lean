-- Prove2me | Definitions.Def_AlgoTransparency_IsOpaqueEq
-- name    : AlgoTransparency_IsOpaqueEq
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:52:13.757015+00:00
-- url     : https://prove2.me/theorems/f76d0531-f63c-495d-8dc4-8cb7a57c7b1f
-- title:
--   Nash equilibrium of the opaque game
-- statement:
--   A triple $(q_H,q_L,P)$ — H agents improve education with probability $q_H$, L agents with probability $q_L$, the firm hires state $S$ with probability $P_S$ — is an **opaque Nash equilibrium** at costs $(C_H,C_L)$ when:
--
--   1. $q_H,q_L\in[0,1]$ and every $P_S\in[0,1]$;
--   2. each type best-responds under (5)–(6): if it improves with positive probability, improving is at least as good as not improving; if it does not improve surely, not improving is at least as good;
--   3. at every occupied state $S$ ($n^H_S+n^L_S>0$) the firm best-responds: $P_S=1$ if $m_S>0$ and $P_S=0$ if $m_S<0$;
--   4. **off-path convention:** an unoccupied educated state ($B$, $D$) is hired with probability 1, an unoccupied uneducated state ($A$, $C$) with probability 0.
--
--   **Formalization Note** The payoff (4) is linear and separable in $P$, so clause 3 is exactly optimality of $P$ at the occupied states. Firm optimality is stated through the margins $m_S$, not through the ratios $\gamma^E_S$ of (12). Clause 4 is a reading: every equilibrium written in App. A.1 uses it, and under plain Nash, where any $P_S$ is optimal at an unoccupied state, the paper's payoff-dominance selection has no solution in region N2.
-- source:
--   Wang, Huang, Jasin & Singh, Algorithmic Transparency with Strategic Users, arXiv:2008.09283v1, §4–§4.1, pp.16–19 (PDF 17–20); App. A.1, pp.39–45 (PDF 40–46)

import Mathlib
import Definitions.Def_AlgoTransparency_marginO
import Definitions.Def_AlgoTransparency_uHImpO
import Definitions.Def_AlgoTransparency_uHNotO
import Definitions.Def_AlgoTransparency_uLImpO
import Definitions.Def_AlgoTransparency_uLNotO

namespace AlgoTransparency

/-- **Nash equilibrium of the opaque game**, Wang, Huang, Jasin & Singh, arXiv:2008.09283v1,
§4 and §4.1, pp.16–19 (PDF 17–20), and App. A.1, pp.39–45 (PDF 40–46).

`IsOpaqueEq p CH CL qH qL P` says that type-H agents improving education with probability `qH`,
type-L agents with probability `qL`, and the firm hiring state `S` with probability `P S` form
a Nash equilibrium:

1. `qH, qL ∈ [0, 1]` and every `P S ∈ [0, 1]`;
2. each type best-responds: if it improves with positive probability then improving is at
   least as good as not improving (utilities (5)–(6), p.14), and if it does not improve with
   probability 1 then not improving is at least as good;
3. the firm best-responds at every occupied state `S` (`n^H_S + n^L_S > 0`): it hires surely when
   its margin `m_S` is positive and never when it is negative (eqs. (4), (12));
4. **off-path convention**: an unoccupied educated state (`B`, `D`) is hired with probability 1
   and an unoccupied uneducated state (`A`, `C`) with probability 0.

**Formalization Note.** Since the payoff (4) is linear and separable in `P`, clause 3 is exactly
"`P` maximizes `Π_O` over `[0,1]^4` at the occupied states". Firm optimality is stated through the
signed margins, not through the ratios `γ^E_S = n^H_S/n_S` of (12), which are `0/0` at an
unoccupied state. The off-path convention (clause 4) is a reading: every equilibrium written in
App. A.1 (cases 1–5) uses it, and under plain Nash, where any `P S` is a best response at an
unoccupied state, the paper's payoff-dominance selection (p.19) has no solution in region N2. -/
def IsOpaqueEq (p : Params) (CH CL qH qL : ℝ) (P : OState → ℝ) : Prop :=
  (0 ≤ qH ∧ qH ≤ 1) ∧ (0 ≤ qL ∧ qL ≤ 1) ∧
  (∀ S, 0 ≤ P S ∧ P S ≤ 1) ∧
  (0 < qH → uHNotO p P ≤ uHImpO p CH P) ∧ (qH < 1 → uHImpO p CH P ≤ uHNotO p P) ∧
  (0 < qL → uLNotO p P ≤ uLImpO p CL P) ∧ (qL < 1 → uLImpO p CL P ≤ uLNotO p P) ∧
  (∀ S, 0 < massHO p qH S + massLO p qL S →
    (0 < marginO p qH qL S → P S = 1) ∧ (marginO p qH qL S < 0 → P S = 0)) ∧
  (massHO p qH .A + massLO p qL .A = 0 → P .A = 0) ∧
  (massHO p qH .B + massLO p qL .B = 0 → P .B = 1) ∧
  (massHO p qH .C + massLO p qL .C = 0 → P .C = 0) ∧
  (massHO p qH .D + massLO p qL .D = 0 → P .D = 1)

end AlgoTransparency


