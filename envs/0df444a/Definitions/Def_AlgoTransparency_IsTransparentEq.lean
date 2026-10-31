-- Prove2me | Definitions.Def_AlgoTransparency_IsTransparentEq
-- name    : AlgoTransparency_IsTransparentEq
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:51:33.664536+00:00
-- url     : https://prove2.me/theorems/5317480f-dbff-4b87-9fca-7c539f5ea2d3
-- title:
--   Nash equilibrium of the transparent game
-- statement:
--   A triple $(q_H,q_L,P)$ with $P=(P_E,P_F)$ is a **transparent Nash equilibrium** at costs $(C_H,C_L)$ when:
--
--   1. $q_H,q_L\in[0,1]$ and $P_E,P_F\in[0,1]$;
--   2. each type best-responds under (7)–(8), with cost $C_H$ for type H and $C_L$ for type L;
--   3. at every occupied state the firm best-responds: $P_S=1$ if $m_S>0$ and $P_S=0$ if $m_S<0$;
--   4. **off-path convention:** an unoccupied $F$ is hired with probability 1, an unoccupied $E$ with probability 0.
--
--   **Formalization Note** The same conventions as the opaque equilibrium; every equilibrium written in App. A.2 uses this off-path rule (transparent case 1 has $P_F=1$ with nobody in $F$).
-- source:
--   Wang, Huang, Jasin & Singh, Algorithmic Transparency with Strategic Users, arXiv:2008.09283v1, §4.2, pp.19–20 (PDF 20–21); App. A.2, pp.46–50 (PDF 47–51)

import Mathlib
import Definitions.Def_AlgoTransparency_marginT
import Definitions.Def_AlgoTransparency_uImpT
import Definitions.Def_AlgoTransparency_uNotT

namespace AlgoTransparency

/-- **Nash equilibrium of the transparent game**, Wang, Huang, Jasin & Singh,
arXiv:2008.09283v1, §4.2, pp.19–20 (PDF 20–21), and App. A.2, pp.46–50 (PDF 47–51).

`IsTransparentEq p CH CL qH qL P` says that type-H agents improving education with probability
`qH`, type-L agents with probability `qL`, and the firm hiring state `S ∈ {E, F}` with
probability `P S` form a Nash equilibrium:

1. `qH, qL ∈ [0, 1]` and `P E, P F ∈ [0, 1]`;
2. each type best-responds under utilities (7)–(8) (p.14), with cost `CH` for type H and `CL`
   for type L;
3. the firm best-responds at every occupied state: it hires surely when its margin is positive
   and never when it is negative (eq. (4));
4. **off-path convention**: an unoccupied `F` is hired with probability 1, an unoccupied `E`
   with probability 0.

**Formalization Note.** The same conventions as `IsOpaqueEq`: margins instead of `γ^E_S`, and
the off-path rule that every equilibrium of App. A.2 uses (transparent case 1: `P_F = 1` with
nobody in `F`; cases 2, 3: `P_E = 0`). -/
def IsTransparentEq (p : Params) (CH CL qH qL : ℝ) (P : TState → ℝ) : Prop :=
  (0 ≤ qH ∧ qH ≤ 1) ∧ (0 ≤ qL ∧ qL ≤ 1) ∧
  (∀ S, 0 ≤ P S ∧ P S ≤ 1) ∧
  (0 < qH → uNotT p P ≤ uImpT p CH P) ∧ (qH < 1 → uImpT p CH P ≤ uNotT p P) ∧
  (0 < qL → uNotT p P ≤ uImpT p CL P) ∧ (qL < 1 → uImpT p CL P ≤ uNotT p P) ∧
  (∀ S, 0 < massHT p qH S + massLT p qL S →
    (0 < marginT p qH qL S → P S = 1) ∧ (marginT p qH qL S < 0 → P S = 0)) ∧
  (massHT p qH .E + massLT p qL .E = 0 → P .E = 0) ∧
  (massHT p qH .F + massLT p qL .F = 0 → P .F = 1)

end AlgoTransparency


