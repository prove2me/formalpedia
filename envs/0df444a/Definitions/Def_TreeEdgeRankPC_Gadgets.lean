-- Prove2me | Definitions.Def_TreeEdgeRankPC_Gadgets
-- name    : TreeEdgeRankPC_Gadgets
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:35:46.949261+00:00
-- url     : https://prove2.me/theorems/daec7503-9bcc-40d7-a55d-3005b8ad2f1a
-- title:
--   Signals, selectors, messages and the instance $\mathcal G(C)$
-- statement:
--   The reduction from AM2CVP to GreedyAllocation uses these multisets of requirements. The **signals** at a clock $e\ge 10$ are
--   $$H_e=\{2^e\},\qquad L_e=\{2^{e-9}+2^{e-10}+1,\ 2^{e-9}+2^{e-10}\},$$
--   representing 1 and 0. For $e\ge 16$ and messages $0\le u_j,v_k<2^{e-14}$, the **selector** is the twelve requirements
--   $$T_1=2^{e-1}+2^{e-14},\quad T_2=2^{e-2}+2^{e-14},\quad U_j=2^{e-j-2}+u_j\ (j\in[6]),\quad V_k=2^{e-k-10}+v_k\ (k\in[4]).$$
--   For $e\ge 13$ the **input messages** are $\mathcal M^L_e(1)=\{2^e\}$, $\mathcal M^L_e(0)=\{2^{e-3}+2^{e-4}\}\cup L_{e-3}$ (a multiset union), $\mathcal M^R_e(1)=\{2^{e-1}+2^{e-3},2^{e-2}\}$, and $\mathcal M^R_e(0)=\{2^{e-1}+2^{e-12}+2^{e-13}+1,\ 2^{e-2}+2^{e-12}+2^{e-13}\}$.
--
--   For an $m$-node instance $C$, set $e_i=18(m-i+1)-1$ and $K=18m$. For each nonoutput node $i<m$, list its outgoing wires by destination, with the left slot before the right. On a wire to node $j$, use $\mathcal M^L_{e_j}$ or $\mathcal M^R_{e_j}$ according to its input slot, appending the bit-0 entries to the $u$-list and the bit-1 entries to the $v$-list, counting parallel wires separately. Pad the lists with zeroes to lengths six and four, and insert the selector at clock $e_i-3$. For each input node $i$, also insert the padding requirements $2^{e_i},2^{e_i-1},2^{e_i-2}$ and the signal $H_{e_i-3}$ if its bit is 1 or $L_{e_i-3}$ if it is 0. For the output node $m$, insert the test requirement $2^{e_m-3}=2^{14}$ instead of a selector. These requirements, with multiplicities, define $\mathcal G(C)=\langle K;q_1,\dots,q_d\rangle$.
--
--   **Formalization Note** The formulas use natural-number subtraction, exact on the stated clock ranges. Node numbers and the families $u,v$ are 0-based. `GC` lists the requirements in node order; the paper's instance is the multiset. Mechanical checks of $\mathcal G(C)$ on small circuits are in the mission's verification file.
-- source:
--   Giliberti–Hajiaghayi–Yun, Parallel Edge Ranking of Trees, arXiv:2610.12438 (held version of 2026-11-02, sha256 9e04ca7b…), §4.2, p.18 (Signals; eq. (4.3); eq. (4.4)); p.20 (eq. (4.5))

import Mathlib
import Definitions.Def_TreeEdgeRankPC_AM2CVP

namespace TreeEdgeRankPC

/-- The signal `H_e = {2^e}`, §4.2, p.18 (arXiv:2610.12438, held version of 2026-11-02, sha256 9e04ca7b…).
It is defined for clocks `e ≥ 10`. -/
def sigH (e : ℕ) : List ℕ := [2 ^ e]

/-- The signal `L_e = {2^{e−9} + 2^{e−10} + 1, 2^{e−9} + 2^{e−10}}`, §4.2, p.18, for clocks `e ≥ 10`. Natural
number subtraction is exact there. -/
def sigL (e : ℕ) : List ℕ := [2 ^ (e - 9) + 2 ^ (e - 10) + 1, 2 ^ (e - 9) + 2 ^ (e - 10)]

/-- The twelve **selector requirements** of eq. (4.3), §4.2, p.18, in the order `T₁, T₂, U₁, …, U₆, V₁, …, V₄`:
`T₁ = 2^{e−1} + 2^{e−14}`, `T₂ = 2^{e−2} + 2^{e−14}`, `U_j = 2^{e−j−2} + u_j` (`j ∈ [6]`),
`V_k = 2^{e−k−10} + v_k` (`k ∈ [4]`), for `e ≥ 16`.

**Formalization Note.** The 0-based `j : Fin 6` stands for the paper's `j + 1`, and `k : Fin 4` for
`k + 1`. Natural-number subtraction is exact for `e ≥ 16`. -/
def selector (e : ℕ) (u : Fin 6 → ℕ) (v : Fin 4 → ℕ) : List ℕ :=
  [2 ^ (e - 1) + 2 ^ (e - 14), 2 ^ (e - 2) + 2 ^ (e - 14)] ++
    (List.finRange 6).map (fun j : Fin 6 => 2 ^ (e - ((j : ℕ) + 1) - 2) + u j) ++
    (List.finRange 4).map (fun k : Fin 4 => 2 ^ (e - ((k : ℕ) + 1) - 10) + v k)

/-- The left input message `𝓜^L_e(b)` of eq. (4.4), §4.2, p.18, for `e ≥ 13`: `{2^e}` on `b = 1`, and the
multiset union `{2^{e−3} + 2^{e−4}} ∪ L_{e−3}` on `b = 0`. -/
def msgL (e : ℕ) (b : Bool) : List ℕ :=
  if b then [2 ^ e] else (2 ^ (e - 3) + 2 ^ (e - 4)) :: sigL (e - 3)

/-- The right input message `𝓜^R_e(b)` of eq. (4.4), §4.2, p.18, for `e ≥ 13`: `{2^{e−1} + 2^{e−3}, 2^{e−2}}`
on `b = 1`, and `{2^{e−1} + 2^{e−12} + 2^{e−13} + 1, 2^{e−2} + 2^{e−12} + 2^{e−13}}` on `b = 0`. -/
def msgR (e : ℕ) (b : Bool) : List ℕ :=
  if b then [2 ^ (e - 1) + 2 ^ (e - 3), 2 ^ (e - 2)]
  else [2 ^ (e - 1) + 2 ^ (e - 12) + 2 ^ (e - 13) + 1, 2 ^ (e - 2) + 2 ^ (e - 12) + 2 ^ (e - 13)]

/-- The positive entries of a family, as a multiset (the residuals left by a selector, Lemma 4.9, p.18). -/
def positives {n : ℕ} (u : Fin n → ℕ) : Multiset ℕ :=
  ((List.finRange n).map u : Multiset ℕ).filter (0 < ·)

namespace AM2Instance

variable (C : AM2Instance)

/-- The clock `e_i = 18(m − i + 1) − 1` of eq. (4.5), p.20. Node numbers here start from `0`, so the
paper's `i` is `i + 1` and the formula reads `18(m − i) − 1`. -/
def clock (i : ℕ) : ℕ := 18 * (C.nodes.length - i) - 1

/-- The outgoing wires of node `i`, as (destination, is the left slot): "list its outgoing wires by
destination, with the left slot before the right", counting parallel wires separately (p.20). -/
def outWires (i : ℕ) : List (ℕ × Bool) :=
  (List.range C.nodes.length).flatMap fun j =>
    match C.nodes[j]? with
    | some (AM2Node.andGate l r) | some (AM2Node.orGate l r) =>
        (if l = i then [(j, true)] else []) ++ (if r = i then [(j, false)] else [])
    | _ => []

/-- The message of a wire to node `j` for the bit `b`: `𝓜^L_{e_j}(b)` or `𝓜^R_{e_j}(b)` by input slot. -/
def wireMsg (w : ℕ × Bool) (b : Bool) : List ℕ :=
  if w.2 then msgL (C.clock w.1) b else msgR (C.clock w.1) b

/-- The `u`-list of node `i`: the bit-0 entries of the messages on its outgoing wires (p.20). -/
def uList (i : ℕ) : List ℕ := (C.outWires i).flatMap fun w => C.wireMsg w false

/-- The `v`-list of node `i`: the bit-1 entries of the messages on its outgoing wires (p.20). -/
def vList (i : ℕ) : List ℕ := (C.outWires i).flatMap fun w => C.wireMsg w true

/-- The requirements inserted for node `i` (p.20). For an input node: "the three padding requirements
`2^{e_i}, 2^{e_i−1}, 2^{e_i−2}` and the signal `H_{e_i−3}` if its assigned bit is 1, or `L_{e_i−3}` if it is 0".
For a non-output node: the selector requirements (4.3) at clock `e_i − 3`, with the lists "pad[ded] with
zeroes to lengths six and four". For the output node: "the test requirement `2^{e_m−3} = 2^{14}` instead of a
selector". -/
def nodeRequirements (i : ℕ) : List ℕ :=
  (match C.nodes[i]? with
    | some (AM2Node.input b) =>
        [2 ^ C.clock i, 2 ^ (C.clock i - 1), 2 ^ (C.clock i - 2)] ++
          (if b then sigH (C.clock i - 3) else sigL (C.clock i - 3))
    | _ => []) ++
  (if i + 1 < C.nodes.length then
      selector (C.clock i - 3) (fun j => (C.uList i).getD (j : ℕ) 0) (fun k => (C.vList i).getD (k : ℕ) 0)
    else [2 ^ (C.clock i - 3)])

/-- The requirements of **`G(C)`**, eq. (4.5), §4.2, p.20: "These requirements, with multiplicities, define
G(C) = ⟨K; q1, ..., qd⟩." With `K = 18m` (eq. (4.5)) this is the instance `⟨18m; GC⟩`.

**Formalization Note.** The paper fixes the multiset. This list is in node order, and in each node in the
order of `nodeRequirements`. -/
def GC : List ℕ := (List.range C.nodes.length).flatMap C.nodeRequirements

end AM2Instance

end TreeEdgeRankPC


