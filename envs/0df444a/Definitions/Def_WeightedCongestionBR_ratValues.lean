-- Prove2me | Definitions.Def_WeightedCongestionBR_ratValues
-- name    : WeightedCongestionBR_ratValues
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:17:30.505804+00:00
-- url     : https://prove2.me/theorems/6dea3cb4-7afe-405e-9c5f-202c7d012519
-- title:
--   The rational numbers Algorithm 1 handles
-- statement:
--   On a rational instance, the finite set $V$ of rational numbers that the pseudocode of Algorithm 1 computes or compares:
--
--   1. $p$, $\alpha+1/p$, the intermediate values of Line 2 ($p^3$, $np^3$, $1+m(1+p)$ and its powers, $d^\nu$), $g$, $g^i$ and $b_i$ for $i\le m$, $c_{\max}$, $c_{\min}$ and $c_{\max}/c_{\min}$;
--   2. for every state, resource and $k\le n$, the partial sums of the load;
--   3. for every load or weight $x$, resource $e$ and $\nu\le d$, the powers $x^\nu$, the terms $a_{e,\nu}x^\nu$ and the partial sums of $c_e(x)$;
--   4. for every state and player, the partial sums of $\sum_{e\in s_u}c_e(x_e(s))$, the cost $C_u(s)$, and the products $(\alpha+1/p)C_u(s)$ and $pC_u(s)$ compared in the guards;
--   5. for every player $u$ and strategy $t$, the partial sums of $\sum_{e\in t}c_e(w_u)$ and their products with $w_u$ (the costs in the empty state).
--
--   Deviation states are states, so they are included.
--
--   **Formalization Note** The game is the published `HarksKlimm.Consistency.Game n r`: players `Fin n`, resources `Fin r` with $n, r \ge 1$, nonempty finite strategy sets $S_u \subseteq 2^E$, weights $w_u > 0$ (the field `demand`) and cost functions of the load. Partial sums follow the order of the indices. This set and the next definitions are the mission's cost model for Theorem 4 (Reading 1).
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, Algorithm 1, p.14, and Theorem 4, p.18

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_Game
import Definitions.Def_WeightedCongestionBR_RatData
set_option autoImplicit false
open scoped NNReal
open HarksKlimm.Consistency

namespace WeightedCongestionBR

open Classical in
/-- The finite set `V` of rational numbers that Algorithm 1 handles on a rational instance
(Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, Algorithm 1, p.14; cost model of Theorem 4, p.18):

1. the constants `p`, `α + 1/p`, the intermediate values `p³`, `n p³`, `1 + m(1 + p)` and its powers,
   `d^ν` (`ν ≤ d`), `g`, its powers `g^i` and the boundaries `b_i = c_max/g^i` (`i ≤ m`), `c_max`,
   `c_min` and `c_max/c_min`;
2. for every state `s`, resource `e` and `k ≤ n`, the partial sums of the load
   `∑_{u < k, e ∈ s_u} w_u`;
3. for every load value `x` (a load `x_e(s)` or a weight `w_u`), resource `e` and `ν ≤ d`: `x^ν`,
   `a_{e,ν} x^ν` and the partial sums `∑_{ν' ≤ ν} a_{e,ν'} x^{ν'}` of `c_e(x)`;
4. for every state `s`, player `u` and `k ≤ |E|`, the partial sums `∑_{e ∈ s_u, e < k} c_e(x_e(s))`,
   the cost `C_u(s)`, and the products `(α + 1/p) C_u(s)` and `p C_u(s)` of the guards;
5. for every player `u`, strategy `t ∈ S_u` and `k ≤ |E|`, the partial sums
   `∑_{e ∈ t, e < k} c_e(w_u)` and their products with `w_u` (the costs in the empty state).

Every deviation state `(s_{-u}, s'_u)` is itself a state, so it is covered by "every state".

**Formalization Note** Partial sums follow the order of `Fin`. The set is finite because the game
has finitely many states. This is Reading 1 of the mission: the size of the numbers is measured on
the values of the pseudocode itself. -/
def ratValues {n r d : ℕ} (G : Game n r) (D : RatData n r d) (m : ℕ) (sinit : G.Profile) :
    Set ℚ :=
  let p : ℚ := (2 * d + 3) * (d + 1) * (4 * d) ^ (d + 1)
  let α : ℚ := d + 1
  let g : ℚ := n * p ^ 3 * (1 + m * (1 + p)) ^ d * (d : ℚ) ^ d + 1
  let ld : G.Profile → Fin r → ℚ := fun s e => ∑ u, if e ∈ (s u).val then D.w u else 0
  let ldPart : G.Profile → Fin r → ℕ → ℚ := fun s e k =>
    ∑ u ∈ Finset.univ.filter (fun u : Fin n => u.val < k), if e ∈ (s u).val then D.w u else 0
  let ce : Fin r → ℚ → ℚ := fun e x => ∑ ν : Fin (d + 1), D.a e ν * x ^ (ν : ℕ)
  let cePart : Fin r → ℚ → ℕ → ℚ := fun e x k =>
    ∑ ν ∈ Finset.univ.filter (fun ν : Fin (d + 1) => ν.val ≤ k), D.a e ν * x ^ (ν : ℕ)
  let cPart : G.Profile → Fin n → ℕ → ℚ := fun s u k =>
    ∑ e ∈ (s u).val.filter (fun e : Fin r => e.val < k), ce e (ld s e)
  let C : G.Profile → Fin n → ℚ := fun s u => D.w u * cPart s u r
  let ePart : Fin n → Finset (Fin r) → ℕ → ℚ := fun u t k =>
    ∑ e ∈ t.filter (fun e : Fin r => e.val < k), ce e (D.w u)
  let cmaxQ : ℚ := Finset.univ.sup' ⟨⟨0, G.players_pos⟩, Finset.mem_univ _⟩ (fun u => C sinit u)
  let cminQ : ℚ := Finset.univ.inf' ⟨⟨0, G.players_pos⟩, Finset.mem_univ _⟩ (fun u =>
    (G.strategies u).inf' (G.strategies_nonempty u) (fun t => D.w u * ePart u t r))
  {q | q = p ∨ q = α + 1 / p ∨ q = p ^ 3 ∨ q = n * p ^ 3 ∨ q = 1 + m * (1 + p) ∨ q = g ∨
      q = cmaxQ ∨ q = cminQ ∨ q = cmaxQ / cminQ ∨
      (∃ ν ≤ d, q = (1 + m * (1 + p)) ^ ν ∨ q = (d : ℚ) ^ ν) ∨
      (∃ i ≤ m, q = g ^ i ∨ q = cmaxQ / g ^ i) ∨
      (∃ (s : G.Profile) (e : Fin r) (k : ℕ), k ≤ n ∧ q = ldPart s e k) ∨
      (∃ (x : ℚ) (e : Fin r) (ν : Fin (d + 1)),
        ((∃ (s : G.Profile) (e' : Fin r), x = ld s e') ∨ ∃ u, x = D.w u) ∧
        (q = x ^ (ν : ℕ) ∨ q = D.a e ν * x ^ (ν : ℕ) ∨ q = cePart e x ν)) ∨
      (∃ (s : G.Profile) (u : Fin n),
        q = C s u ∨ q = (α + 1 / p) * C s u ∨ q = p * C s u ∨
        ∃ k ≤ r, q = cPart s u k) ∨
      (∃ (u : Fin n) (t : Finset (Fin r)), t ∈ G.strategies u ∧
        ∃ k ≤ r, q = ePart u t k ∨ q = D.w u * ePart u t k)}

end WeightedCongestionBR


