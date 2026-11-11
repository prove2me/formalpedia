-- Prove2me | Definitions.Def_AcceptSubcube_WCNF
-- name    : AcceptSubcube_WCNF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T22:00:41.784465+00:00
-- url     : https://prove2.me/theorems/ff6c6d45-d317-4597-926e-67f3693d03e6
-- title:
--   Weighted unary/binary CNFs, fractional cost, pinning, and the objective (15)
-- statement:
--   A **weighted CNF** is a list of clauses, each a weight and a list of literals; the literal $(i,b)$ is true when $x_i=b$. Its cost $C_\Phi(z)$ is the total weight of violated clauses. Under the local laws of a point, the **fractional cost** is $V=\sum_c w_c\,\mathbb P[c\text{ violated}]$; a clause $a\vee b$ has fractional violation $\mathbb P[a=0,b=0]$ and a unit clause $a$ is treated as $a\vee a$.
--
--   **Pinning** (proof of Lemma 4.5): delete clauses containing a literal pinned true and remove literals pinned false; $F_0$ is the weight of clauses all of whose literals are pinned false, and the **residual formula** consists of the remaining nonempty clauses.
--
--   **Vector input of Lemma 4.6**: unit vectors $v_0,\dots,v_q$ given by their Gram matrix (positive semidefinite, unit diagonal) satisfying all squared-Euclidean triangle inequalities on $\{\pm v_0,\dots,\pm v_q\}$. With the literal $x_i\mapsto v_i$, $\neg x_i\mapsto -v_i$, the implication $u\to w$ has value
--   $$\frac{\|v_u-v_w\|^2-\|v_0-v_u\|^2+\|v_0-v_w\|^2}{8}\qquad(15)$$
--   and $a\vee b$ is $\bar a\to b$ and $\bar b\to a$ with half the weight each.
--
--   **Formalization Note** The Gram matrix is rational (the only use passes a principal submatrix of the rational moment matrix, p.21); every positive semidefinite matrix with unit diagonal is the Gram matrix of real unit vectors.
-- source:
--   Cai, Jiang, Liu, Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs, STOC 2027 submission (manuscript sha256 66626baf…), §4.4, p.17 (literals, fractional cost); §4.5, p.19 (a ∨ a; pinning in the proof of Lemma 4.5); §4.6, p.20 ((15), Lemma 4.6)

import Mathlib
import Definitions.Def_AcceptSubcube_RelaxFeasible

namespace AcceptSubcube

/-- **Weighted CNF**: a list of clauses, each a weight and a list of literals `(i, b)`, the literal
`(i, b)` being true iff `x_i = b`.

Cai, Jiang, Liu, *Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs*,
STOC 2027 submission (manuscript sha256 66626baf…), §4.4, p.17: "A literal is identified with the
event that it is true"; §4.5, p.19: "a unit clause a is treated as a ∨ a". -/
abbrev WCNF : Type := List (ℚ × List (ℕ × Bool))

/-- A clause is violated by `x` when all its literals are false. -/
def clauseViol (x : ℕ → Bool) (c : ℚ × List (ℕ × Bool)) : Bool :=
  c.2.all (fun l => x l.1 != l.2)

/-- **Cost** `C_Φ(z)`: total weight of the clauses violated by `z`. -/
def cnfCost (Φ : WCNF) (x : ℕ → Bool) : ℚ :=
  (Φ.map (fun c => if clauseViol x c then c.1 else 0)).sum

/-- `P[c violated]` under the local laws: the probability that every literal of `c` is false
(`0` if `c` contains a variable with both signs, a tautology). -/
def clauseViolProb (L : List (List ℕ × ℚ)) (c : ℚ × List (ℕ × Bool)) : ℚ :=
  if c.2.all (fun l => c.2.all (fun l' => l.1 != l'.1 || l.2 == l'.2)) then
    atom L (c.2.map Prod.fst).toFinset ((c.2.filter (fun l => !l.2)).map Prod.fst).toFinset
  else 0

/-- **Fractional cost** `V = Σ_c w_c P[c violated]` (§4.4, p.17; §4.5, p.19: "a clause a ∨ b has
fractional violation ε = P[a = 0, b = 0]"). -/
def fracCost (L : List (List ℕ × ℚ)) (Φ : WCNF) : ℚ :=
  (Φ.map (fun c => c.1 * clauseViolProb L c)).sum

/-- Unary/binary: every clause has one or two literals. -/
def IsUnaryBinary (Φ : WCNF) : Prop := ∀ c ∈ Φ, c.2.length = 1 ∨ c.2.length = 2

/-- Nonnegative integer weights. -/
def NatWeights (Φ : WCNF) : Prop := ∀ c ∈ Φ, ∃ m : ℕ, c.1 = m

/-- Nonnegative weights. -/
def NonnegWeights (Φ : WCNF) : Prop := ∀ c ∈ Φ, 0 ≤ c.1

/-- Every variable of `Φ` lies in `V`. -/
def OnVars (Φ : WCNF) (V : Finset ℕ) : Prop := ∀ c ∈ Φ, ∀ l ∈ c.2, l.1 ∈ V

/-- The value a list of pins gives a variable (first pin of that variable). -/
def pinVal (pins : List (ℕ × Bool)) (i : ℕ) : Option Bool :=
  (pins.find? (fun p => p.1 == i)).map Prod.snd

/-- The clauses kept after pinning: "Delete clauses containing a literal pinned true, and remove
literals pinned false from the remaining clauses" (Proof of Lemma 4.5, p.19). -/
def pinReduce (pins : List (ℕ × Bool)) (Φ : WCNF) : WCNF :=
  (Φ.filter (fun c => !(c.2.any (fun l => pinVal pins l.1 == some l.2)))).map
    (fun c => (c.1, c.2.filter (fun l => !(pinVal pins l.1 == some (!l.2)))))

/-- `F₀`: the weight of the clauses made permanently false (all literals pinned false). -/
def pinF0 (pins : List (ℕ × Bool)) (Φ : WCNF) : ℚ :=
  (((pinReduce pins Φ).filter (fun c => c.2.isEmpty)).map Prod.fst).sum

/-- The residual formula: the reduced clauses that still have a literal. -/
def pinResidual (pins : List (ℕ × Bool)) (Φ : WCNF) : WCNF :=
  (pinReduce pins Φ).filter (fun c => !c.2.isEmpty)

/-- The Gram matrix given by its rows, indices `0, …, q` (`0` is `v₀`, `i + 1` is variable `i`). -/
def gramOf (q : ℕ) (G : List (List ℚ)) : Matrix (Fin (q + 1)) (Fin (q + 1)) ℚ :=
  fun a b => (G.getD a []).getD b 0

/-- `‖s_a v_a − s_b v_b‖² = G_aa + G_bb − 2 s_a s_b G_ab` for signs `s = ±1` (`true` is `+`). -/
def sqd {q : ℕ} (G : Matrix (Fin (q + 1)) (Fin (q + 1)) ℚ) (a : Fin (q + 1) × Bool)
    (b : Fin (q + 1) × Bool) : ℚ :=
  G a.1 a.1 + G b.1 b.1 - 2 * (if a.2 == b.2 then 1 else -1) * G a.1 b.1

/-- **The input condition of Lemma 4.6**: `G` is the Gram matrix of unit vectors `v₀, …, v_q`
(positive semidefinite with unit diagonal) satisfying the squared-Euclidean triangle inequalities on
`{±v₀, …, ±v_q}`.

Cai, Jiang, Liu, STOC 2027 submission (manuscript sha256 66626baf…), Lemma 4.6, p.20.

**Formalization Note.** The unit vectors are given through their rational Gram matrix (the only use,
§4.8, p.21, passes a principal submatrix of the rational moment matrix `Z`); every positive
semidefinite matrix with unit diagonal is the Gram matrix of real unit vectors. -/
def GramFeasible (q : ℕ) (G : List (List ℚ)) : Prop :=
  ((gramOf q G).map (fun x : ℚ => (x : ℝ))).PosSemidef ∧ (∀ a, gramOf q G a a = 1) ∧
    ∀ a b c : Fin (q + 1) × Bool, sqd (gramOf q G) a c ≤ sqd (gramOf q G) a b + sqd (gramOf q G) b c

/-- The signed vector of a literal: `x_i ↦ v_{i+1}`, `¬x_i ↦ −v_{i+1}` (p.20). Only variables
`i < q` occur (formula on `q` variables), for which the index is `i + 1`. -/
def litVec (q : ℕ) (l : ℕ × Bool) : Fin (q + 1) × Bool :=
  (⟨(l.1 + 1) % (q + 1), Nat.mod_lt _ (Nat.succ_pos q)⟩, l.2)

/-- (15), p.20: `P[u = 1, w = 0] = (‖v_u − v_w‖² − ‖v₀ − v_u‖² + ‖v₀ − v_w‖²)/8` for the
implication `u → w`. -/
def implCost (q : ℕ) (G : Matrix (Fin (q + 1)) (Fin (q + 1)) ℚ) (u w : ℕ × Bool) : ℚ :=
  (sqd G (litVec q u) (litVec q w) - sqd G (0, true) (litVec q u) +
    sqd G (0, true) (litVec q w)) / 8

/-- **The objective of (15)** at the vectors with Gram matrix `G`: "Writing a ∨ b as the implications
ā → b and b̄ → a with half the weight each" (p.20); a unit clause `a` is `a ∨ a` (p.19). Clauses
with more than two literals do not occur (unary/binary formulas). -/
def objW (q : ℕ) (G : List (List ℚ)) (Φ : WCNF) : ℚ :=
  (Φ.map (fun c =>
    match c.2 with
    | [a] => c.1 / 2 * (implCost q (gramOf q G) (a.1, !a.2) a +
        implCost q (gramOf q G) (a.1, !a.2) a)
    | [a, b] => c.1 / 2 * (implCost q (gramOf q G) (a.1, !a.2) b +
        implCost q (gramOf q G) (b.1, !b.2) a)
    | _ => 0)).sum

end AcceptSubcube


