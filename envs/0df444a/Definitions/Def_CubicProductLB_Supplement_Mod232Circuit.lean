-- Prove2me | Definitions.Def_CubicProductLB_Supplement_Mod232Circuit
-- name    : CubicProductLB_Supplement_Mod232Circuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:39:24.62114+00:00
-- url     : https://prove2.me/theorems/480d3e2d-6e68-49f7-8639-950884611952
-- title:
--   $\mathrm{MOD}_2\circ\mathrm{MOD}_3\circ\mathrm{MOD}_2[k]$ circuits and their measures
-- statement:
--   A **$\mathrm{MOD}_2\circ\mathrm{MOD}_3\circ\mathrm{MOD}_2[k]$ circuit** on $n$ Boolean inputs $x \in \{0,1\}^n$ has three layers:
--
--   1. $B$ bottom $\mathrm{MOD}_2$ gates; each reads a set of at most $k$ inputs and outputs their XOR, possibly negated.
--   2. $M$ middle $\mathrm{MOD}_3$ gates; gate $j$ reads a set of $t_j$ bottom gates and outputs $1$ exactly when the number of its inputs equal to $1$, reduced mod $3$, lies in its accepting set $A_j \subseteq \mathbb Z/3$.
--   3. One top $\mathrm{MOD}_2$ gate: the XOR of all middle outputs, possibly negated.
--
--   The circuit **computes** $[q \mid |x|]$ if its output equals $1$ exactly when $q$ divides the number of ones of $x$, for every $x$. The measures are: $\sum_j (t_j+1)^2$ over the middle gates whose output is not constant in $x$; the number $W=\sum_j t_j$ of bottom-to-middle wires; and the number $S = B+M+1$ of gates.
--
--   **Formalization Note** Wires into a gate form a set, the simple-circuit convention of Section 16.2. The accepting sets and negations are free because the paper leaves the gate conventions open (the constant $c$ in Eq. (425)). Every middle gate feeds the top gate.
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Theorem 7, p.5; Section 16.1–16.2, Eqs. (424)–(431), pp.67–68

import Mathlib

namespace CubicProductLB.Supplement

open Finset

/-- A `MOD2 ∘ MOD3 ∘ MOD2[k]` circuit on `n` Boolean inputs (Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Theorem 7, p.5; Section 16.1–16.2,
pp.67–68).

* `B` bottom MOD2 gates; bottom gate `b` reads the set `bottomIn b` of at most `k` inputs and outputs
  the XOR of those inputs, negated when `bottomNeg b` (Section 16.1: signed output `ε ∏_{i∈S} x_i`,
  `|S| ≤ k`, `ε ∈ {±1}`).
* `M` middle MOD3 gates; middle gate `j` reads the set `middleIn j` of bottom gates and outputs `1`
  exactly when the number of its inputs equal to `1`, taken mod 3, lies in `middleAcc j`.
* One top MOD2 gate, the XOR of all middle outputs, negated when `topNeg`.

**Formalization Note** Wires into a gate form a `Finset`: the simple-circuit convention of p.68 (at
most one wire between a fixed pair of gates). The accepting set `middleAcc j ⊆ Z/3` is arbitrary,
because the paper leaves the MOD3 gate convention open ("a constant c ∈ F3 depending only on the gate
convention", Eq. (425)); likewise each MOD2 gate may be negated. A bottom gate of fan-in `0` is a
constant. Every middle gate feeds the top gate; a middle gate that feeds nothing could be deleted
without increasing any measure. -/
structure Mod232Circuit (k n : ℕ) where
  /-- number of bottom gates -/
  B : ℕ
  /-- inputs of each bottom gate -/
  bottomIn : Fin B → Finset (Fin n)
  /-- bottom fan-in at most `k` -/
  bottom_fanIn_le : ∀ b, (bottomIn b).card ≤ k
  /-- negation bit of each bottom gate -/
  bottomNeg : Fin B → Bool
  /-- number of middle gates -/
  M : ℕ
  /-- bottom gates feeding each middle gate -/
  middleIn : Fin M → Finset (Fin B)
  /-- accepting residues of each middle MOD3 gate -/
  middleAcc : Fin M → Finset (ZMod 3)
  /-- negation bit of the top gate -/
  topNeg : Bool

namespace Mod232Circuit

variable {k n : ℕ} (C : Mod232Circuit k n)

/-- Output of bottom gate `b` on input `x`: XOR of its inputs, possibly negated. -/
def bottomOut (x : Fin n → Bool) (b : Fin C.B) : Bool :=
  xor (decide (((C.bottomIn b).filter fun i => x i = true).card % 2 = 1)) (C.bottomNeg b)

/-- Output of middle gate `j`: `1` iff the number of its bottom inputs equal to `1`, mod 3, is accepted. -/
def middleOut (x : Fin n → Bool) (j : Fin C.M) : Bool :=
  decide ((((C.middleIn j).filter fun b => C.bottomOut x b = true).card : ZMod 3) ∈ C.middleAcc j)

/-- Output of the circuit: XOR of all middle outputs, possibly negated. -/
def eval (x : Fin n → Bool) : Bool :=
  xor (decide ((univ.filter fun j => C.middleOut x j = true).card % 2 = 1)) C.topNeg

/-- The circuit computes the Boolean predicate `[q ∣ |x|]` at every `x ∈ {0,1}^n`. -/
def Computes (q : ℕ) : Prop :=
  ∀ x : Fin n → Bool, C.eval x = decide (q ∣ (univ.filter fun i => x i = true).card)

/-- `t_j`: the fan-in of middle gate `j` (the number of bottom-to-middle wires entering it). -/
def fanIn (j : Fin C.M) : ℕ := (C.middleIn j).card

/-- `Σ_j (t_j + 1)^2` over the middle gates whose output is not constant in `x`
(Theorem 7: "after constant middle gates are removed"). -/
noncomputable def quadCost : ℕ := by
  classical
  exact ∑ j ∈ univ.filter (fun j => ∃ x y, C.middleOut x j ≠ C.middleOut y j), (C.fanIn j + 1) ^ 2

/-- `W`: the number of bottom-to-middle wires, `Σ_j t_j` over all middle gates. -/
def wires : ℕ := ∑ j, C.fanIn j

/-- `S = B + M + 1`: the number of noninput gates (bottom, middle, top), p.68. -/
def size : ℕ := C.B + C.M + 1

end Mod232Circuit

end CubicProductLB.Supplement


