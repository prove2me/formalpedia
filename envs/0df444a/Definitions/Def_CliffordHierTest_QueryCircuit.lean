-- Prove2me | Definitions.Def_CliffordHierTest_QueryCircuit
-- name    : CliffordHierTest_QueryCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:21:59.503764+00:00
-- url     : https://prove2.me/theorems/a7407743-3f47-48f5-9ac2-ea5ebb52c9e8
-- title:
--   Qudit query circuits with oracle gates for $U$ and $U^*$
-- statement:
--   A **query circuit** for an unknown $n$-qudit unitary $U$ acts on $m+1$ qudit wires of dimension $d$, starting in the basis state $|0\cdots0\rangle$. It is a fixed list of gates, each of which is either an **elementary gate** (an arbitrary unitary acting on at most three wires, identity elsewhere) or an **oracle gate** (the unknown $U$, or its inverse $U^*$, applied to $n$ distinct wires in a chosen order, identity elsewhere). After the last gate, wire $0$ is measured in the computational basis; the circuit **outputs $1$** if it reads $1$ and outputs $0$ otherwise. The **number of queries** is the number of oracle gates (to $U$ and $U^*$ together) and the **size** is the total number of gates.
--
--   This is the model of computation in which the main theorem's tester is stated: an algorithm with query access to $U$ and $U^*$ touches the unknown unitary only through oracle gates.
--
--   **Formalization Note** The source names no model. There is no controlled-oracle gate and no gate depending on $U$ otherwise. Intermediate measurements and random coins are not primitives; by the principle of deferred measurement, a unitary circuit followed by one final measurement loses no generality. The circuit is a Lean structure with the number of wires and a `List` of gates; `acceptProb A U` is the probability of output $1$.
-- source:
--   Bao, Briët, Castro-Silva, van Dordrecht, Helsen, On Clifford hierarchy testing and near-extremizers of noncommutative uniformity norms, arXiv:2605.26983 (held version, sha256 610d53a6…), Theorem 1, p.2 (query access to U and U*, efficient algorithm, O(1/ε) queries); Algorithm 1, p.12

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

open scoped Matrix

namespace CliffordHierTest

/-!
# Qudit query circuits with oracle gates for `U` and `U*`

Z. Bao, J. Briët, D. Castro-Silva, P. van Dordrecht, J. Helsen, *On Clifford hierarchy testing and
near-extremizers of noncommutative uniformity norms*, arXiv:2605.26983 (held version, sha256
610d53a6…), Theorem 1, p.2 ("query access to a unitary `U ∈ 𝒰(dⁿ)` and its inverse `U*`, … an
efficient algorithm … that makes `O(1/ε)` queries to `U` and `U*`"); Algorithm 1, p.12.

**Formalization Note.** The paper names no model of computation; this is the model its goal
statement is read in. A circuit acts on `m + 1` wires, each a `d`-dimensional qudit (computational
basis `Fin (m + 1) → ZMod d`), and starts in the all-zero basis state `|0⋯0⟩`. Each gate is either

* an *elementary gate*: an arbitrary unitary on at most `3` wires, placed on the wires picked out by
  an injection `Fin k ↪ Fin (m + 1)` (`k ≤ 3`), identity on the other wires; or
* an *oracle gate*: the unknown unitary `U` (or its adjoint `U*`, flag `dagger = true`) placed on
  `n` distinct wires in the order given by an injection `Fin n ↪ Fin (m + 1)`, identity elsewhere.

There is no controlled-oracle gate and no gate that depends on `U` otherwise: the paper grants only
query access to `U` and `U*`. Intermediate measurements and random coins are not primitives (by the
principle of deferred measurement a unitary circuit followed by one final measurement loses no
generality). The output is the computational-basis measurement of wire `0`: the circuit outputs `1`
iff that wire reads `1`, and outputs `0` otherwise, so `P[output 0] = 1 − P[output 1]`.
`queries` counts the oracle gates (`U` and `U*` together) and `size` counts all gates.
-/

open QAlgorithms.Papers.Independent.Extend50.P30

/-- Computational basis of `m` qudit wires. -/
abbrev WireBasis (d m : ℕ) := Fin m → ZMod d

open Classical in
/-- The operator `G` on the wires `e(0), …, e(k-1)` (in that order), tensored with the identity on
all other wires: entry `(x, y)` is `G (x ∘ e) (y ∘ e)` if `x` and `y` agree off the range of `e`,
and `0` otherwise. -/
noncomputable def embedGate {d m k : ℕ} [NeZero d] (e : Fin k ↪ Fin m)
    (G : Matrix (Fin k → ZMod d) (Fin k → ZMod d) ℂ) : Matrix (WireBasis d m) (WireBasis d m) ℂ :=
  fun x y => if ∀ j, j ∉ Set.range e → x j = y j then G (x ∘ e) (y ∘ e) else 0

/-- A gate of a circuit on `m` wires querying an `n`-qudit oracle: an elementary unitary on at most
three wires, or a query to `U` (`dagger = false`) or `U*` (`dagger = true`) on `n` distinct wires. -/
inductive Gate (d n m : ℕ) [NeZero d] where
  | elem (k : ℕ) (hk : k ≤ 3) (e : Fin k ↪ Fin m) (G : Matrix.unitaryGroup (Fin k → ZMod d) ℂ)
  | query (e : Fin n ↪ Fin m) (dagger : Bool)

namespace Gate

variable {d n m : ℕ} [NeZero d]

/-- Whether a gate is an oracle gate. -/
def isQuery : Gate d n m → Bool
  | elem .. => false
  | query .. => true

/-- The operator a gate applies when the oracle is `U`. -/
noncomputable def toMatrix (U : QuditOperator d n) : Gate d n m → Matrix (WireBasis d m) (WireBasis d m) ℂ
  | elem _ _ e G => embedGate e (G : Matrix (Fin _ → ZMod d) (Fin _ → ZMod d) ℂ)
  | query e false => embedGate e U
  | query e true => embedGate e Uᴴ

end Gate

/-- A query circuit: `wires + 1` qudit wires (wire `0` is the output wire) and a list of gates,
applied in list order. It is fixed before the oracle `U` is given. -/
structure Circuit (d n : ℕ) [NeZero d] where
  wires : ℕ
  gates : List (Gate d n (wires + 1))

namespace Circuit

variable {d n : ℕ} [NeZero d]

/-- The initial basis state `|0⋯0⟩`. -/
def initState (m : ℕ) : WireBasis d m → ℂ := fun x => if x = 0 then 1 else 0

/-- The final state of the circuit run with oracle `U`. -/
noncomputable def run (A : Circuit d n) (U : QuditOperator d n) : WireBasis d (A.wires + 1) → ℂ :=
  A.gates.foldl (fun ψ g => (g.toMatrix U).mulVec ψ) (initState (A.wires + 1))

/-- The probability that the circuit outputs `1`: wire `0` reads `1` in the final measurement. -/
noncomputable def acceptProb (A : Circuit d n) (U : QuditOperator d n) : ℝ :=
  ∑ x : WireBasis d (A.wires + 1), if x 0 = 1 then Complex.normSq (A.run U x) else 0

/-- The number of oracle gates (queries to `U` and `U*` together). -/
def queries (A : Circuit d n) : ℕ := (A.gates.filter Gate.isQuery).length

/-- The number of gates, oracle gates included. -/
def size (A : Circuit d n) : ℕ := A.gates.length

end Circuit

end CliffordHierTest


