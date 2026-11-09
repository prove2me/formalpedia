-- Prove2me | Definitions.Def_SemAC02_Circ
-- name    : SemAC02_Circ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:26:53.90865+00:00
-- url     : https://prove2.me/theorems/a58fd48d-4f60-46b7-8c3b-f6fba36411fc
-- title:
--   AC0[2] circuits: evaluation, depth, subcircuits, size
-- statement:
--   An **AC0[2] circuit** over a set $V$ of Boolean variables is built from the constants $0,1$, the literals $x_v$ and $\neg x_v$ (negations occur only at the inputs) and gates $\bigwedge$, $\bigvee$, $\bigoplus$ of unbounded fan-in. An empty AND gate equals $1$; empty OR and XOR gates equal $0$.
--
--   * The **depth** counts gates: literals and constants have depth $0$, and a gate has depth one more than the largest depth of its children.
--   * The **subcircuits** of a circuit are the circuit itself and, recursively, the subcircuits of its children. The **size** of a family of circuits (or of a proof, read as the family of its lines) is the number of *distinct* rooted subcircuits appearing anywhere in it, shared between circuits.
--   * The **tree size** of a formula is its number of nodes counted with repetition.
--   * $g$ is **AND/OR** (an AC0 circuit) if it has no XOR gate, and **monotone** if moreover it has no negative literal.
--   * A circuit is in **normal form** if consecutive equal gate types are flattened (no gate has a child of its own type, i.e. the circuit is *alternating*) and no gate has two equal children.
--   * The **polarity flip** of $A$ replaces every literal $x_v$ by $\neg x_v$ and vice versa; it computes $A(\overline X)$.
--
--   These are the proof lines of semantic AC0[2]-Frege and the gadgets of the lifting construction.
--
--   **Formalization Note** Gates store their children as a `List`. The paper's circuits have unordered children, flattened equal gate types, AND/OR duplicates removed and XOR duplicates cancelled in pairs. A paper circuit is represented by a list presentation; evaluation, depth and distinct-subcircuit counts do not depend on the presentation, and normalising a list circuit never increases its depth or its number of distinct subterms. `IsReduced` is the normal form; `famSize`/`proofSize` count distinct subterms; `treeSize` counts nodes.
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), §2.2, p.17 (PDF p.19)

import Mathlib

namespace SemAC02

/-- **AC0[2] circuits** (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, *Hard Instances for
Strong Semantic Proof Systems*, manuscript (STOC 2027 submission), §2.2, p.17): Boolean variables
`V`, the constants, literals (negations only at inputs), and unbounded-fan-in AND, OR and XOR gates.

`lit v true` is the positive literal `x_v` and `lit v false` the negative literal `¬x_v`.

**Formalization Note** A gate stores its children as a `List`. The paper's circuits have
unordered children, with consecutive equal gate types flattened, repeated AND/OR children removed
and repeated XOR children cancelled in pairs. A paper circuit is represented by any of its list
presentations; evaluation, depth and the number of distinct subcircuits do not depend on the
presentation chosen, and normalising a list circuit (flattening, deduplicating, cancelling) never
increases its depth or its number of distinct subterms (see `IsReduced` for the predicate that
singles out normal-form presentations). -/
inductive Circ (V : Type) where
  | const : Bool → Circ V
  | lit : V → Bool → Circ V
  | and : List (Circ V) → Circ V
  | or : List (Circ V) → Circ V
  | xor : List (Circ V) → Circ V

namespace Circ

variable {V W : Type}

/-- Evaluation of a circuit at an assignment `x : V → Bool` (p.17). An empty AND gate equals `1`,
empty OR and XOR gates equal `0`. -/
def eval (x : V → Bool) : Circ V → Bool
  | const b => b
  | lit v b => if b then x v else !x v
  | and cs => (cs.map (fun c => eval x c)).all id
  | or cs => (cs.map (fun c => eval x c)).any id
  | xor cs => (cs.map (fun c => eval x c)).foldr Bool.xor false

/-- Depth (p.17): "Depth counts gates; literals and constants have depth zero." A gate has depth
one more than the largest depth of its children (`1` for a gate without children). -/
def depth : Circ V → ℕ
  | const _ => 0
  | lit _ _ => 0
  | and cs => 1 + (cs.map (fun c => depth c)).foldr max 0
  | or cs => 1 + (cs.map (fun c => depth c)).foldr max 0
  | xor cs => 1 + (cs.map (fun c => depth c)).foldr max 0

/-- Tree size (number of nodes, counted with repetition). Used for the sizes of the formulas of
§8.3; it is at least the number of distinct subcircuits, so an upper bound on it is the stronger
statement. -/
def treeSize : Circ V → ℕ
  | const _ => 1
  | lit _ _ => 1
  | and cs => 1 + (cs.map (fun c => treeSize c)).sum
  | or cs => 1 + (cs.map (fun c => treeSize c)).sum
  | xor cs => 1 + (cs.map (fun c => treeSize c)).sum

/-- Renaming of the variables along `f : V → W`. -/
def rename (f : V → W) : Circ V → Circ W
  | const b => const b
  | lit v b => lit (f v) b
  | and cs => and (cs.map (fun c => rename f c))
  | or cs => or (cs.map (fun c => rename f c))
  | xor cs => xor (cs.map (fun c => rename f c))

/-- Polarity flip of every literal: `flip A` computes `A(X̄)`, where `X̄` is the coordinatewise
complement of `X` (§8.1, p.62). It is not a negation gate (negations occur only at inputs). -/
def flip : Circ V → Circ V
  | const b => const b
  | lit v b => lit v (!b)
  | and cs => and (cs.map (fun c => flip c))
  | or cs => or (cs.map (fun c => flip c))
  | xor cs => xor (cs.map (fun c => flip c))

open Classical in
/-- The set of distinct rooted subcircuits of a circuit: the circuit itself together with the
subcircuits of its children. -/
noncomputable def subcircuits : Circ V → Finset (Circ V)
  | const b => {const b}
  | lit v b => {lit v b}
  | and cs => insert (and cs) ((cs.map (fun c => subcircuits c)).foldr (· ∪ ·) ∅)
  | or cs => insert (or cs) ((cs.map (fun c => subcircuits c)).foldr (· ∪ ·) ∅)
  | xor cs => insert (xor cs) ((cs.map (fun c => subcircuits c)).foldr (· ∪ ·) ∅)

/-- The circuit is an AND gate. -/
def isAnd : Circ V → Bool
  | and _ => true
  | _ => false

/-- The circuit is an OR gate. -/
def isOr : Circ V → Bool
  | or _ => true
  | _ => false

/-- The circuit is an XOR gate. -/
def isXor : Circ V → Bool
  | xor _ => true
  | _ => false

/-- The children of the root if it is an AND gate; otherwise the circuit itself as the only
conjunct. -/
def andChildren : Circ V → List (Circ V)
  | and cs => cs
  | c => [c]

/-- The children of the root if it is an OR gate; otherwise the circuit itself as the only
disjunct (the paper's "rudimentary arity-1 OR gate", p.63). -/
def orChildren : Circ V → List (Circ V)
  | or cs => cs
  | c => [c]

end Circ

open Circ

/-- An **AND/OR circuit** (AC0 circuit): no XOR gate occurs. -/
inductive NoXor {V : Type} : Circ V → Prop
  | const (b : Bool) : NoXor (Circ.const b)
  | lit (v : V) (b : Bool) : NoXor (Circ.lit v b)
  | and (cs : List (Circ V)) : (∀ c ∈ cs, NoXor c) → NoXor (Circ.and cs)
  | or (cs : List (Circ V)) : (∀ c ∈ cs, NoXor c) → NoXor (Circ.or cs)

/-- A **monotone** AND/OR circuit: no XOR gate and no negative literal. -/
inductive IsMonotoneCirc {V : Type} : Circ V → Prop
  | const (b : Bool) : IsMonotoneCirc (Circ.const b)
  | lit (v : V) : IsMonotoneCirc (Circ.lit v true)
  | and (cs : List (Circ V)) : (∀ c ∈ cs, IsMonotoneCirc c) → IsMonotoneCirc (Circ.and cs)
  | or (cs : List (Circ V)) : (∀ c ∈ cs, IsMonotoneCirc c) → IsMonotoneCirc (Circ.or cs)

/-- A circuit presented in the paper's **normal form** (p.17): "Consecutive equal gate types are
flattened; repeated children are removed for AND/OR and cancelled in pairs for XOR." No gate has a
child of its own gate type (in the terminology of Lemma 8.12, the circuit is *alternating*), and
the children of every gate are pairwise distinct. -/
inductive IsReduced {V : Type} : Circ V → Prop
  | const (b : Bool) : IsReduced (Circ.const b)
  | lit (v : V) (b : Bool) : IsReduced (Circ.lit v b)
  | and (cs : List (Circ V)) : cs.Nodup → (∀ c ∈ cs, c.isAnd = false) →
      (∀ c ∈ cs, IsReduced c) → IsReduced (Circ.and cs)
  | or (cs : List (Circ V)) : cs.Nodup → (∀ c ∈ cs, c.isOr = false) →
      (∀ c ∈ cs, IsReduced c) → IsReduced (Circ.or cs)
  | xor (cs : List (Circ V)) : cs.Nodup → (∀ c ∈ cs, c.isXor = false) →
      (∀ c ∈ cs, IsReduced c) → IsReduced (Circ.xor cs)

/-- The **size** of a family (or a proof) of circuits (p.18): the number of distinct rooted
subcircuits appearing anywhere in it, with sharing across circuits. -/
noncomputable def famSize {V : Type} (Fs : Finset (Circ V)) : ℕ :=
  open Classical in (Fs.biUnion Circ.subcircuits).card

/-- The size `size(π)` of a proof `π` (a list of circuits), p.18: the number of distinct rooted
subcircuits appearing anywhere in `π`. -/
noncomputable def proofSize {V : Type} (π : List (Circ V)) : ℕ :=
  open Classical in famSize π.toFinset

end SemAC02


