-- Prove2me | Definitions.Def_LogStarBinPacking_FiveClassRaw
-- name    : LogStarBinPacking_FiveClassRaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:20.572269+00:00
-- url     : https://prove2.me/theorems/db3119ad-75e4-45a3-9b53-8ef75df4f5f9
-- title:
--   Instances with five item classes, feasible five-tuples and (fractional) five-tuple partitions
-- statement:
--   Fix an integer $N\ge1$ and an instance $I$ with a specified partition $I=A\,\dot\cup\,B\,\dot\cup\,C\,\dot\cup\,D\,\dot\cup\,E$ into five **item classes** with $|A|=|B|=|C|=|D|=|E|=N$.
--
--   1. A **feasible five-tuple** is $(a,b,c,d,e)\in A\times B\times C\times D\times E$ with $s_I(a)+s_I(b)+s_I(c)+s_I(d)+s_I(e)\le1$.
--   2. A **partition into feasible five-tuples** is a family of feasible five-tuples whose underlying five-element sets partition $I$.
--   3. A **fractional partition** assigns nonnegative weights to feasible five-tuples so that each item belongs to tuples of total weight one.
--
--   These notions are the interface between the five-item construction of [OAI26] (Proposition 3.1) and the three-item reduction (Lemma 2.2).
--
--   **Formalization Note** An instance with five classes is $(N,[A,B,C,D,E])$, each class a list of sizes $(p,q)$ meaning $p/q$; it is valid if $N\ge1$, there are five classes, each with $N$ items of size in $(0,1]$. $I$ is the concatenation $A,B,C,D,E$, so the item at position $i$ (0-based) lies in class $\lfloor i/N\rfloor$. A five-tuple is a map $t:\{0,\dots,4\}\to I$ with $t(j)$ in class $j$; weights are real and vanish off feasible tuples. The bundle also defines the binary encodings of an instance and of an instance with a packing.
-- source:
--   I. Doron-Arad, Additive Ω(log∗ OPT) Gap for Bin Packing with Three Items per Bin, manuscript (sha256 1d88425d…), §2.2, p.8

import Mathlib
import Definitions.Def_BinPackingGap

namespace LogStarBinPacking

open OAI.BinPackingGap

/-- **Instances with five item classes.** Doron-Arad, *Additive Ω(log∗ OPT) Gap for Bin Packing
with Three Items per Bin*, manuscript (sha256 1d88425d…), §2.2, p.8: an integer `N ≥ 1` and an
instance `I` with a specified partition `I = A ∪̇ B ∪̇ C ∪̇ D ∪̇ E`, `|A| = … = |E| = N`. A
*feasible five-tuple* is `(a, b, c, d, e) ∈ A × B × C × D × E` with
`s_I(a) + s_I(b) + s_I(c) + s_I(d) + s_I(e) ≤ 1`. A *partition into feasible five-tuples* means
that their underlying five-element sets partition `I`. A *fractional partition* assigns
nonnegative weights to feasible five-tuples so that each item belongs to tuples of total weight
one.

**Formalization Note** `FiveClassRaw` is `(N, [A, B, C, D, E])`, each class a raw instance (pairs
`(p, q)` for the size `p/q`). The instance `I` is the concatenation `A ++ B ++ C ++ D ++ E`, so the
item at position `i` lies in class `⌊i / N⌋` (`0`-based). A five-tuple is a map `t : Fin 5 → I`
with `t j` in class `j`. -/
abbrev FiveClassRaw : Type := ℕ × List RawInstance

namespace FiveClassRaw

/-- `N ≥ 1`, five classes, each of `N` items with sizes in `(0, 1]`. -/
def Valid (y : FiveClassRaw) : Prop :=
  1 ≤ y.1 ∧ y.2.length = 5 ∧ ∀ c ∈ y.2, c.length = y.1 ∧ RawInstance.Valid c

/-- The instance `I` as one raw list, `A ++ B ++ C ++ D ++ E`. -/
def flat (y : FiveClassRaw) : RawInstance := y.2.flatten

theorem Valid.flat_valid {y : FiveClassRaw} (hy : y.Valid) : (flat y).Valid := by
  intro q hq
  obtain ⟨c, hc, hqc⟩ := List.mem_flatten.mp hq
  exact (hy.2.2 c hc).2 q hqc

/-- The instance `I`. -/
def toInstance (y : FiveClassRaw) (hy : y.Valid) : Instance := (flat y).toInstance hy.flat_valid

/-- A feasible five-tuple: one item of each class, `t j` in class `j`, of total size at most one. -/
def IsFeasibleTuple (y : FiveClassRaw) (hy : y.Valid) (t : Fin 5 → (toInstance y hy).Item) :
    Prop :=
  (∀ j : Fin 5, (t j).val / y.1 = j.val) ∧ ∑ j, (toInstance y hy).size (t j) ≤ 1

/-- `I` has a partition into feasible five-tuples: a family of feasible five-tuples whose
underlying sets partition `I`, i.e. every item lies in exactly one tuple of the family. -/
def HasTuplePartition (y : FiveClassRaw) (hy : y.Valid) : Prop :=
  ∃ S : Finset (Fin 5 → (toInstance y hy).Item), (∀ t ∈ S, IsFeasibleTuple y hy t) ∧
    ∀ i : (toInstance y hy).Item, ∃! t, t ∈ S ∧ ∃ j, t j = i

/-- `I` has a fractional partition into feasible five-tuples: nonnegative weights, zero off the
feasible five-tuples, such that each item belongs to tuples of total weight one. -/
def HasFractionalTuplePartition (y : FiveClassRaw) (hy : y.Valid) : Prop :=
  ∃ x : (Fin 5 → (toInstance y hy).Item) → ℝ, (∀ t, 0 ≤ x t) ∧
    (∀ t, ¬ IsFeasibleTuple y hy t → x t = 0) ∧
    ∀ i : (toInstance y hy).Item,
      ∑ t ∈ Finset.univ.filter (fun t : Fin 5 → (toInstance y hy).Item => ∃ j, t j = i), x t = 1

/-- The binary encoding: `N`, then the list of classes. -/
def bits (y : FiveClassRaw) : List Bool :=
  BinaryEncoding.natBits y.1 ++ BinaryEncoding.listBits BinaryEncoding.rawInstanceBits y.2

/-- The binary encoding of an instance together with a raw packing (the decoder's input). -/
def packingBits (yp : FiveClassRaw × RawPacking) : List Bool :=
  bits yp.1 ++ BinaryEncoding.rawPackingBits yp.2

end FiveClassRaw

end LogStarBinPacking


