-- Prove2me | Definitions.Def_LogStarBinPacking_FSInput
-- name    : LogStarBinPacking_FSInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:31:43.497337+00:00
-- url     : https://prove2.me/theorems/2f4f556f-7cc0-49ce-b3fd-aea64d775f57
-- title:
--   Inputs of the finite-state reduction (Lemma 2.1) and the raw form of $J$
-- statement:
--   An input of the finite-state reduction of Lemma 2.1 consists of a bin packing instance $I$, an integer $b\ge1$, a finite set $V$, a function $h:V\to[0,1]\cap\mathbb Q$ and a rational $\varepsilon>0$ with $|V|\ge|I|+b$.
--
--   As data a machine reads, the input lists:
--
--   1. the sizes of $I$ as pairs $(p,q)$ meaning $p/q$;
--   2. the integer $b$;
--   3. the values of $h$ as pairs $(p,q)$, the states being $V=\{0,\dots,|V|-1\}$;
--   4. $\varepsilon$ as a pair $(p,q)$.
--
--   The input is **valid** if every size lies in $(0,1]$, $b\ge1$, every load lies in $[0,1]$, $\varepsilon>0$ and $|V|\ge|I|+b$. The bundle also defines the binary encoding of an input (and of an input with a packing) from the published self-delimiting encodings, and the instance $J$ of the proof of Lemma 2.1 in raw form: the pair $(M,J)$ with $M=|V|+b$ and the items of $J$ listed class by class ($S^+,S^-,X,X^0,E^-_1,E^-_2,E^+_1,E^+_2$) with the sizes (2.5).
--
--   These are the objects through which the polynomial-time statements (Lemma 2.1, Claim 2.6) are expressed.
--
--   **Formalization Note** A rational $q$ of $J$ is stored as $(\mathrm{num}(q),\mathrm{den}(q))$. A load may be $0$, so loads are not a published raw instance.
-- source:
--   I. Doron-Arad, Additive Ω(log∗ OPT) Gap for Bin Packing with Three Items per Bin, manuscript (sha256 1d88425d…), Lemma 2.1, p.4; proof of Lemma 2.1, pp.4–5

import Mathlib
import Definitions.Def_BinPackingGap
import Definitions.Def_LogStarBinPacking_ThreeItem

namespace LogStarBinPacking

open OAI.BinPackingGap

/-- **The input of the finite-state reduction of Lemma 2.1.** Doron-Arad, *Additive Ω(log∗ OPT)
Gap for Bin Packing with Three Items per Bin*, manuscript (sha256 1d88425d…), Lemma 2.1, p.4:
a bin packing instance `I`, an integer `b ≥ 1`, a finite set `V`, a function
`h : V → [0, 1] ∩ ℚ` and a rational `ε > 0` with `|V| ≥ |I| + b`.

**Formalization Note** The record lists `I` as a raw instance (pairs `(p, q)` for the size
`p/q`), `b`, the values of `h` as a list of pairs `(p, q)` for `p/q` with the states
`V = Fin |list|`, and `ε` as a pair `(p, q)` for `p/q`. `Valid` is the paper's domain; `bits` is
the binary encoding a machine reads, built from the published self-delimiting encodings. The bundle
also holds the raw form of the instance `J` of the proof of Lemma 2.1, listed class by class, for
Claim 2.6. -/
structure FSInput where
  inst : RawInstance
  b : ℕ
  loads : List (ℕ × ℕ)
  eps : ℕ × ℕ

namespace FSInput

/-- The domain of Lemma 2.1: `I` valid (sizes in `(0, 1]`), `b ≥ 1`, every load in `[0, 1]` with a
positive denominator, `ε > 0`, and `|V| ≥ |I| + b`. -/
def Valid (x : FSInput) : Prop :=
  x.inst.Valid ∧ 1 ≤ x.b ∧ (∀ q ∈ x.loads, 0 < q.2 ∧ q.1 ≤ q.2) ∧
    0 < x.eps.1 ∧ 0 < x.eps.2 ∧ x.inst.length + x.b ≤ x.loads.length

/-- The state set `V = Fin |V|`. -/
abbrev State (x : FSInput) : Type := Fin x.loads.length

/-- The load function `h : V → [0, 1] ∩ ℚ`. -/
def load (x : FSInput) (v : x.State) : ℚ := RawInstance.ratValue (x.loads.get v)

/-- The rational `ε`. -/
def epsilon (x : FSInput) : ℚ := RawInstance.ratValue x.eps

/-- The size `s_I(i)` of the `i`-th source item, read from the raw list. -/
def sourceSize (x : FSInput) (i : Fin x.inst.length) : ℚ := RawInstance.ratValue (x.inst.get i)

/-- The source instance `I`. -/
def source (x : FSInput) (hx : x.Valid) : Instance := x.inst.toInstance hx.1

/-- The binary encoding of the input. -/
def bits (x : FSInput) : List Bool :=
  BinaryEncoding.rawInstanceBits x.inst ++ BinaryEncoding.natBits x.b ++
    BinaryEncoding.listBits (BinaryEncoding.pairBits BinaryEncoding.natBits BinaryEncoding.natBits)
      x.loads ++
    BinaryEncoding.pairBits BinaryEncoding.natBits BinaryEncoding.natBits x.eps

/-- The binary encoding of an input together with a raw packing (the decoder's input). -/
def packingBits (xp : FSInput × RawPacking) : List Bool :=
  bits xp.1 ++ BinaryEncoding.rawPackingBits xp.2

/-- The number `f = |V| − n − b` of filler items. -/
def fillers (x : FSInput) : ℕ := x.loads.length - x.inst.length - x.b

/-- The items of `J`, listed class by class: `S⁺`, `S⁻`, `X`, `X⁰`, `E⁻₁`, `E⁻₂`, `E⁺₁`, `E⁺₂`. -/
def jItems (x : FSInput) : List (ThreeItem x.State x.inst.length x.fillers x.b) :=
  (List.finRange x.loads.length).map ThreeItem.sPlus ++
  (List.finRange x.loads.length).map ThreeItem.sMinus ++
  (List.finRange x.inst.length).map ThreeItem.src ++
  (List.finRange x.fillers).map ThreeItem.filler ++
  (List.finRange x.b).map ThreeItem.eMinus1 ++
  (List.finRange x.b).map ThreeItem.eMinus2 ++
  (List.finRange x.b).map ThreeItem.ePlus1 ++
  (List.finRange x.b).map ThreeItem.ePlus2

/-- A nonnegative rational `q` as the pair `(numerator, denominator)`. -/
def rawPair (q : ℚ) : ℕ × ℕ := (q.num.toNat, q.den)

/-- **The instance `J` of the proof of Lemma 2.1 in raw form**, pp.4–5: the pair `(M, J)` with
`M = |V| + b` and the sizes (2.5) of the items of `J` in the order of `jItems`. -/
def threeItemRaw (x : FSInput) : RawReductionOutput :=
  (x.loads.length + x.b,
    (jItems x).map fun u => rawPair (ThreeItem.size x.sourceSize x.load x.epsilon u))

end FSInput

end LogStarBinPacking


