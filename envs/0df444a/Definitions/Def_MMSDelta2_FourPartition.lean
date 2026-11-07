-- Prove2me | Definitions.Def_MMSDelta2_FourPartition
-- name    : MMSDelta2_FourPartition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:58:47.712008+00:00
-- url     : https://prove2.me/theorems/6ab80d27-3e66-4b23-afe8-fecdfba031d7
-- title:
--   4-PARTITION, incidence strings and LexMax4Partition-Promise
-- statement:
--   An instance of **4-PARTITION** is a multiset $W=\{w_1,\dots,w_{4q}\}$ of positive integers, $q\ge1$, and an integer $T$ with $\sum_{j=1}^{4q}w_j=qT$ and $T/5<w_j<T/3$ for every $j$. A **solution** $\mathcal S=(S_1,\dots,S_q)$ is an ordered tuple of pairwise disjoint four-element submultisets whose union is $W$ and each of which sums to exactly $T$. Its **incidence matrix** $\mathrm{inc\text{-}mat}(\mathcal S)\in\{0,1\}^{q\times 4q}$ has $\mathrm{inc\text{-}mat}(\mathcal S)_{j,i}=1$ iff $w_i\in S_j$, and its **incidence string** reads the matrix column by column:
--
--   $$\mathrm{inc}(\mathcal S)=\big(\mathrm{inc\text{-}mat}(\mathcal S)_{1,1},\dots,\mathrm{inc\text{-}mat}(\mathcal S)_{q,1},\dots,\mathrm{inc\text{-}mat}(\mathcal S)_{1,4q},\dots,\mathrm{inc\text{-}mat}(\mathcal S)_{q,4q}\big)\in\{0,1\}^{4q^2}.$$
--
--   In **LexMax4Partition-Promise** the instance is promised to admit a solution; with $\mathcal S^*$ the solution whose incidence string is lexicographically maximum, the question is whether the last bit $\mathrm{inc\text{-}mat}(\mathcal S^*)_{q,4q}$ is $1$. For a constant $C$, the restricted problem additionally promises $T\le C\,q^4$.
--
--   **Formalization Note** The numbers are indexed, $w:\{0,\dots,4q-1\}\to\mathbb N$, and a solution is a map $\sigma$ sending number $i$ to its part, every part receiving four numbers of sum $T$; then $\mathrm{inc\text{-}mat}_{j,i}=1$ iff $\sigma(i)=j$ (0-based indices). Strings are compared lexicographically with $0<1$. Instances are encoded by the codes of $q$, $T$ and $w_1,\dots,w_{4q}$.
-- source:
--   Gupta, Seetharaman, The Existence of Maximin Share Allocations is Δ₂ᴾ-complete, arXiv:2609.15841 (held version, sha256 a43b06b9…), §7, pp.26–27 (PDF pp.28–29); §4, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_MMSDelta2_Delta2P
import Definitions.Def_MMSDelta2_instCode

namespace MMSDelta2

/-!
# 4-PARTITION, incidence strings and LexMax4Partition-Promise

S. Gupta, S. Seetharaman, *The Existence of Maximin Share Allocations is Δ₂ᴾ-complete*,
arXiv:2609.15841 (held version, sha256 a43b06b9…), §7, pp.26–27 (PDF pp.28–29): "In an instance of
4-PARTITION, we are given a multiset `W = {w_1, …, w_{4q}}` of positive integers and an integer `T`
such that `Σ_{j=1}^{4q} w_j = qT` and `T/5 < w_j < T/3` for every `j ∈ [4q]`. A solution `S` is an
ordered tuple `(S_1, …, S_q)` of pairwise disjoint four-element submultisets whose union is `W` and
such that every `S_j` sums to exactly `T`." The incidence string reads `inc-mat(S)` column by
column; LexMax4Partition-Promise asks whether the last bit of the lexicographically maximum
incidence string is `1`, under the promise that a solution exists.

**Formalization Note.**
* The multiset is indexed: `w : Fin (4q) → ℕ`, `q ≥ 1`, and `T/5 < w_j < T/3` is `T < 5 w_j` and
  `3 w_j < T`. Indices are 0-based: number `i` is `w_{i+1}`, part `j` is `S_{j+1}`.
* A solution is `σ : Fin (4q) → Fin q` (number `i` goes to part `σ i`) whose every fibre has four
  elements and sum `T`. `inc-mat(S)_{j,i} = 1` iff `σ i = j`. The incidence string lists, for
  `i = 0, …, 4q−1`, the bits `[σ i = 0], …, [σ i = q−1]`; it determines `σ`.
* Strings are compared with the lexicographic order of `List Bool`, `false < true`.
* `LexMax4PartPromise C` restricts the promise to instances with `T ≤ C·q⁴`; every number is then
  below `T/3`, hence also `O(q⁴)`.
* Code: `natCode q`, `natCode T`, then `natCode w_i` for `i = 0, …, 4q−1`.
-/

/-- An instance of 4-PARTITION. -/
structure FourPartInstance where
  /-- the number of parts -/
  q : ℕ
  /-- the `4q` numbers -/
  w : Fin (4 * q) → ℕ
  /-- the target -/
  T : ℕ
  hq : 1 ≤ q
  hpos : ∀ j, 0 < w j
  hsum : ∑ j, w j = q * T
  hlow : ∀ j, T < 5 * w j
  hhigh : ∀ j, 3 * w j < T

namespace FourPartInstance

/-- `σ` is a solution: every part receives exactly four numbers, summing to `T`. -/
def IsSolution (I : FourPartInstance) (σ : Fin (4 * I.q) → Fin I.q) : Prop :=
  ∀ j, (Finset.univ.filter (fun i => σ i = j)).card = 4 ∧
    ∑ i ∈ Finset.univ.filter (fun i => σ i = j), I.w i = I.T

/-- The instance has a solution (the promise of LexMax4Partition-Promise). -/
def HasSolution (I : FourPartInstance) : Prop := ∃ σ, I.IsSolution σ

end FourPartInstance

/-- The incidence string `inc(S)`: the incidence matrix read column by column. -/
def incString {q : ℕ} (σ : Fin (4 * q) → Fin q) : List Bool :=
  (List.finRange (4 * q)).flatMap fun i => (List.finRange q).map fun j => decide (σ i = j)

namespace FourPartInstance

/-- `σ` is a solution with lexicographically maximum incidence string. -/
def IsLexMaxSolution (I : FourPartInstance) (σ : Fin (4 * I.q) → Fin I.q) : Prop :=
  I.IsSolution σ ∧ ∀ σ', I.IsSolution σ' → ¬ (incString σ < incString σ')

/-- The last bit of the lexicographically maximum incidence string is `1`. -/
def LastBitOne (I : FourPartInstance) : Prop :=
  ∃ σ, I.IsLexMaxSolution σ ∧ (incString σ).getLast? = some true

end FourPartInstance

/-- The binary code of a 4-PARTITION instance. -/
def fourPartCode (I : FourPartInstance) : List Bool :=
  natCode I.q ++ natCode I.T ++ (List.ofFn fun j => natCode (I.w j)).flatten

/-- LexMax4Partition-Promise restricted to instances with `T ≤ C·q⁴` (Lemma 7.1). -/
def LexMax4PartPromise (C : ℕ) : KarpLiptonOM.PromiseProblem :=
  promiseOn {x | ∃ I : FourPartInstance, I.HasSolution ∧ I.T ≤ C * I.q ^ 4 ∧ x = fourPartCode I}
    {x | ∃ I : FourPartInstance, I.LastBitOne ∧ x = fourPartCode I}

end MMSDelta2


