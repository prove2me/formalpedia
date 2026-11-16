-- Prove2me | Definitions.Def_TangleStructTree_Supplement_Sk
-- name    : TangleStructTree_Supplement_Sk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:05:32.461148+00:00
-- url     : https://prove2.me/theorems/4c6daa60-59e4-47ea-93ee-d44d89404229
-- title:
--   The separation system $\vec S_k$ of separations of order $<k$, and $\mathcal F$ read on it
-- statement:
--   Let $\vec S$ be a separation system with an order function $s\mapsto|s|$ and let $k\in\mathbb R$. Then
--
--   $$\vec S_k:=\{\vec s\in\vec S:\ |s|<k\}$$
--
--   is again an ordered separation system, with the order, the involution and the order function restricted from $\vec S$.
--
--   A set $\mathcal F$ of subsets of $\vec S$ is **read on $\vec S_k$** as the family of those $\sigma\subseteq\vec S_k$ that belong to $\mathcal F$; elements of $\mathcal F$ that are not subsets of $\vec S_k$ never occur as subsets of orientations of $S_k$, so they do not matter there. This is the sense in which the paper speaks of $\mathcal F$-tangles of $S_k$ and of $\mathcal F$ being rich (or standard) for $\vec S_k$.
--
--   **Formalization Note** $\vec S_k$ is the subtype of oriented separations $x$ with $|x|<k$ and $|x^*|<k$; for an order function ($|x^*|=|x|$) this is $\{x:|x|<k\}$, and the second condition makes the subtype closed under the involution without a hypothesis.
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), §2, p.5 (PDF 16): definition of S⃗_k; §6, pp.17–18 (PDF 28–29)

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem

namespace TangleStructTree

namespace Supplement

open SepSystem

variable {E : Type*} [PartialOrder E] [SepSystem E]

/-- "For every `k ∈ ℝ` we let `S⃗_k := {s⃗ ∈ S⃗ : |s| < k}`; this is again an ordered separation
system" (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, §2, p.5 (PDF 16)).

**Formalization Note** `S⃗_k` is the subtype of oriented separations `x` with `ord x < k` and
`ord (x∗) < k`; for an order function (`ord (x∗) = ord x`) this is `{x : ord x < k}`, and the second
condition makes the subtype closed under `∗` without a hypothesis on `ord`. It carries the induced
partial order, the restricted involution, and the order function `x ↦ ord x`. -/
abbrev Sk (ord : E → ℝ) (k : ℝ) : Type _ :=
  {x : E // ord x < k ∧ ord (rev x) < k}

/-- The restricted involution on `S⃗_k`. -/
instance instSepSystemSk (ord : E → ℝ) (k : ℝ) : SepSystem (Sk ord k) where
  rev x := ⟨rev x.1, x.2.2, by rw [rev_rev]; exact x.2.1⟩
  rev_rev x := Subtype.ext (rev_rev x.1)
  rev_le_rev x y h := rev_le_rev x.1 y.1 h

/-- `ℱ`, read on `S⃗_k`: the subsets `σ ⊆ S⃗_k` that are elements of `ℱ`
(von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, §2, p.6 (PDF 17): `ℱ` is "any set"; the `ℱ`-tangles of `S_k` and "`ℱ` rich
for `S⃗_k`", p.18 (PDF 29), refer to the elements of `ℱ` that are subsets of `S⃗_k`). -/
def restrictFamily (ord : E → ℝ) (k : ℝ) (ℱ : Set (Set E)) : Set (Set (Sk ord k)) :=
  {σ | Subtype.val '' σ ∈ ℱ}

end Supplement

end TangleStructTree


