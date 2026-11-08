-- Prove2me | Definitions.Def_ParityCubes_blockPower
-- name    : ParityCubes_blockPower
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T10:15:12.345504+00:00
-- url     : https://prove2.me/theorems/61844ddd-aaa6-47f4-9663-114d40da60ce
-- title:
--   The block substitution $f^w$
-- statement:
--   Assign to each variable $x_i$ a block $B_i$ of new variables, the blocks disjoint and covering the new variables, and write $w_i=|B_i|$. Put
--
--   $$P_i=\prod_{b\in B_i}b,\qquad E_i=\sum_{b\in B_i}\ \prod_{c\in B_i\setminus\{b\}}c,\qquad f^w=\Big(\prod_i E_i\Big)\,f(P_1,\dots,P_n),$$
--
--   over $\mathbb F_2$. For $I$ a set of new variables, $J(I)=\{i:B_i\subseteq I\}$ is the set of blocks contained in $I$.
--
--   With odd block sizes, this substitution makes a zero cube pay for a whole block (Lemma 4.2).
--
--   **Formalization Note.** The blocks are the fibres of a map `blk` from new variables to old ones, which makes them disjoint and covering by construction. Oddness of the $w_i$ is a hypothesis of the statements that use $f^w$.
-- source:
--   Sheshadri, Smirnov, The Complexity of Choosing Parity Projections, arXiv:2611.00289 (manuscript sha256 95994d2d…), §4, p.8 (PDF p.9)

import Mathlib

set_option autoImplicit false

namespace ParityCubes

/-- `P_i = ∏_{b ∈ B_i} b`, the product of the variables of block `B_i = blk⁻¹(i)`
(Sheshadri–Smirnov, arXiv:2611.00289, manuscript sha256 95994d2d…, §4, p.8 (PDF p.9)). -/
def blockP {α β : Type*} [Fintype β] [DecidableEq α] (blk : β → α) (x : β → Bool) (i : α) : Bool :=
  decide (∀ b : β, blk b = i → x b = true)

/-- `E_i = Σ_{b ∈ B_i} ∏_{c ∈ B_i ∖ {b}} c` over `𝔽₂` (§4, p.8 (PDF p.9)): the parity of the number
of `b ∈ B_i` such that every other variable of the block is `1`. -/
def blockE {α β : Type*} [Fintype β] [DecidableEq α] [DecidableEq β] (blk : β → α) (x : β → Bool)
    (i : α) : Bool :=
  decide (Odd (Finset.univ.filter
    (fun b : β => blk b = i ∧ ∀ c : β, blk c = i → c ≠ b → x c = true)).card)

/-- The **block substitution** `f^w = (∏_i E_i) · f(P_1, …, P_n)` (§4, p.8 (PDF p.9)). The variables
`x_i` of `f` are indexed by `α`; the new variables are indexed by `β`, and `blk : β → α` sends each
new variable to the index of its block, so the blocks `B_i = blk⁻¹(i)` are disjoint and cover `β`.

**Formalization Note.** The weights `w_i = |B_i|` are the fibre sizes of `blk`
(`blockWeight`); oddness of the weights is a hypothesis of the statements that use `f^w`. -/
def blockPower {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (f : (α → Bool) → Bool) (blk : β → α) (x : β → Bool) : Bool :=
  decide (∀ i : α, blockE blk x i = true) && f (blockP blk x)

/-- `w_i = |B_i|`, the size of block `i`. -/
def blockWeight {α β : Type*} [Fintype β] [DecidableEq α] (blk : β → α) (i : α) : ℕ :=
  (Finset.univ.filter (fun b : β => blk b = i)).card

/-- `J(I) = {i : B_i ⊆ I}`, the set of blocks contained in `I` (Lemma 4.2, p.8 (PDF p.9)). -/
def blocksInside {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (blk : β → α)
    (I : Finset β) : Finset α :=
  Finset.univ.filter (fun i : α => ∀ b : β, blk b = i → b ∈ I)

end ParityCubes


