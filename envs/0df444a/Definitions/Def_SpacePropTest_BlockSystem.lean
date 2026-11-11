-- Prove2me | Definitions.Def_SpacePropTest_BlockSystem
-- name    : SpacePropTest_BlockSystem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:55:55.083056+00:00
-- url     : https://prove2.me/theorems/459fa86f-a4bc-4d5d-a5f9-234ea548a680
-- title:
--   $(I,\beta)$-block systems and corruptible properties (Definitions 34–35)
-- statement:
--   Let $I$ be a non-empty finite index set and $0<\beta\le1$. An **$(I,\beta)$-block system** consists of
--
--   1. pairwise disjoint blocks $B_i\subseteq\{0,1\}^n$ ($i\in I$) with $\sum_{i\in I}|B_i|\ge\beta\,2^n$ and $|B_i|\le2^n/|I|$;
--   2. sub-blocks $C_i\subseteq B_i$;
--   3. a background map $b:\{0,1\}^n\setminus\bigcup_iB_i\to\{0,1\}$.
--
--   For $c\in\{0,1\}^I$ let $f_c(x)=c_i$ if $x\in B_i$ and $f_c(x)=b(x)$ otherwise, and for $J\subseteq I$ let $g_{c,J}$ be $f_c$ with its values flipped on $\bigcup_{i\in J}C_i$. The system **corrupts** $\mathcal P$ (Definition 35) if every $f_c\in\mathcal P$ and, for every non-empty $J$ and every $c$,
--
--   $$d(g_{c,J},\mathcal P)\ge0.2\sum_{i\in J}\frac{|B_i|}{2^n}.$$
--
--   This is the framework from which the paper derives its symmetry and monotonicity space lower bounds (Theorem 36).
--
--   **Formalization Note** The background map is a total function on the cube; only its values off $\bigcup_iB_i$ are used.
-- source:
--   Canonne, Chen, Pires, Pitassi, Servedio, The Space Complexity of Property Testing, manuscript of November 2, 2026 (sha256 65850aa6…), Definitions 34–35, p.31 (PDF 33)

import Mathlib
import Definitions.Def_SpacePropTest_Cube

set_option autoImplicit false

namespace SpacePropTest

noncomputable section

open Classical

/-- **Block systems and corruptible properties** (C. Canonne, X. Chen, W. Pires, T. Pitassi,
R. A. Servedio, *The Space Complexity of Property Testing*, manuscript of November 2, 2026,
sha256 65850aa6…; Definitions 34–35, p.31 (PDF 33)).

An `(I, β)`-block system, for a non-empty finite index type `I` and `0 < β ≤ 1`: pairwise disjoint
blocks `B i ⊆ {0,1}ⁿ` with `∑_i |B_i| ≥ β·2ⁿ` and `|B_i| ≤ 2ⁿ/|I|`; sub-blocks `C i ⊆ B i`; and a
background map `bg`.

**Formalization Note.** The background map is a total function on the cube; only its values off
`⋃_i B_i` are ever used (Definition 34(c) defines it on `{0,1}ⁿ ∖ ⋃_i B_i`). -/
structure BlockSystem (n : ℕ) (I : Type*) [Fintype I] (β : ℝ) where
  /-- The blocks `B_i`. -/
  B : I → Finset (Cube n)
  /-- The sub-blocks `C_i`. -/
  C : I → Finset (Cube n)
  /-- The background map `b`. -/
  bg : Cube n → Bool
  index_nonempty : Nonempty I
  β_pos : 0 < β
  β_le_one : β ≤ 1
  disjoint : Pairwise (fun i j => Disjoint (B i) (B j))
  mass : β * 2 ^ n ≤ ∑ i, ((B i).card : ℝ)
  small : ∀ i, ((B i).card : ℝ) ≤ 2 ^ n / Fintype.card I
  sub : ∀ i, C i ⊆ B i

namespace BlockSystem

variable {n : ℕ} {I : Type*} [Fintype I] {β : ℝ}

/-- `f_c(x) = c_i` if `x ∈ B_i` for some `i`, and `b(x)` otherwise (Definition 35 (1.)). The
blocks are disjoint, so the index `i` is unique. -/
def fc (S : BlockSystem n I β) (c : I → Bool) (x : Cube n) : Bool :=
  if h : ∃ i, x ∈ S.B i then c h.choose else S.bg x

/-- `g_{c,J}`: `f_c` flipped on `⋃_{i∈J} C_i` (Definition 35 (2.)). -/
def gcJ (S : BlockSystem n I β) (c : I → Bool) (J : Finset I) (x : Cube n) : Bool :=
  if ∃ i ∈ J, x ∈ S.C i then !S.fc c x else S.fc c x

/-- The block system corrupts `P` (Definition 35): every `f_c` lies in `P`, and for every
non-empty `J ⊆ I` and every `c`, `d(g_{c,J}, P) ≥ 0.2 ∑_{i∈J} |B_i|/2ⁿ`. -/
def Corrupts (S : BlockSystem n I β) (P : Set (BoolFn n)) : Prop :=
  (∀ c : I → Bool, S.fc c ∈ P) ∧
  ∀ J : Finset I, J.Nonempty → ∀ c : I → Bool,
    IsFar P (S.gcJ c J) (0.2 * ∑ i ∈ J, ((S.B i).card : ℝ) / 2 ^ n)

end BlockSystem

end

end SpacePropTest


