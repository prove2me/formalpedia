-- Prove2me | Definitions.Def_ConantTerry_Orders_binary_words
-- name    : ConantTerry_Orders_binary_words
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T06:31:06.78409+00:00
-- url     : https://prove2.me/theorems/4e75a97b-6f18-4892-b4a6-25c2c0359fb7
-- title:
--   Finite binary words and their height truncations
-- statement:
--   A binary word is a finite sequence of bits, with $0$ and $1$ represented by `false` and `true`. For an integer $t\ge0$, write
--   $$
--   B_{<t}=\{\sigma:|\sigma|<t\},\qquad
--   B_{\le t}=\{\sigma:|\sigma|\le t\},\qquad
--   B_t=\{\sigma:|\sigma|=t\}.
--   $$
--   The empty word has length zero and is the unique element of $B_0$. Concatenation is list concatenation; $\sigma\unlhd\tau$ means that $\tau=\sigma\mathbin{{}^\frown}\mu$ for some word $\mu$. The module also provides the canonical inclusions of $B_{<t}$ and $B_t$ into $B_{\le t}$.
--
--   These types provide a common indexing layer for the source's trees, embeddings and extraction predicates. They impose no constraints on the labels assigned to words.
-- source:
--   C. Terry, G. Conant, STOC 2027 submission #1299 (October 2026), p.2, §1.2, binary-word notation; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1299.pdf

import Mathlib

namespace ConantTerry.Orders

/-- Binary words below height `t`, including the empty word when `t > 0` (§1.2, p.2). -/
def WordsBelow (t : ℕ) := {σ : List Bool // σ.length < t}

/-- Binary words of length at most `t` (§1.2, p.2). -/
def WordsAtMost (t : ℕ) := {σ : List Bool // σ.length ≤ t}

/-- Binary words of length exactly `t` (§1.2, p.2). -/
def WordsAt (t : ℕ) := {σ : List Bool // σ.length = t}

/-- The canonical inclusion of internal nodes into the whole tree. -/
def nodeInclusion {t : ℕ} (σ : WordsBelow t) : WordsAtMost t :=
  ⟨σ.val, Nat.le_of_lt σ.property⟩

/-- The canonical inclusion of leaves into the whole tree. -/
def leafInclusion {t : ℕ} (η : WordsAt t) : WordsAtMost t :=
  ⟨η.val, Nat.le_of_eq η.property⟩

end ConantTerry.Orders


