-- Prove2me | Definitions.Def_DetCCHard_CodeSym
-- name    : DetCCHard_CodeSym
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:35:31.306211+00:00
-- url     : https://prove2.me/theorems/fdf301a3-cc7b-4ab0-9ba4-8fcc7096f987
-- title:
--   Output alphabet, explicit table encoding and machine runs
-- statement:
--   The reductions of the mission are string functions over a four-letter alphabet $\{0, 1, \texttt{endNum}, \texttt{endBlock}\}$. A natural number is written in binary (least significant digit first, no leading zeros) followed by $\texttt{endNum}$; a block of numbers is followed by $\texttt{endBlock}$.
--
--   The **explicit encoding of a total Boolean table** $M : [a] \times [b] \to \{0,1\}$ is the header block $[a, b]$ followed by one block per row listing its $b$ entries; the **encoding of a table with a threshold** $B \in \mathbb N$ has header $[a, b, B]$. Both are injective (checked in the verification file), so the output string determines the table and the threshold.
--
--   A Turing machine (Cook's one-tape model, published `CookPvsNP.TM`) **runs on input $x$ within $T$ steps with output $y$** if it halts within $T$ steps and its output, the tape from the head rightwards with trailing blanks removed, is $y$.
--
--   **Formalization Note** The paper fixes no alphabet or format; any injective explicit encoding with polynomially related length serves. The output convention is that of the published `CookPvsNP.PolyTimeComputable`.
-- source:
--   Gaspers–He–Mackenzie, NP-Hardness and Additive Inapproximability of Deterministic Communication Complexity, arXiv:2508.05597 (held version, sha256 ad552d13…), Theorem 1.1, p.3 (explicit table and integer B); Theorem 8.4, p.36 (running time and output length)

import Mathlib
import Definitions.Def_CookPvsNP_defs

namespace DetCCHard

/-- The four-letter **output alphabet** of the reductions (Gaspers–He–Mackenzie,
arXiv:2508.05597, held version sha256 ad552d13…a4a03; the paper fixes no alphabet): the binary
digits `0`, `1`, a separator ending a number, and a separator ending a block of numbers. -/
inductive CodeSym where
  | zero
  | one
  | endNum
  | endBlock
  deriving DecidableEq

instance : Fintype CodeSym where
  elems := {CodeSym.zero, CodeSym.one, CodeSym.endNum, CodeSym.endBlock}
  complete := by intro x; cases x <;> simp

/-- The binary digits of a natural number, least significant first, without leading zeros
(`0` has no digits). -/
def natBits (n : ℕ) : List CodeSym :=
  (Nat.digits 2 n).map fun d => if d = 1 then CodeSym.one else CodeSym.zero

/-- A list of natural numbers, each written in binary and followed by `endNum`. -/
def encodeNats (l : List ℕ) : List CodeSym :=
  (l.map fun n => natBits n ++ [CodeSym.endNum]).flatten

/-- A list of blocks of natural numbers, each block followed by `endBlock`. -/
def encodeBlocks (ls : List (List ℕ)) : List CodeSym :=
  (ls.map fun l => encodeNats l ++ [CodeSym.endBlock]).flatten

/-- The 0/1 entries of row `i` of a table. -/
def tableRow {a b : ℕ} (M : Fin a → Fin b → Bool) (i : Fin a) : List ℕ :=
  List.ofFn fun j => if M i j then 1 else 0

/-- The **explicit encoding of a total Boolean table** `M : [a] × [b] → {0, 1}`: a header block
`[a, b]`, then one block per row listing its `b` entries. -/
def encodeTable {a b : ℕ} (M : Fin a → Fin b → Bool) : List CodeSym :=
  encodeBlocks ([a, b] :: List.ofFn (tableRow M))

/-- The **explicit encoding of a table together with a threshold** `B ∈ ℕ` (Theorem 1.1, p.3: the
reduction outputs "an explicit total Boolean table `M` and an integer `B`"): a header block
`[a, b, B]` (with `B` in binary), then one block per row listing its `b` entries.

**Formalization Note** The encoding is injective in `(a, b, M, B)`; this is checked in the
mission's verification file. -/
def encodeTableNat {a b : ℕ} (M : Fin a → Fin b → Bool) (B : ℕ) : List CodeSym :=
  encodeBlocks ([a, b, B] :: List.ofFn (tableRow M))

/-- A Turing machine `M` (Cook's one-tape model, published `CookPvsNP.TM`), with input and output
alphabets embedded by `ι₁`, `ι₂` into its tape alphabet, **halts on input `x` within `T` steps with
output `y`** (the output convention of `CookPvsNP.PolyTimeComputable`: the tape from the head
rightwards, trailing blanks removed). -/
def RunsWithin {Sym₁ Sym₂ Γ : Type} (M : CookPvsNP.TM Γ) (ι₁ : Sym₁ ↪ Γ) (ι₂ : Sym₂ ↪ Γ)
    (x : List Sym₁) (T : ℕ) (y : List Sym₂) : Prop :=
  M.HaltsWithin T (x.map ι₁) ∧ M.output (M.run T (M.init (x.map ι₁))) = y.map (some ∘ ι₂)

end DetCCHard


