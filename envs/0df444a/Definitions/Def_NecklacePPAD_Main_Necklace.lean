-- Prove2me | Definitions.Def_NecklacePPAD_Main_Necklace
-- name    : NecklacePPAD_Main_Necklace
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:04:54.651386+00:00
-- url     : https://prove2.me/theorems/a06499a6-b599-41ec-ae10-cdc74f2a6ce1
-- title:
--   Necklaces, labellings, cuts, balanced labellings and splits (Definition 3.1)
-- statement:
--   A **necklace** is a word $a=a_1\cdots a_N$ over the colours $C=\{0,\dots,n-1\}$ (`Fin n`); it is a necklace in the sense of Definition 3.1 when every colour $c$ occurs an even number $2b_c$ of times (`IsNecklace`; `half c` $=b_c$). A **labelling** is $\ell:[N]\to\{0,1\}$, encoded as `Fin N → Bool` with `true` for label 1; positions are 0-based in Lean (the page's position $q$ is Lean's $q-1$). Its **cuts** are the positions $q$ with $q+1<N$ and $\ell(q)\neq\ell(q+1)$ (a cut between $q$ and $q+1$). It is **balanced** if for every colour $c$ exactly $b_c$ of the positions of colour $c$ have label 1, written $2\cdot\#\{q: a_q=c,\ \ell(q)=1\}=\#\{q: a_q=c\}$. A **split** is a balanced labelling with at most $n$ cuts.
-- source:
--   Zeng, Wang, Cao, Dai, Wang, Necklace Splitting with Ten Beads per Colour is PPAD-Hard (STOC 2027 submission, sha256 d5b5449c…41ac), Definition 3.1, p. 5 (PDF 7)

import Mathlib

set_option autoImplicit false

namespace NecklacePPAD.Main

/-- **A necklace** (Zeng, Wang, Cao, Dai, Wang, *Necklace Splitting with Ten Beads per Colour is
PPAD-Hard*, STOC 2027 submission, sha256 d5b5449c…, Definition 3.1, p. 5 (PDF 7)): a word
`a = a₁ ⋯ a_N` over the set `C = Fin n` of `n` colours.

**Formalization Note** The colours are `Fin n`; positions are 0-based (the paper's position `q` is
the Lean position `q − 1`). The parity condition "every colour occurs an even number `2b_c` of
times" is the separate predicate `Necklace.IsNecklace`. -/
structure Necklace where
  n : ℕ
  beads : List (Fin n)

namespace Necklace

/-- The number `N` of beads (positions) of a necklace. -/
abbrev N (a : Necklace) : ℕ := a.beads.length

/-- Every colour `c` occurs an even number `2b_c` of times (Definition 3.1). -/
def IsNecklace (a : Necklace) : Prop := ∀ c : Fin a.n, Even (a.beads.count c)

/-- `b_c`: half the number of occurrences of colour `c`. -/
def half (a : Necklace) (c : Fin a.n) : ℕ := a.beads.count c / 2

/-- The label of the (0-based) position `q` under a labelling `ℓ : [N] → {0, 1}` (encoded as
`Fin N → Bool`, `true` = label 1); positions `q ≥ N` read `false` and are never used. -/
def lab (a : Necklace) (ℓ : Fin a.N → Bool) (q : ℕ) : Bool :=
  if h : q < a.N then ℓ ⟨q, h⟩ else false

/-- The **cuts** of a labelling (Definition 3.1): the (0-based) positions `q` with `q + 1 < N` and
`ℓ(q) ≠ ℓ(q + 1)` — a cut between positions `q` and `q + 1`. -/
def cuts (a : Necklace) (ℓ : Fin a.N → Bool) : Finset ℕ :=
  (Finset.range (a.N - 1)).filter (fun q => a.lab ℓ q ≠ a.lab ℓ (q + 1))

/-- A labelling is **balanced** (Definition 3.1) if for every colour `c` exactly `b_c` of the
`2b_c` positions of colour `c` have label 1; written `2 · #{q : a_q = c, ℓ(q) = 1} = #{q : a_q = c}`. -/
def Balanced (a : Necklace) (ℓ : Fin a.N → Bool) : Prop :=
  ∀ c : Fin a.n,
    2 * ((Finset.univ : Finset (Fin a.N)).filter (fun q => a.beads.get q = c ∧ ℓ q = true)).card =
      a.beads.count c

/-- A **split** (Definition 3.1): a balanced labelling with at most `n` cuts, `n` the number of
colours. -/
def IsSplit (a : Necklace) (ℓ : Fin a.N → Bool) : Prop :=
  a.Balanced ℓ ∧ (a.cuts ℓ).card ≤ a.n

end Necklace

end NecklacePPAD.Main


