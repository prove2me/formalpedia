-- Prove2me | Definitions.Def_CentralStrQ_PLCPBitvector
-- name    : CentralStrQ_PLCPBitvector
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:21:34.076704+00:00
-- url     : https://prove2.me/theorems/40511d6d-536e-4358-9812-a031031c58fd
-- title:
--   Selection queries and the PLCP bitvector $B^{\mathrm{PLCP}}_T$
-- statement:
--   For a string $S$ of length $m$, a symbol $a$ and $r\ge 1$, $\mathrm{select}_S(r,a)$ is the $r$-th smallest position $i\in[1\,.\,.\,m]$ with $S[i]=a$, and $\infty$ if there are fewer than $r$ such positions (Definition 3.27).
--
--   For a string $T\in\Sigma^n$, the **PLCP bitvector** $B^{\mathrm{PLCP}}_T[1\,.\,.\,2n]$ has a one at position $2j+\mathrm{PLCP}_T[j]$ for every $j\in[1\,.\,.\,n]$ and a zero at every other position (Definition 9.1, due to Sadakane). For a bitvector $B$, $\mathrm{ones}(B)$ denotes the set of positions $x$ with $B[x]=1$.
--
--   By Lemma 9.4 the $n$ marks are distinct and lie in $[1\,.\,.\,2n]$, so $\mathrm{PLCP}_T[j]=\mathrm{select}_{B}(j,1)-2j$: the bitvector stores the whole PLCP array in $2n$ bits. Its construction is the goal of the mission. For example, $T=aab$ has $\mathrm{PLCP}=(0,1,0)$ and $B^{\mathrm{PLCP}}_T=010011$.
--
--   **Formalization Note** Bitvectors are lists of booleans (true is one). $\mathrm{select}$ takes values in $\mathbb N\cup\{\infty\}$; $r=0$ also gives $\infty$.
-- source:
--   Kempa–Kociumaka, A Complete Characterization of Central String Queries in Compact Space, STOC 2027 submission (manuscript sha256 dea2f74f66f1bd686c8e3c6d4e11f36643253c3c86a04fc5faa1c3ac1c96f346), Definition 3.27, p.18 (PDF p.19); Definition 9.1, p.163 (PDF p.164)

import Mathlib
import Definitions.Def_CentralStrQ_Strings

set_option autoImplicit false

namespace CentralStrQ

/-!
# Selection queries and the PLCP bitvector (Definitions 3.27 and 9.1)

Kempa–Kociumaka, *A Complete Characterization of Central String Queries in Compact Space*,
STOC 2027 submission (manuscript sha256 dea2f74f…c96f346): Definition 3.27, p.18 (PDF p.19);
Definition 9.1, p.163 (PDF p.164): "For a string T ∈ Σⁿ, the PLCP bitvector B^PLCP_T[1..2n] has
a one at position 2j + PLCP_T[j] for every j ∈ [1..n] and a zero at every remaining position."

**Formalization Note.** A bitvector is a `List Bool` (`true` = one), positions 1-based. `select`
returns a value in `ℕ∞`, with `⊤` for the paper's `∞`; `r = 0` (outside the paper's `r ∈ ℤ≥1`)
also gives `⊤`. `plcpBits T` is the list of length `2n` whose entry at 1-based position `x` is
`true` iff `x = 2j + PLCP_T[j]` for some `j ∈ [1..n]`.
-/

variable {α β : Type}

/-- The 1-based positions `i ∈ [1..|S|]` with `S[i] = a`, in increasing order. -/
def occurrences [DecidableEq β] (S : List β) (a : β) : List ℕ :=
  (List.range' 1 S.length).filter fun i => S[i - 1]? = some a

/-- `select_S(r, a)`: the `r`-th smallest `i ∈ [1..|S|]` with `S[i] = a`, or `∞` if there are
fewer than `r` such positions (Definition 3.27). -/
def select [DecidableEq β] (S : List β) (r : ℕ) (a : β) : ℕ∞ :=
  if h : 1 ≤ r ∧ r ≤ (occurrences S a).length then
    (((occurrences S a)[r - 1]'(by omega) : ℕ) : ℕ∞)
  else ⊤

/-- The set of 1-based positions of the ones of a bitvector. -/
def onesOf (B : List Bool) : Set ℕ := {x | 1 ≤ x ∧ B[x - 1]? = some true}

/-- The PLCP bitvector `B^PLCP_T[1..2n]` (Definition 9.1). -/
def plcpBits [LinearOrder α] (T : List α) : List Bool :=
  (List.range' 1 (2 * T.length)).map fun x =>
    (List.range' 1 T.length).any fun j => 2 * j + PLCP T j == x

end CentralStrQ


