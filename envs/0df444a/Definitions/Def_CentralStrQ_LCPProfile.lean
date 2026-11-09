-- Prove2me | Definitions.Def_CentralStrQ_LCPProfile
-- name    : CentralStrQ_LCPProfile
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:20:44.505674+00:00
-- url     : https://prove2.me/theorems/d5400718-f973-4752-8163-cb4fa1b56801
-- title:
--   Prefix special predecessors, LCP profiles and unary-encoded LCP profiles
-- statement:
--   Let $W[1\,.\,.\,m]$ be a sequence of strings and $A[1\,.\,.\,m)$ a sequence of nonnegative integers.
--
--   1. For $j\in[0\,.\,.\,m]$ and a string $X$, $\mathrm{prefix\text{-}pred}_W(j,X)$ is the largest $i\in[1\,.\,.\,j]$ such that $X$ is a prefix of $W[i]$, and $-\infty$ if there is none; $\mathrm{prefix\text{-}special\text{-}pred}_W(j,p)=\mathrm{prefix\text{-}pred}_W(j-1,W[j][1\,.\,.\,p])$ (Definition 3.30).
--   2. For $i\in[1\,.\,.\,m]$ and $p\in[0\,.\,.\,|W[i]|]$, with $h=\mathrm{prefix\text{-}special\text{-}pred}_W(i,p)$, the **LCP profile** is
--   $$
--   \mathrm{profile}_{A,W}(i)[p]=\begin{cases}\min A[h\,.\,.\,i) & \text{if } h\ne-\infty,\\ 0 & \text{otherwise}\end{cases}
--   $$
--   (Definition 8.1).
--   3. For $d\ge1$ and $q(p)=\mathrm{profile}_{A,W}(i)[p]$, if $|W[i]|\ge d$ the **unary encoding** is the binary string
--   $$
--   \mathrm{unary\text{-}profile}_{A,W,d}(i)=1\cdot\bigodot_{p=d+1}^{|W[i]|}0^{\,q(p-1)-q(p)}\,1,
--   $$
--   and it is empty if $|W[i]|<d$ (Definition 8.4).
--
--   If $A[h]$ is the LCP of consecutive strings of a sorted list and $W[h]$ is a label of the $h$-th string, the profile value is the LCP of the $i$-th string with its predecessor among the strings whose labels start with $W[i][1\,.\,.\,p]$ (Remark 8.2). Example 8.5: $W=(ab,aa,ab)$, $A=(4,2)$ give the profiles $(0,0,0)$, $(4,4,0)$, $(2,2,2)$ and, for $d=1$, the encodings $11$, $100001$, $11$.
--
--   **Formalization Note** Sequences are lists with 1-based access; $-\infty$ is the bottom element of $\mathbb N\cup\{-\infty\}$. The minimum over an empty range is set to $0$; it never occurs in the profile, where $h<i$. The exponent $q(p-1)-q(p)$ is natural subtraction, which Lemma 8.3 shows is never truncated.
-- source:
--   Kempa–Kociumaka, A Complete Characterization of Central String Queries in Compact Space, STOC 2027 submission (manuscript sha256 dea2f74f66f1bd686c8e3c6d4e11f36643253c3c86a04fc5faa1c3ac1c96f346), Definition 3.30, p.18 (PDF p.19); Definition 8.1, p.144 (PDF p.145); Definition 8.4, p.145 (PDF p.146)

import Mathlib

set_option autoImplicit false

namespace CentralStrQ

/-!
# Prefix special predecessors, LCP profiles and their unary encodings
(Definitions 3.30, 8.1 and 8.4)

Kempa–Kociumaka, *A Complete Characterization of Central String Queries in Compact Space*,
STOC 2027 submission (manuscript sha256 dea2f74f…c96f346): Definition 3.30, p.18 (PDF p.19);
Definition 8.1, p.144 (PDF p.145); Definition 8.4, p.145 (PDF p.146).

Definition 8.1 (rendered page; the text layer loses the second value): for `i ∈ [1..m]` and
`p ∈ [0..|W[i]|]`, `profile_{A,W}(i)[p] = min A[h..i)` if `h ≠ −∞` and `0` otherwise, where
`h = prefix-special-pred_W(i, p)`. Definition 8.4: if `|W[i]| ≥ d`,
`unary-profile_{A,W,d}(i) = 1 · ⨀_{p=d+1}^{|W[i]|} 0^{q(p−1)−q(p)} 1` with `q(p) = profile(i)[p]`;
otherwise it is the empty string.

**Formalization Note.** A sequence of strings `W[1..m]` is a `List (List α)` and `W[i]` is entry
`i − 1` (`strAt`); an integer sequence `A[1..m)` is a `List ℕ` and `A[h]` is entry `h − 1`
(`seqAt`). `−∞` is `⊥ : WithBot ℕ`. `rangeMin A h i = min A[h..i)` for `h < i`; it is `0` on an
empty range, which never occurs in `profile` (there `h ≤ i − 1`). In `unaryProfile` the exponent
`q(p−1) − q(p)` is natural-number subtraction; Lemma 8.3 shows it is never truncated. Bits are
`Bool`, `true` = 1.
-/

variable {α : Type}

/-- `W[i]` for a 1-based index `i` (the empty string out of range). -/
def strAt (W : List (List α)) (i : ℕ) : List α := W.getD (i - 1) []

/-- `A[h]` for a 1-based index `h` (`0` out of range). -/
def seqAt (A : List ℕ) (h : ℕ) : ℕ := A.getD (h - 1) 0

/-- `prefix-pred_W(j, X) = max{i ∈ [1..j] : X is a prefix of W[i]}`, or `−∞` if there is none
(Definition 3.30). -/
def prefixPred [DecidableEq α] (W : List (List α)) (j : ℕ) (X : List α) : WithBot ℕ :=
  ((Finset.Icc 1 j).filter fun i => X <+: strAt W i).max

/-- `prefix-special-pred_W(j, p) = prefix-pred_W(j − 1, W[j][1..p])` (Definition 3.30). -/
def prefixSpecialPred [DecidableEq α] (W : List (List α)) (j p : ℕ) : WithBot ℕ :=
  prefixPred W (j - 1) ((strAt W j).take p)

/-- `min A[h..i)` (`0` on an empty range). -/
def rangeMin (A : List ℕ) (h i : ℕ) : ℕ :=
  if hne : (Finset.Ico h i).Nonempty then (Finset.Ico h i).inf' hne (seqAt A) else 0

/-- The LCP profile value `profile_{A,W}(i)[p]` (Definition 8.1). -/
def profile [DecidableEq α] (A : List ℕ) (W : List (List α)) (i p : ℕ) : ℕ :=
  match prefixSpecialPred W i p with
  | ⊥ => 0
  | (h : ℕ) => rangeMin A h i

/-- The unary encoding `unary-profile_{A,W,d}(i)` (Definition 8.4). -/
def unaryProfile [DecidableEq α] (A : List ℕ) (W : List (List α)) (d i : ℕ) : List Bool :=
  if d ≤ (strAt W i).length then
    true :: (List.range' (d + 1) ((strAt W i).length - d)).flatMap fun p =>
      List.replicate (profile A W i (p - 1) - profile A W i p) false ++ [true]
  else []

end CentralStrQ


