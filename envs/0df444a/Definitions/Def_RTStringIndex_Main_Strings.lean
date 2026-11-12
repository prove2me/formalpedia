-- Prove2me | Definitions.Def_RTStringIndex_Main_Strings
-- name    : RTStringIndex_Main_Strings
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T06:40:00.753285+00:00
-- url     : https://prove2.me/theorems/9355daa3-afa2-47cb-81f9-7a05d6099ab6
-- title:
--   Strings, occurrences, longest common prefixes, and the prepended suffixes $S_k$
-- statement:
--   Letters are natural numbers. For a pattern $P$ and a text $T$, the **occurrences** of $P$ in $T$ are the $0$-based positions
--   $$\mathrm{occ}(P,T)=\{\,i\in\{0,\dots,|T|\} : P \text{ is a prefix of } T[i..]\,\},$$
--   so the empty pattern occurs at all $|T|+1$ positions and a pattern longer than $T$ does not occur.
--
--   $\mathrm{LCP}(x,y)$ is the longest common prefix of two strings; for a finite set $Y$, $|\mathrm{LCP}(X,Y)|$ is the length of the longest common prefix of $X$ with a string of $Y$ ($0$ if $Y$ is empty).
--
--   Inside the suffix tree, strings are over $\mathbb N\cup\{\$\}$, where the terminator $\$$ is larger than every letter, and $x\$$ denotes $x$ followed by $\$$.
--
--   For the block $A=a_1\cdots a_d$ and the main text $S_{\mathrm{init}}$, the prepended suffixes are
--   $$S_k=a_{d-k+1}\cdots a_d\,S_{\mathrm{init}}\quad(0\le k\le d),\qquad S_0=S_{\mathrm{init}},$$
--   and $s_k=a_{d-k+1}\cdots a_d$ is the length-$k$ prefix of $S_k$.
--
--   These are the string notions used by Theorem 1 and by the lemmas of Sections 5 and 7.
-- source:
--   Gregory Kucherov, Yakov Nekrich, Real-Time String Indexing in Optimal Time, STOC 2027 submission #1543 (October 2026), Theorem 1, p. 2; §2, p. 2; §5, pp. 8–10 (S_init, s_i, S_i, LCP); §7, p. 18 (LCP(X, Y)); PDF SHA256 71c79bb80cc4d3fcb625decd72e0891e6b6178c09cb94001a67c6abfb63052f0

import Mathlib

set_option autoImplicit false

namespace RTStringIndex.Main

/-! # Strings, occurrences, longest common prefixes and the prepended suffixes

Gregory Kucherov, Yakov Nekrich, *Real-Time String Indexing in Optimal Time*, STOC 2027
submission #1543 (October 2026). Theorem 1, p.2 ("report all occ occurrences of P in the current
text T"); §2, p.2 (suffix trees, `label`, `strdepth`); §5, pp.8–10 (`S_init`, `s_i`, `S_i`,
`LCP(x, y)`); §7, p.18 (`LCP(X, Y)` for a set `Y`).

**Formalization Note.** Letters are natural numbers (an integer alphabet of arbitrary size).
Positions are `0`-based. Inside the suffix tree, strings are over `Chr = WithTop ℕ`: a letter `a`
is `(a : Chr)` and the terminator `$` is `⊤`, larger than every letter (the convention of §8,
p.22). `term x` is `x$`. -/

/-- The alphabet of the suffix tree: the letters `ℕ` and the terminator `$ = ⊤`. -/
abbrev Chr := WithTop ℕ

/-- `x$`: the letters of `x` followed by the terminator. -/
def term (x : List ℕ) : List Chr := x.map (fun a => (a : Chr)) ++ [⊤]

/-- The occurrences of the pattern `P` in the text `T`: the `0`-based starting positions
`i ∈ {0, …, |T|}` such that `P` is a prefix of `T[i..]`. -/
def occ (P T : List ℕ) : Finset ℕ :=
  (Finset.range (T.length + 1)).filter (fun i => P <+: T.drop i)

/-- The longest common prefix of two strings. -/
def lcpStr {α : Type} [DecidableEq α] : List α → List α → List α
  | a :: x, b :: y => if a = b then a :: lcpStr x y else []
  | _, _ => []

/-- `|LCP(x, y)|`. -/
def lcpLen {α : Type} [DecidableEq α] (x y : List α) : ℕ := (lcpStr x y).length

/-- `|LCP(X, Y)|` for a finite set `Y` of strings (§7, p.18): the length of the longest among
the common prefixes of `X` and the strings of `Y` (`0` when `Y` is empty). -/
def lcpSet {α : Type} [DecidableEq α] (X : List α) (Y : Finset (List α)) : ℕ :=
  Y.sup (lcpLen X)

/-- The prepended suffixes of §5 (p.8–9): for the block `A = a_1 ⋯ a_d` and the main text
`X = S_init`, `Sk A X k = a_{d−k+1} ⋯ a_d · S_init` (so `Sk A X 0 = S_init`, and for `k ≥ 1` its
length-`k` prefix is `s_k`). -/
def Sk (A X : List ℕ) (k : ℕ) : List ℕ := A.drop (A.length - k) ++ X

/-- `s_k = a_{d−k+1} ⋯ a_d`, as a string over `Chr`. -/
def sk (A : List ℕ) (k : ℕ) : List Chr := (A.drop (A.length - k)).map (fun a => (a : Chr))

/-- The nonempty suffixes `T[i..]` of `T` (`0 ≤ i < |T|`), as plain strings. -/
def suffixes (T : List ℕ) : Finset (List ℕ) :=
  (Finset.range T.length).image (fun i => T.drop i)

end RTStringIndex.Main


