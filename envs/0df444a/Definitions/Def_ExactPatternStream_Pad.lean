-- Prove2me | Definitions.Def_ExactPatternStream_Pad
-- name    : ExactPatternStream_Pad
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:03:05.066992+00:00
-- url     : https://prove2.me/theorems/35147765-1b5e-4937-a60d-222650ba0618
-- title:
--   Definitions 4.3, 4.5, 4.8 — Pad, $\rho_{S\to S'}$, and Group
-- statement:
--   An annotated string (Definition 4.1) is a pair $(S,A)$ with $A\in\{0,1\}^{|S|+1}$; the last bit annotates the virtual final position.
--
--   **Pad** (Definition 4.3). Given a trigger $u^c\circ v$ with $u\ne v$, $c>0$, and a fresh symbol $\#$, let $x_1<\dots<x_k$ be the active trigger occurrences, i.e. the $x\in[0\,.\,.\,s-c)$ with $S[x\,.\,.\,x+c]=u^c\circ v$ and $A[x]=1$. They factor $S=\big(\bigodot_{i<k}(X_i\circ u^c\circ v)\big)\circ X_k$. With $Y_i=X_i\circ u^c\circ v\circ\#^{t_i}$ and $t_i=(1-|X_i|)\bmod(c+2)$, the output is
--   $$S'=\Big(\bigodot_{i<k}Y_i\Big)\circ X_k,\qquad A'=0\circ\bigodot_{i<k}\big(0^{|Y_i|-1}\circ1\big)\circ0^{|X_k|}.$$
--   Definition 4.5: $\rho_{S\to S'}$ sends each position of $S$ to the position of its copy in $S'$, and $|S|$ to $|S'|$.
--
--   **Group** (Definition 4.8). For $f$ on $(c+2)$-tuples, $S''$ applies $f$ to each full block of $S'$ of length $c+2$, $A''$ keeps $A'$ at the multiples of $c+2$ up to $\lfloor s'/(c+2)\rfloor$ inclusive, and the residual $R''$ is the rest of $S'$.
--
--   Padding makes each active trigger end at a group boundary, which synchronizes pattern and text parses.
--
--   **Formalization Note** $t_i$ is an integer residue, computed in `ℤ`. The case $k=0$ of the definition is what the recursion returns on an empty list of occurrences. `padRho` adds to $j$ the markers inserted before it.
-- source:
--   Gawrychowski, Janczewski, Jin, Nelson, An Improved Streaming Algorithm for Exact Pattern Matching (preprint, STOC 2027 submission, sha256 351218cb…), §4.1–§4.2, pp.6–8 (PDF 7–9), Definitions 4.1, 4.3, 4.5, 4.8

import Mathlib
import Definitions.Def_ExactPatternStream_Strings

namespace ExactPatternStream

/-! # Padding and grouping

Gawrychowski, Janczewski, Jin, Nelson (preprint, sha256 351218cb…), §4.1–§4.2, pp.6–8 (PDF 7–9),
Definitions 4.1, 4.3, 4.5, 4.8.

**Formalization Note.** An annotated string (Definition 4.1) is a pair `S : List α`, `A : List Bool` with
`|A| = |S| + 1`; `A.getD x false` reads a bit. The trigger `u^c ◦ v` is the triple `u, c, v`, and the
paper's requirements `u ≠ v`, `c > 0`, `# ∉ Σ` are hypotheses of the statements that use `pad`. In
`padCount`, `t = (1 - |X|) mod (c + 2)` is the integer residue, computed in `ℤ` (`%` is the Euclidean one).
The case `k = 0` of Definition 4.3 returns `(S, 0^{s+1})`, which is what the recursion gives on an empty
list of occurrences. -/

variable {α : Type*}

/-- Active trigger occurrences, Definition 4.3:
`U = {x ∈ [0 . . s - c) : S[x . . x + c] = u^c ◦ v ∧ A[x] = 1}`, listed increasingly. -/
def trigOcc [DecidableEq α] (S : List α) (A : List Bool) (u : α) (c : ℕ) (v : α) : List ℕ :=
  (List.range (S.length - c)).filter fun x =>
    slice S x (x + c + 1) = List.replicate c u ++ [v] ∧ A.getD x false = true

/-- `t = (1 - ℓ) mod (c + 2)`, the number of markers after a piece `X` of length `ℓ`. -/
def padCount (c ℓ : ℕ) : ℕ := ((1 - (ℓ : ℤ)) % ((c : ℤ) + 2)).toNat

/-- The factorization of Definition 4.3, from position `prev` on and the remaining occurrences:
returns `Y_i ◦ ⋯ ◦ Y_{k-1} ◦ X_k` and the annotations after the initial `0`,
`⨀ (0^{|Y_j| - 1} ◦ 1) ◦ 0^{|X_k|}`. -/
def padLoop (S : List α) (u : α) (c : ℕ) (v hash : α) : ℕ → List ℕ → List α × List Bool
  | prev, [] =>
      let X := slice S prev S.length
      (X, List.replicate X.length false)
  | prev, x :: xs =>
      let X := slice S prev x
      let Y := X ++ List.replicate c u ++ [v] ++ List.replicate (padCount c X.length) hash
      let rest := padLoop S u c v hash (x + c + 1) xs
      (Y ++ rest.1, List.replicate (Y.length - 1) false ++ [true] ++ rest.2)

/-- Definition 4.3: `Pad(S, A, u^c ◦ v, #)` returns the annotated string `(S', A')`. -/
def pad [DecidableEq α] (S : List α) (A : List Bool) (u : α) (c : ℕ) (v hash : α) :
    List α × List Bool :=
  let r := padLoop S u c v hash 0 (trigOcc S A u c v)
  (r.1, false :: r.2)

/-- The markers inserted before position `j`, from position `prev` on: the sum of `t_i` over the
occurrences `x_i` with `x_i + c + 1 ≤ j`. -/
def padShift (c j : ℕ) : ℕ → List ℕ → ℕ
  | _, [] => 0
  | prev, x :: xs =>
      if x + c + 1 ≤ j then padCount c (x - prev) + padShift c j (x + c + 1) xs else 0

/-- Definition 4.5: `ρ_{S→S'}` sends position `j` of `S` to the position of its copy in `S'`, and `s`
to `|S'|`. -/
def padRho [DecidableEq α] (S : List α) (A : List Bool) (u : α) (c : ℕ) (v : α) (j : ℕ) : ℕ :=
  j + padShift c j 0 (trigOcc S A u c v)

/-- Definition 4.8: `Group(S', A', c, f)` returns `S''`, `A''`, and the residual string `R''`, for groups
of size `c + 2`. The group function is applied to the `α`-entries of `S'` with no assumption on `β`. -/
def group {β : Type*} (S' : List α) (A' : List Bool) (c : ℕ) (f : List α → β) :
    List β × List Bool × List α :=
  let q := S'.length / (c + 2)
  ((List.range q).map (fun i => f (slice S' (i * (c + 2)) ((i + 1) * (c + 2)))),
   (List.range (q + 1)).map (fun i => A'.getD (i * (c + 2)) false),
   slice S' (q * (c + 2)) S'.length)

end ExactPatternStream


