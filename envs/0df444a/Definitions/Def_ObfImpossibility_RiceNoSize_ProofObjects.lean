-- Prove2me | Definitions.Def_ObfImpossibility_RiceNoSize_ProofObjects
-- name    : ObfImpossibility_RiceNoSize_ProofObjects
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T10:28:11.33098+00:00
-- url     : https://prove2.me/theorems/10bf5724-b4e3-4b68-84e6-3d7185344431
-- title:
--   $\mathrm{KC}(f)$, the promise problem $\Pi=(\Pi_Y,\Pi_N)$, the machine $Z$ and the function $N_{n,r}$ of the proof of Theorem A.4 (p. A:42)
-- statement:
--   This file defines the objects used in the proof of Theorem A.4 of Barak et al., in the step-counted Turing-machine model of the mission's setting file.
--
--   1. **Description complexity of a function.** For a partial function $f:\mathbb N\rightharpoonup\mathbb N$,
--   $$\mathrm{KC}(f)=\min\{\,|M| : [M]=f\,\},$$
--   the size of the smallest machine computing $f$. If no machine computes $f$, the value is $0$; this never happens for $f=[M]$.
--   2. **Always halts.** $M$ always halts if $[M](x)$ is defined for every $x$.
--   3. **The promise problem.**
--   $$\Pi_Y=\{M : M \text{ always halts and } \exists x<\mathrm{KC}([M]) \text{ with } [M](x)=1\},\qquad \Pi_N=\{M : M \text{ always halts and } [M](x)=0 \text{ for all } x\}.$$
--   4. **The machine $Z$.** $Z$ has a single state: reading $1$ it moves right, reading the blank it halts. It reads its unary input and then returns $0$.
--   5. **The function $N_{n,r}$.** For $n,r\in\mathbb N$,
--   $$N_{n,r}(x)=\begin{cases}0 & x\le n,\\ 1 & x=n+1,\\ r & x\ge n+2.\end{cases}$$
--
--   The proof of Theorem A.4 shows that $\Pi$ is closed under $[\cdot]$ and decidable, that every oracle machine accepting $Z$ (which lies in $\Pi_N$) also accepts a suitable machine computing $N_{n,r}$, and that such machines lie in $\Pi_Y$.
--
--   **Formalization Note** $\mathrm{KC}$ is `sInf` of a set of natural numbers, which is $0$ on the empty set. Inputs are unary, so the paper's $|x|$ is $x$ itself, and the paper's string $r$ is a natural number (an output written in unary).
-- source:
--   Barak et al., On the (Im)possibility of Obfuscating Programs, J. ACM 59(2) (2012), author's copy, p. A:42, proof of Theorem A.4 (KC, Π_Y, Π_N, Z, N_{n,r})

import Mathlib
import Definitions.Def_ObfImpossibility_RiceNoSize_Setting

namespace ObfImpossibility.RiceNoSize

open Turing

/-- `KC(f)` (p. A:42): the description length of the smallest machine computing the partial
function `f`, i.e. the least size of a machine `M` with `[M] = f`. If no machine computes `f`
the infimum of the empty set is `0` (Mathlib's convention); this case never occurs for
`f = [M]`. -/
noncomputable def KC (f : ℕ →. ℕ) : ℕ :=
  sInf {s : ℕ | ∃ M : Machine, fn M = f ∧ size M = s}

/-- `M` always halts: `[M]` is total. -/
def AlwaysHalts (M : Machine) : Prop := ∀ x : ℕ, (fn M x).Dom

/-- `Π_Y` of the proof of Theorem A.4 (p. A:42):
`{M : M always halts and ∃ x < KC([M]) s.t. [M](x) = 1}`. -/
def PiY : Set Machine :=
  {M | AlwaysHalts M ∧ ∃ x < KC (fn M), fn M x = Part.some 1}

/-- `Π_N` of the proof of Theorem A.4 (p. A:42): `{M : M always halts and ∀ x M(x) = 0}`. -/
def PiN : Set Machine :=
  {M | AlwaysHalts M ∧ ∀ x : ℕ, fn M x = Part.some 0}

/-- The machine `Z` that reads its input and then returns `0` (p. A:42): one state; reading
`1` it moves right, reading the blank `0` it halts (the head is then on a blank, so the
output is `0`). -/
def Z : Machine where
  q := 0
  δ := fun _ a => if a then some (0, TM0.Stmt.move Dir.right) else none

/-- The function `N_{n,r}` of p. A:42: `0` for `|x| ≤ n`, `1` for `|x| = n + 1`, and `r` for
`|x| ≥ n + 2` (inputs are unary, so `|x| = x`; the string `r` is a natural number). -/
def Nfun (n r : ℕ) : ℕ →. ℕ := fun x =>
  Part.some (if x ≤ n then 0 else if x = n + 1 then 1 else r)

end ObfImpossibility.RiceNoSize


