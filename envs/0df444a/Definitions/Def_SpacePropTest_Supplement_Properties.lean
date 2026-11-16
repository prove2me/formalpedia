-- Prove2me | Definitions.Def_SpacePropTest_Supplement_Properties
-- name    : SpacePropTest_Supplement_Properties
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:42:13.337502+00:00
-- url     : https://prove2.me/theorems/7563ec90-7b0d-4fee-ba28-3af2135fd06a
-- title:
--   Symmetric, linear, $k$-junta and linear threshold functions on $\{0,1\}^n$ (Definitions 3–6)
-- statement:
--   For $x\in\{0,1\}^n$ let $|x|$ be its **Hamming weight**, the number of coordinates equal to $1$. For a Boolean function $f:\{0,1\}^n\to\{0,1\}$:
--
--   1. $f$ is **symmetric** (Definition 3) if $f(x)=f(y)$ whenever $|x|=|y|$; $\mathsf{Sym}_n$ is the set of symmetric functions.
--   2. $f$ is **linear** (a parity function, Definition 4) if there is $a\in\{0,1\}^n$ with $f(x)=a\cdot x=\sum_i a_ix_i \bmod 2$ for all $x$; $\mathsf{Lin}_n$ is the set of linear functions ($a=0$, the constant $0$, included).
--   3. $f$ is a **$k$-junta** (Definition 5) if there is $S\subseteq[n]$ with $|S|\le k$ such that $f(x)=f(y)$ whenever $x_S=y_S$; $\mathsf{Junta}_{n,k}$ is the set of $k$-juntas.
--   4. $f$ is a **linear threshold function** (LTF, Definition 6) if there are real numbers $w_0,w_1,\dots,w_n$ with
--   $$f(x)=1\iff w_0+w_1x_1+\dots+w_nx_n\ge0\qquad(x_i\in\{0,1\});$$
--   $\mathsf{LTF}_n$ is the set of LTFs.
--
--   These are four of the five properties whose space complexity of testing the paper determines (Table 1); monotonicity is defined in `SpacePropTest.Cube`.
--
--   **Formalization Note** Points of the cube are `Fin n → Bool` (`true` = 1), as in `SpacePropTest.Cube`. $\mathsf{Sym}_n$ is the published predicate `ShallowSym.IsSymmetric` (Hamming weight `ShallowSym.weight` on the same carrier `Fin n → Bool`), collected into a set. $a\cdot x=1$ is stated as “the number of $i$ with $a_i=x_i=1$ is odd”. `Junta n k` is defined for every $k\in\mathbb N$; the paper takes $k\in[n]$ and the statements restrict $k$. In the LTF sum, $x_i$ is the real number $1$ or $0$ (the 0/1 cube of Definition 6, not the $\pm1$ form of §5.5).
-- source:
--   Canonne, Chen, Pires, Pitassi, Servedio, The Space Complexity of Property Testing, manuscript of November 2, 2026 (sha256 65850aa6…), §3, p.14 (PDF 16) (Hamming weight, dot product over F₂); Definitions 3–6, pp.14–15 (PDF 16–17)

import Mathlib
import Definitions.Def_SpacePropTest_Cube
import Definitions.Def_ShallowSym_IsSymmetric

set_option autoImplicit false

namespace SpacePropTest.Supplement

open SpacePropTest

/-- **Symmetric functions** (C. Canonne, X. Chen, W. Pires, T. Pitassi, R. A. Servedio, *The Space
Complexity of Property Testing*, manuscript of November 2, 2026, sha256 65850aa6…; Definition 3,
p.14 (PDF 16)): `f(x) = f(y)` whenever `|x| = |y|`, where `|x|` is the Hamming weight (§3, p.14).

**Formalization Note.** This is the published predicate `ShallowSym.IsSymmetric` (Hamming weight
`ShallowSym.weight`, the number of `true` coordinates, on `ShallowSym.Cube n := Fin n → Bool`, the
same carrier as `SpacePropTest.Cube`), collected into a set. -/
def Sym (n : ℕ) : Set (BoolFn n) := {f | ShallowSym.IsSymmetric f}

/-- **Linear (parity) functions** (Definition 4, p.15 (PDF 17)): there is `a ∈ {0,1}ⁿ` with
`f(x) = a · x`, the dot product over `F₂` (§3, p.14).

**Formalization Note.** `a · x = 1` iff the number of coordinates `i` with `a_i = x_i = 1` is odd;
`a = 0` (the constant-`0` function) is included. -/
def Lin (n : ℕ) : Set (BoolFn n) :=
  {f | ∃ a : Cube n, ∀ x : Cube n,
    f x = true ↔ Odd (Finset.univ.filter (fun i => a i = true ∧ x i = true)).card}

/-- **k-juntas** (Definition 5, p.15 (PDF 17)): there is `S ⊆ [n]` with `|S| ≤ k` such that
`f(x) = f(y)` whenever `x_S = y_S`.

**Formalization Note.** The paper takes `k ∈ [n]`; the set is defined for every `k : ℕ` and the
statements that use it restrict `k`. -/
def Junta (n k : ℕ) : Set (BoolFn n) :=
  {f | ∃ S : Finset (Fin n), S.card ≤ k ∧ ∀ x y : Cube n, (∀ i ∈ S, x i = y i) → f x = f y}

/-- **Linear threshold functions** (Definition 6, p.15 (PDF 17)): there are real numbers
`w₀, w₁, …, w_n` with `f(x) = 1` iff `w₀ + w₁x₁ + … + w_nx_n ≥ 0`, where `x_i ∈ {0,1}`.

**Formalization Note.** The coordinate `x_i` enters the weighted sum as the real number `1` when
`x i = true` and `0` when `x i = false` (the 0/1 cube of Definition 6, not the `±1` form of §5.5). -/
def LTF (n : ℕ) : Set (BoolFn n) :=
  {f | ∃ (w₀ : ℝ) (w : Fin n → ℝ), ∀ x : Cube n,
    f x = true ↔ 0 ≤ w₀ + ∑ i, w i * (if x i = true then (1 : ℝ) else 0)}

end SpacePropTest.Supplement


