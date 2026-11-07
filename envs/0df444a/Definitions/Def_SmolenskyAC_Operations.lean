-- Prove2me | Definitions.Def_SmolenskyAC_Operations
-- name    : SmolenskyAC_Operations
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:46:30.772282+00:00
-- url     : https://prove2.me/theorems/4cb4661e-add6-4a28-abd2-16e061ce4bfd
-- title:
--   Basic operations AND, OR, NOT, $\mathrm{MOD}_{s,p}$, $\mathrm{MOD}_p$ on the Boolean cube
-- statement:
--   Write $D^n=\{0,1\}^n$ for the Boolean cube, the truth assignments to $X_1,\dots,X_n$. An **operation** is a Boolean function of every arity $m$: gates have unbounded fan-in. For inputs $z_1,\dots,z_m$ let $|z|$ be the number of ones, counted with multiplicity.
--
--   1. $\mathrm{AND}(z)=1$ iff all inputs are ones; $\mathrm{OR}(z)=1$ iff at least one input is one.
--   2. $\mathrm{NOT}(z)$ is the negation of its (first) input.
--   3. $\mathrm{MOD}_{s,p}(z)=1$ iff $|z|\equiv s \pmod p$.
--   4. $\mathrm{MOD}_p=\mathrm{NOT}(\mathrm{MOD}_{0,p})$: it outputs $1$ iff $|z|$ is **not** divisible by $p$.
--
--   These are the basic operations of the paper's circuits; $\mathrm{MOD}_r$ on $n$ inputs is the function the main theorem shows hard.
--
--   **Formalization Note** $\mathrm{NOT}$ is an operation of every arity that negates its first input and ignores the others, and outputs $1$ with no input; the page's $\mathrm{NOT}$ is the fan-in $1$ case. The empty AND is $1$ and the empty OR is $0$.
-- source:
--   Smolensky, Algebraic methods in the theory of lower bounds for Boolean circuit complexity, Proc. 19th ACM STOC (1987), pp. 77–82, doi:10.1145/28395.28404, Basic Notation and Definitions, operations 1)–4), p.78 (pdf 2); abstract, p.77 (pdf 1)

import Mathlib

namespace SmolenskyAC

/-- The Boolean cube `D^n`: truth assignments to the variables `X_1, …, X_n`
(Smolensky, STOC 1987, "The Mappings from the set of Boolean functions to F-algebras", p.78). -/
abbrev Cube (n : ℕ) := Fin n → Bool

/-- A type of operation (Smolensky, STOC 1987, "Basic Notation and Definitions", p.78): a Boolean
function of every arity `m`, since gates have unbounded fan-in.

**Formalization Note.** The inputs of an `m`-ary application are indexed by `Fin m`; repeated
wires are allowed, so counts are with multiplicity. -/
abbrev Operation := ∀ m : ℕ, (Fin m → Bool) → Bool

/-- The number of ones among the inputs `z`. -/
def countOnes {m : ℕ} (z : Fin m → Bool) : ℕ :=
  (Finset.univ.filter fun i => z i = true).card

/-- `AND` (Smolensky, STOC 1987, p.78, operation 1): outputs one iff all of the inputs are ones.
The empty `AND` is `true`. -/
def AND : Operation := fun _ z => decide (∀ i, z i = true)

/-- `OR` (Smolensky, STOC 1987, p.78, operation 2): outputs one iff at least one input is one.
The empty `OR` is `false`. -/
def OR : Operation := fun _ z => decide (∃ i, z i = true)

/-- `NOT` (Smolensky, STOC 1987, p.78, operation 3): takes one input and computes the negation.

**Formalization Note.** As an operation of every arity, `NOT` negates its first input and ignores
any further inputs; with no input it outputs `true` (a constant, which wires provide anyway). A
page circuit uses `NOT` with exactly one input, which is the case `m = 1`. -/
def NOT : Operation := fun m z => if h : 0 < m then !(z ⟨0, h⟩) else true

/-- `MOD_{s,p}` (Smolensky, STOC 1987, p.78, operation 4): outputs one iff the number of ones in
the input is congruent to `s` mod `p`. -/
def MODs (s p : ℕ) : Operation := fun _ z => decide (countOnes z ≡ s [MOD p])

/-- `MOD_p = NOT(MOD_{0,p})` (Smolensky, STOC 1987, p.78, operation 4): outputs one iff the number
of ones in the input is **not** divisible by `p` (also the abstract, p.77: "outputs zero, if the
number of ones is divisible by m"). -/
def MODp (p : ℕ) : Operation := fun m z => !(MODs 0 p m z)

end SmolenskyAC


