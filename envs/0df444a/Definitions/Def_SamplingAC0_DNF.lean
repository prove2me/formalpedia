-- Prove2me | Definitions.Def_SamplingAC0_DNF
-- name    : SamplingAC0_DNF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:44:39.783918+00:00
-- url     : https://prove2.me/theorems/2344baaf-afd8-4397-b579-1cd68685d3c6
-- title:
--   DNF formulas and their size
-- statement:
--   A **literal** over variables $V$ is $x_v$ or $\neg x_v$; a **term** is a conjunction of literals; a **DNF** is a disjunction of terms, given as a list of terms. A DNF is true on an assignment $x\in\{0,1\}^V$ when some term has all its literals satisfied; the empty DNF is constantly false.
--
--   The **size** of a DNF is the number of terms plus the total number of literal occurrences. Renaming variables along a map $V\to W$ gives a DNF over $W$.
--
--   These are the samplers of Theorem 4: each output bit of the hard distribution is one DNF of the uniform input bits.
--
--   **Formalization Note** The size counts literals as well as terms, so a size bound is at least as strong as a bound on the number of terms.
-- source:
--   Riazanov–Viola, Sampling Tools and the Power of AC0, STOC 2027 submission (manuscript sha256 99c33d30…), §3, p.8; Theorem 4, p.3

import Mathlib
set_option autoImplicit false

namespace SamplingAC0

/-- A literal over variables `V`: a variable together with the value it requires
(`(v, true)` is `x_v`, `(v, false)` is `¬x_v`). -/
abbrev Literal (V : Type) : Type := V × Bool

/-- A term (conjunction of literals). -/
abbrev Term (V : Type) : Type := List (Literal V)

/-- **DNF formula.** Riazanov–Viola, *Sampling Tools and the Power of AC0*, STOC 2027 submission
(manuscript sha256 99c33d30…), §3, p.8 ("This is an explicit DNF with q² terms") and Theorem 4, p.3
("sampled by n explicit DNFs of size n^c"). A DNF over the variables `V` is a list of terms; it is
true on `x` when some term has all its literals satisfied. The empty DNF is constantly false. -/
abbrev DNF (V : Type) : Type := List (Term V)

/-- Evaluation of a DNF on an assignment `x : V → Bool`. -/
def DNF.eval {V : Type} (φ : DNF V) (x : V → Bool) : Bool :=
  φ.any (fun t => t.all (fun l => x l.1 == l.2))

/-- **Size of a DNF**: number of terms plus total number of literal occurrences.

**Formalization Note.** This counts more than the number of terms alone, so a bound on it is the
stronger size bound. -/
def DNF.size {V : Type} (φ : DNF V) : ℕ :=
  φ.length + (φ.map List.length).sum

/-- Renaming the variables of a DNF along `g : V → W`. -/
def DNF.rename {V W : Type} (g : V → W) (φ : DNF V) : DNF W :=
  φ.map (fun t => t.map (fun l => (g l.1, l.2)))

end SamplingAC0


