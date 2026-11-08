-- Prove2me | Definitions.Def_ErrAmpOV_SizeDecides
-- name    : ErrAmpOV_SizeDecides
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:38:29.457379+00:00
-- url     : https://prove2.me/theorems/adcfb1b5-42de-4d71-a153-95e4e98a309b
-- title:
--   $\mathsf{SIZE}[S]$ at one input length
-- statement:
--   For a real number $S$ and a Boolean function $f:\{0,1\}^\iota\to\{0,1\}$, $f$ is decided in size $S$ when there is a deterministic circuit $C$ with at most $S$ gates and one output wire such that
--   $$
--   C(x)=f(x)\quad\text{for every }x\in\{0,1\}^\iota .
--   $$
--
--   A family statement $f\in\mathsf{SIZE}[S(n)]$ reads: for all sufficiently large $n$, $f_n$ is decided in size $S(n)$. This is the deterministic class in the conclusion of Theorem 3.1.
--
--   **Formalization Note** The bound is exact, with no $O$-constant. Asymptotic statements use `∀ᶠ n in Filter.atTop, SizeDecides (S n) (f n)`.
-- source:
--   Koucký, Mertz, Rajgopal, Efficient Error Amplification for Sorting and Orthogonal Vectors, STOC 2027 submission (manuscript of November 3, 2026, sha256 f31f577a…72fbb9d3), §2.1, p.5 (unnumbered definition of SIZE[S(n)])

import Mathlib
import Definitions.Def_ErrAmpOV_Circuit

set_option autoImplicit false

namespace ErrAmpOV

/-- `SizeDecides S f`: some deterministic circuit with at most `S` gates and a single output
wire computes `f` on every input. At one input length this is "`f ∈ SIZE[S]`".

Source: Koucký, Mertz, Rajgopal, *Efficient Error Amplification for Sorting and Orthogonal
Vectors*, STOC 2027 submission (manuscript of November 3, 2026, sha256 f31f577a…72fbb9d3),
§2.1, p.5 (unnumbered definition of `SIZE[S(n)]`: "each `C_n` is over `n` inputs and has size
`S(n)`, such that … for every `x ∈ {0,1}^n`, `C_n(x) = f_n(x)`").

**Formalization Note.** The size bound is exact ("at most `S`"), with no `O`-constant. A family
statement "`f ∈ SIZE[S(n)]`" is `∀ᶠ n in Filter.atTop, SizeDecides (S n) (f n)`. The circuit
model is `ErrAmpOV.Circuit` (fan-in ≤ 2, size = number of gates). -/
def SizeDecides {ι : Type} (S : ℝ) (f : (ι → Bool) → Bool) : Prop :=
  ∃ C : Circuit ι, (C.size : ℝ) ≤ S ∧ ∀ x, C.eval x = [f x]

end ErrAmpOV


