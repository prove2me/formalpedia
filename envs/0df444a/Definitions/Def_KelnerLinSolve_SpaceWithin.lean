-- Prove2me | Definitions.Def_KelnerLinSolve_SpaceWithin
-- name    : KelnerLinSolve_SpaceWithin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:54:41.779191+00:00
-- url     : https://prove2.me/theorems/6780d5cb-e4ed-40f1-811c-1ac691ff93f1
-- title:
--   Storage of a multitape run, the polylogarithmic factor, and regular multiplication-time bounds
-- statement:
--   Let $M$ be a deterministic multitape Turing machine. $M$ runs **within storage $\sigma$** on input $w$ for $t$ steps if during its first $t$ steps no head, including the head of the read-only input tape, moves past cell $\sigma$. With the number of tapes fixed, the number of cells used is within a constant factor of $\sigma$.
--
--   The polylogarithmic factor of the $\tilde O$ bounds is $\mathrm{lg}(x)^K$ with $\mathrm{lg}(x) = \max(\lceil\log_2 x\rceil, 1)$.
--
--   A function $T:\mathbb N\to\mathbb R$ is a **regular multiplication-time bound** if $T(s)/s$ is nondecreasing for $s\ge1$ and $T(2s)\le 4T(s)$ for $s\ge1$. These are the standard conditions under which half-gcd style reconstruction costs $O(M(s)\log s)$; they hold for $s$, $s\,\mathrm{lg}\,s$ and $s\,(\mathrm{lg}\,s+2c)^c$, the last of which bounds $s\,\mathrm{lg}(s)^c$.
--
--   **Formalization Note** The machine model is the public `IntMul.MultitapeTM`. The paper names no machine and says "bits of storage"; the input tape is counted, as in its own accounting.
-- source:
--   Kelner, Solving Linear Systems in Õ(mn log(κ/ε)) Bit Operations, STOC 2027 submission (sha256 d1af55cb…), Theorem 1.1, p.3; Theorem 2.3, p.7; Theorem 3.3, p.10; §4.4, p.14

import Mathlib
import Definitions.Def_IntMul_MultitapeWords

namespace KelnerLinSolve

/-- **Storage bound of a multitape run.** On input `w`, during its first `t` steps the machine `M`
never moves any head (input tape included) past cell `σ`. With the number of tapes fixed, the number
of tape cells the run uses is within the factor `M.k` of `σ`, so this is "storage at most `σ`
cells" up to a constant. Storage convention for "bits of storage" in Kelner, *Solving Linear Systems
in Õ(mn log(κ/ε)) Bit Operations*, STOC 2027 submission (sha256 d1af55cb…), Theorem 1.1, p.3, and
Theorem 3.3, p.10.

**Formalization Note.** The machine model is `IntMul.MultitapeTM` (reused, public). The read-only
input tape is counted, as in the paper's storage accounting ("Retaining the original encoded
inputs", §4.4, p.14). A head can only reach cell `p` after visiting cells `0, …, p`, so the head
position bounds the used cells. -/
def SpaceWithin (M : IntMul.MultitapeTM) (w : List (Option Bool)) (t : ℕ) (σ : ℝ) : Prop :=
  ∀ s ≤ t, ∀ i, (((M.step^[s] (M.initCfgW w)).head i : ℕ) : ℝ) ≤ σ

/-- The polylogarithmic factor `lg(x)^K` of the `Õ` bounds, with `lg x = max(⌈log₂ x⌉, 1)`
(`IntMul.lg`). Kelner (sha256 d1af55cb…), §1.1, p.3: "`Õ` suppresses factors polylogarithmic in
the dimension and bit-length". -/
noncomputable def polylog (K : ℕ) (x : ℕ) : ℝ := (IntMul.lg x : ℝ) ^ K

/-- **A regular multiplication-time bound** `T : ℕ → ℝ`: `T(s)/s` is nondecreasing for `s ≥ 1`, and
`T(2s) ≤ 4 T(s)` for `s ≥ 1`. These are the standard regularity conditions under which the cost of
fast extended-Euclidean (half-gcd) reconstruction is `O(M(s) log s)`; they hold for `s`, `s · lg s` and
`s · (lg s + 2c)^c`, the last of which bounds `s · (lg s)^c`. Used to read `M(s)` in Kelner
(sha256 d1af55cb…), Theorem 2.3 and Corollary 2.4, p.7, where `M(s)` is "the bit complexity of
multiplying two `s`-bit integers". -/
def IsRegularTimeBound (T : ℕ → ℝ) : Prop :=
  (∀ s : ℕ, 1 ≤ s → T s / s ≤ T (s + 1) / (s + 1)) ∧ (∀ s : ℕ, 1 ≤ s → T (2 * s) ≤ 4 * T s)

end KelnerLinSolve


