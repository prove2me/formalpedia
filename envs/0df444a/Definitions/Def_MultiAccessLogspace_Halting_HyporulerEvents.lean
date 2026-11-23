-- Prove2me | Definitions.Def_MultiAccessLogspace_Halting_HyporulerEvents
-- name    : MultiAccessLogspace_Halting_HyporulerEvents
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T02:28:44.892098+00:00
-- url     : https://prove2.me/theorems/f06f68b2-d07d-4945-91dd-f046f08f26ec
-- title:
--   Events in the hyporuler generation bound
-- statement:
--   For $x\in\mathbb N\cup\{\infty\}$ and $d\ge0$, the predicate $\operatorname{InRange}(d,x)$ says that $x=h$ for some integer $1\le h\le d$.
--
--   For random variables $H_0,\ldots,H_{N-1}$ with values in $\mathbb N\cup\{\infty\}$, an index $j$, and $h\in[d]$, the event $\operatorname{RepeatedBeforeGreater}(b,H,j,h)$ consists of those $\omega$ for which $H_j(\omega)=h$ and there is an interval $\{k,\ldots,j\}$ containing no value larger than $h$ and containing at least $b$ occurrences of $h$. This is precisely the finite-run event bounded by scanning backwards in Hoza’s proof of Lemma 3.4: after fixing $H_j=h$, there would be $b-1$ earlier occurrences of $h$ before any occurrence of a value larger than $h$.
--
--   The aggregate event $\operatorname{HasRepeatedBeforeGreater}(b,d,H,j)$ is the union of these events over $h\in[d]$. These definitions isolate the set-theoretic content of the generation bound and do not assert any probability estimate.
--
--   **Formalization Note.** Coordinates are indexed by `Fin N`, and a greater-free interval is represented by `Finset.Icc k j`.
-- source:
--   William M. Hoza, STOC 2027 submission #92 (October 2026), Lemma 3.4 proof, PDF p. 7 (printed p. 6), especially the backward-scanning event after Condition 2 of Lemma 3.3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/92.pdf; PDF SHA-256 92de35889559d87b5a77d83317b9c7b2c8924912fbd5c712f2af3c005c8998d8

import Mathlib
import Definitions.Def_MultiAccessLogspace_Halting_Rulers

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MultiAccessLogspace.Halting

/-- A value in `ℕ ∪ {∞}` belongs to the source's discrete interval `[d] = {1, …, d}`. -/
def InRangeENat (d : ℕ) (x : ℕ∞) : Prop :=
  ∃ h : ℕ, 1 ≤ h ∧ h ≤ d ∧ x = (h : ℕ∞)

/-- There is an interval ending at `j`, containing no value greater than `h`, in which `h`
occurs at least `b` times; in particular the last entry is `h`. This is the finite-sequence event
used in the backward-scanning estimate in Lemma 3.4. -/
def RepeatedBeforeGreater {Ω : Type*} {N : ℕ} (b : ℕ) (H : Fin N → Ω → ℕ∞)
    (j : Fin N) (h : ℕ) (ω : Ω) : Prop :=
  H j ω = (h : ℕ∞) ∧
    ∃ k : Fin N, k ≤ j ∧
      b ≤ ((Finset.Icc k j).filter fun i => H i ω = (h : ℕ∞)).card ∧
      ∀ i ∈ Finset.Icc k j, ¬ (h : ℕ∞) < H i ω

/-- At coordinate `j`, the repeated-value event occurs for some value in `[d]`. -/
def HasRepeatedBeforeGreater {Ω : Type*} {N : ℕ} (b d : ℕ) (H : Fin N → Ω → ℕ∞)
    (j : Fin N) (ω : Ω) : Prop :=
  ∃ h : ℕ, 1 ≤ h ∧ h ≤ d ∧ RepeatedBeforeGreater b H j h ω

end MultiAccessLogspace.Halting


