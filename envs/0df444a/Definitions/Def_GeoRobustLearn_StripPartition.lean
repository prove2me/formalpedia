-- Prove2me | Definitions.Def_GeoRobustLearn_StripPartition
-- name    : GeoRobustLearn_StripPartition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:07:14.312365+00:00
-- url     : https://prove2.me/theorems/8cd50d84-ae24-404a-a6c4-d9437101760b
-- title:
--   Strip partitions of $\mathbb R^d$ encoded by seams and colours
-- statement:
--   A strip partition of $\mathbb R^d$ is given by seams $d_1\le\dots\le d_t$ and colours $\ell_0,\dots,\ell_t\in\{1,2,3\}$. With $d_0=-\infty$ and $d_{t+1}=+\infty$, the parts are
--
--   $$A_i=\bigcup_{0\le k\le t,\ \ell_k=i}\{x\in\mathbb R^d:\ d_k<x_1\le d_{k+1}\},\qquad i=1,2,3,$$
--
--   which partition $\mathbb R^d$ into parallel slabs orthogonal to the first coordinate. This is the output format of Algorithm 4, line 17.
--
--   **Formalization Note** The output block of a program is the list $[d_1,\dots,d_t,\ell_0,\dots,\ell_t]$ of length $2t+1$; `ValidStrips S` requires $t\le S$, nondecreasing seams (a repeated seam bounds an empty slab) and colours in $\{1,2,3\}$. Part $i\in\{0,1,2\}$ in Lean is colour $i+1$.
-- source:
--   Lange, Marcussen, Vasilyan, Geometrically Constrained Learning I: Agnostically Learning Adversarially Robust Classifiers, manuscript (Nov. 3, 2026; sha256 8cbf3f52…), Algorithm 4, lines 14–17, p.36

import Definitions.Def_GeoLipLearn_Agnostic_Gaussian

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GeoRobustLearn

open GeoLipLearn.Agnostic

/-!
# Strip partitions encoded by seams and colours

Lange, Marcussen, Vasilyan, *Geometrically Constrained Learning I*, manuscript of November 3, 2026
(sha256 8cbf3f52…): Algorithm 4, lines 14–17, p.36.

**Formalization Note.** An output block `rep = [d_1, …, d_t, ℓ_0, …, ℓ_t]` (length `2t + 1`) encodes
seams `d_1 ≤ ⋯ ≤ d_t` (a repeated seam bounds an empty strip) and colours `ℓ_k ∈ {1, 2, 3}`;
with `d_0 = −∞`, `d_{t+1} = +∞`, part `i`
(`i ∈ Fin 3`, colour `i + 1`) is `A_i = ⋃_{ℓ_k = i+1} {x : d_k < x_1 ≤ d_{k+1}}`. The first coordinate
`x_1` is `x 0`, and `0` when `d = 0`.
-/

/-- The first coordinate `x_1` of `x ∈ ℝ^d` (`0` if `d = 0`). -/
noncomputable def firstCoord {d : ℕ} (x : Space d) : ℝ :=
  if h : 0 < d then x ⟨0, h⟩ else 0

/-- The number of seams `t` of a block of length `2t + 1`. -/
def numSeams (rep : List ℝ) : ℕ := (rep.length - 1) / 2

/-- `rep` is a valid encoding with at most `S` seams: length `2t + 1`, `t ≤ S`, nondecreasing
seams, colours in `{1, 2, 3}`. -/
def ValidStrips (S : ℕ) (rep : List ℝ) : Prop :=
  ∃ t : ℕ, t ≤ S ∧ rep.length = 2 * t + 1 ∧
    (∀ k l : ℕ, k < l → l < t → rep[k]! ≤ rep[l]!) ∧
    ∀ k : ℕ, k ≤ t → (rep[t + k]! = 1 ∨ rep[t + k]! = 2 ∨ rep[t + k]! = 3)

/-- Part `A_i` (colour `i + 1`) of the strip partition encoded by `rep` (Algorithm 4, line 17). -/
noncomputable def stripPart {d : ℕ} (rep : List ℝ) (i : Fin 3) : Set (Space d) :=
  {x | ∃ k : ℕ, k ≤ numSeams rep ∧ rep[numSeams rep + k]! = (i.val + 1 : ℝ) ∧
    (k = 0 ∨ rep[k - 1]! < firstCoord x) ∧ (k = numSeams rep ∨ firstCoord x ≤ rep[k]!)}

end GeoRobustLearn


