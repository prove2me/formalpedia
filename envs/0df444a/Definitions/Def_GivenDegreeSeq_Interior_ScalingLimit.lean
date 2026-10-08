-- Prove2me | Definitions.Def_GivenDegreeSeq_Interior_ScalingLimit
-- name    : GivenDegreeSeq_Interior_ScalingLimit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T04:51:30.737452+00:00
-- url     : https://prove2.me/theorems/595d5fbe-3b42-449d-9e48-6ff3e94717ba
-- title:
--   Scaling limits (2) of degree sequences, the set $\mathcal F$, and its interior in $(D'[0,1],\|\cdot\|_{1'})$
-- statement:
--   Suppose that for each $n$ a degree sequence $\mathbf d^n=(d^n_1,\dots,d^n_n)$ is given, written in nonincreasing order $d^n_1\ge d^n_2\ge\cdots\ge d^n_n$.
--
--   1. The sequence $\{\mathbf d^n\}$ has **scaling limit** $f$ if $f$ is a nonincreasing function on $[0,1]$ such that
--   $$\lim_{n\to\infty}\Bigl(\Bigl|\frac{d^n_1}{n}-f(0)\Bigr|+\Bigl|\frac{d^n_n}{n}-f(1)\Bigr|+\frac1n\sum_{i=1}^n\Bigl|\frac{d^n_i}{n}-f\Bigl(\frac in\Bigr)\Bigr|\Bigr)=0.\qquad(2)$$
--   2. $\mathcal F$ is the set of functions in $D'[0,1]$ that are scaling limits of some sequence $\{\mathbf d^n\}_{n\ge0}$ in which every $\mathbf d^n$ is the (nonincreasingly ordered) degree sequence of a simple graph on $n$ vertices.
--   3. $f$ lies in the **interior of $\mathcal F$** if $f\in D'[0,1]$ and there is $\varepsilon>0$ such that every $h\in D'[0,1]$ with $\|h-f\|_{1'}<\varepsilon$ belongs to $\mathcal F$.
--
--   $\mathcal F$ is the set of possible limiting degree profiles of large graphs; its interior is where the paper's graph-limit theorem (Theorem 1.1) applies.
--
--   **Formalization Note** $\mathbf d^n$ is `d n : Fin n → ℕ` with $d^n_i$ = `d n ⟨i-1, _⟩`, so $f(i/n)$ is written `f ((i+1)/n)` for `i : Fin n`. The bracket in (2) is undefined at $n=0$ and is set to $0$ there; this does not affect the limit. The sequence is indexed by every $n$, not a subsequence (for small $n$ the zero sequence is graphic, so this costs nothing). The interior is taken in the metric space $D'[0,1]$ with $\|\cdot\|_{1'}$: this is a genuine norm on $D'[0,1]$, since a nonincreasing function that is left continuous on $(0,1)$ and vanishes almost everywhere vanishes on $(0,1)$, and the endpoint values are controlled explicitly; so the ball formulation is exactly the topological interior.
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, pp. 3–4, Eq. (2), definition of D′[0,1], ‖·‖_{1′} and F

import Mathlib
import Definitions.Def_GivenDegreeSeq_Interior_IsGraphic
import Definitions.Def_GivenDegreeSeq_Interior_DPrime

namespace GivenDegreeSeq.Interior

/-! Chatterjee, Diaconis & Sly, *Random Graphs with a Given Degree Sequence*,
arXiv:1005.1136v5, pp. 3–4: scaling limits (2) of degree sequences, the set `F` of all scaling
limits in `D′[0,1]`, and its topological interior for the modified `L¹` norm `‖·‖_{1′}`.

For every `n` a degree sequence `d^n = (d^n_1, …, d^n_n)` is given; in Lean it is
`d n : Fin n → ℕ`, with the paper's `d^n_i` equal to `d n ⟨i − 1, _⟩`. -/

/-- The quantity inside the limit (2) (p. 4), for `n ≥ 1`:
`|d^n_1/n − f(0)| + |d^n_n/n − f(1)| + (1/n) Σ_{i=1}^n |d^n_i/n − f(i/n)|`.
The paper's index `i = 1, …, n` is `i : Fin n` shifted by one, so `f(i/n)` is
`f ((i + 1)/n)`. There is no `d^0_1`, so the value at `n = 0` is set to `0`; it does not affect
the limit. -/
noncomputable def scalingError (d : (n : ℕ) → Fin n → ℕ) (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  if h : 0 < n then
    |(d n ⟨0, h⟩ : ℝ) / n - f 0| + |(d n ⟨n - 1, Nat.sub_lt h Nat.one_pos⟩ : ℝ) / n - f 1|
      + (1 / (n : ℝ)) * ∑ i : Fin n, |(d n i : ℝ) / n - f (((i : ℕ) + 1 : ℝ) / n)|
  else 0

/-- The sequence `{d^n}` has scaling limit `f` (p. 4): `f` is nonincreasing on `[0,1]` and the
quantity of (2) tends to `0` as `n → ∞`. -/
def HasScalingLimit (d : (n : ℕ) → Fin n → ℕ) (f : ℝ → ℝ) : Prop :=
  AntitoneOn f (Set.Icc 0 1) ∧ Filter.Tendsto (scalingError d f) Filter.atTop (nhds 0)

/-- The set `F` (p. 4): the functions in `D′[0,1]` that are scaling limits of a sequence
`{d^n}_{n ≥ 0}` in which every `d^n` is a degree sequence of a simple graph on `n` vertices,
written in nonincreasing order `d^n_1 ≥ ⋯ ≥ d^n_n`. -/
def setF : Set (ℝ → ℝ) :=
  {f | InDprime f ∧ ∃ d : (n : ℕ) → Fin n → ℕ,
    (∀ n, Antitone (d n) ∧ IsGraphic (d n)) ∧ HasScalingLimit d f}

/-- `f` lies in the topological interior of `F` inside `D′[0,1]` with the topology of the
modified `L¹` norm `‖·‖_{1′}` (p. 4): `f ∈ D′[0,1]` and some `‖·‖_{1′}`-ball around `f`,
intersected with `D′[0,1]`, is contained in `F`. -/
def InteriorF (f : ℝ → ℝ) : Prop :=
  InDprime f ∧ ∃ ε > 0, ∀ h : ℝ → ℝ, InDprime h → norm1' (h - f) < ε → h ∈ setF

end GivenDegreeSeq.Interior


