-- Prove2me | Definitions.Def_IntroDelayAMDP_sampleCat
-- name    : IntroDelayAMDP_sampleCat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:44:01.252197+00:00
-- url     : https://prove2.me/theorems/2abb0db7-0baf-4746-9645-ec1f9a91cbb9
-- title:
--   Inverse-CDF sampler
-- statement:
--   For a finite type enumerated as $x_0,\dots,x_{n-1}$, a weight vector $p$ and $u\in[0,1]$, the sampler returns the element $x_j$ with $\sum_{i<j}p(x_i)\le u<\sum_{i\le j}p(x_i)$, and a default element if there is none.
--
--   If $p$ is a probability vector and $u$ is uniform on $[0,1]$, the result has law $p$. The default is reached only on a null set.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), realizing the sampling of Section 2.1, p.12

import Mathlib

namespace IntroDelayAMDP

open Classical in
/-- **Inverse-CDF sampler** (the realization of "`a_h ∼ π(· | s_h)` and `s_{h+1} ∼ P(· | s_h, a_h)`",
Section 2.1, printed p.12, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)).

For a finite type `X`, a weight vector `p : X → ℝ` and `u ∈ [0, 1]`, enumerate `X` as
`x_0, …, x_{n−1}` (`Fintype.equivFin`) and let `F_i = ∑_{j<i} p(x_j)`. `sampleCat d p u` is the
element `x_j` with `F_j ≤ u < F_{j+1}`, and the default `d` if there is none.

**Formalization Note.** If `p` is a probability vector and `u` is uniform on `[0, 1]`, the
result has law `p` (the intervals `[F_j, F_{j+1})` partition `[0, 1)`, and `u = 1` has
probability `0`). The default is only reached on a null set or for a vector that is not a
probability vector. -/
noncomputable def sampleCat {X : Type} [Fintype X] (d : X) (p : X → ℝ) (u : ℝ) : X :=
  if h : ∃ j : Fin (Fintype.card X),
      (∑ i ∈ Finset.univ.filter (fun i : Fin (Fintype.card X) => (i : ℕ) < j),
          p ((Fintype.equivFin X).symm i)) ≤ u ∧
        u < ∑ i ∈ Finset.univ.filter (fun i : Fin (Fintype.card X) => (i : ℕ) < (j : ℕ) + 1),
          p ((Fintype.equivFin X).symm i) then
    (Fintype.equivFin X).symm h.choose
  else d

end IntroDelayAMDP


