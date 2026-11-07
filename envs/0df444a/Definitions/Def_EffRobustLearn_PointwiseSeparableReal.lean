-- Prove2me | Definitions.Def_EffRobustLearn_PointwiseSeparableReal
-- name    : EffRobustLearn_PointwiseSeparableReal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:31:45.617985+00:00
-- url     : https://prove2.me/theorems/d8392e51-a55d-4e7b-9bc0-2f04a875081a
-- title:
--   Pointwise separability of a real-valued class
-- statement:
--   A class $F$ of real functions is pointwise separable if it has a countable subclass $F_0$ such that every $f\in F$ is the pointwise limit of a sequence in $F_0$.
--
--   Together with measurability of each $f$ and boundedness, this makes $s\mapsto\sup_{f\in F}\frac1n\sum_i\sigma_if(s_i)$ measurable.
--
--   **Formalization Note** This is not in the paper. It is the real-valued analogue of the published Boolean condition and supports the correction of Fact C.3 item 6.
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), Fact C.3 item 6, p.41 (PDF p.42), hypothesis added by the correction; Shalev-Shwartz and Ben-David, Understanding Machine Learning, Remark 3.1

import Mathlib

open Filter Topology

namespace EffRobustLearn

/-- The real-valued analogue of `UnderstandingML.PointwiseSeparable`: `F` has a countable subclass `F₀` such that every
`f ∈ F` is the pointwise limit of a sequence in `F₀`.

**Formalization Note.** This hypothesis is not in the paper (arXiv:2609.17655). It is the minimal correction of the paper's "any class"
in Fact C.3: for a bounded `F` of measurable functions it makes `s ↦ sup_{f∈F} (1/n) ∑ σ_i f(s_i)` measurable, so that the Bochner
integral defining `R_{n,D}(F)` is not the junk value `0`. It is the standard condition (Shalev-Shwartz and Ben-David, Remark 3.1). -/
def PointwiseSeparableReal {X : Type*} (F : Set (X → ℝ)) : Prop :=
  ∃ F₀ ⊆ F, F₀.Countable ∧ ∀ f ∈ F, ∃ u : ℕ → X → ℝ, (∀ k, u k ∈ F₀) ∧
    ∀ x, Tendsto (fun k => u k x) atTop (𝓝 (f x))

end EffRobustLearn


