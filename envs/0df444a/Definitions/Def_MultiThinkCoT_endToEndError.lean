-- Prove2me | Definitions.Def_MultiThinkCoT_endToEndError
-- name    : MultiThinkCoT_endToEndError
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:40:28.777852+00:00
-- url     : https://prove2.me/theorems/6f2bfee9-0eaf-42a0-ab7d-b4a9a0615ca0
-- title:
--   The end-to-end error $L_{\mathcal D,h^\star}$ and the i.i.d. sample law
-- statement:
--   For a distribution $\mathcal D$ over the domain $\mathcal X$, a target $h^\star:\mathcal X\to\{0,1\}$ and a predictor $\hat h:\mathcal X\to\{0,1\}$, the **end-to-end error** is
--
--   $$
--   L_{\mathcal D,h^\star}(\hat h)=\Pr_{x\sim\mathcal D}\big[\hat h(x)\neq h^\star(x)\big].
--   $$
--
--   The training inputs $x^{(1)},\dots,x^{(m)}$ are drawn i.i.d. from $\mathcal D$; the module also defines the law of this $m$-tuple, built from $m$ independent draws.
--
--   All guarantees of the mission bound the probability, under this law (and the learner's internal randomness), that the error exceeds $\varepsilon$.
--
--   **Formalization Note** The domain is a set of finite strings, hence countable, so a distribution on it is a probability mass function. The error is the probability of the disagreement set as a real number in $[0,1]$.
-- source:
--   Joshi, Magen, Srebro, Tsilivis, Vardi, Learning to Think from Multiple Thinkers: How Chain-of-Thought Heterogeneity Affects Efficient Learnability, arXiv:2604.24737 (held version, sha256 e663a640…), §2, eq. (5), p.5 (PDF p.5); Definition 2.3, p.8; eq. (8), p.16

import Mathlib

namespace MultiThinkCoT

/-!
# The end-to-end error `L_{D,h⋆}` (5) and the i.i.d. sample

N. Joshi, R. Magen, N. Srebro, N. Tsilivis, G. Vardi, *Learning to Think from Multiple Thinkers*,
arXiv:2604.24737 (held version, sha256 e663a640…), §2, eq. (5), p.5 (PDF p.5); the sample
`x(1), …, x(m) ∼iid D` of Definition 2.3, p.8, and (8), p.16.

`L_{D,h⋆}(ĥ) = Pr_{x∼D}[ĥ(x) ≠ h⋆(x)]`.

**Formalization Note.** The domain `X ⊆ {0,1}*` is countable, so a distribution `D ∈ ∆(X)` is a
probability mass function `D : PMF X`. The error is the `D`-probability of the disagreement set,
converted to a real number (it is at most `1`). `iidSample D m` is the law of
`(x(1), …, x(m))`, built as `m` independent draws from `D`.
-/

/-- (5) The end-to-end error `L_{D,h⋆}(h) = Pr_{x∼D}[h(x) ≠ h⋆(x)]`. -/
noncomputable def endToEndError {X : Type} (D : PMF X) (hstar h : X → Bool) : ℝ :=
  (D.toOuterMeasure {x | h x ≠ hstar x}).toReal

/-- The law of `m` i.i.d. draws `x(1), …, x(m) ∼ D`. -/
noncomputable def iidSample {X : Type} (D : PMF X) : (m : ℕ) → PMF (Fin m → X)
  | 0 => PMF.pure Fin.elim0
  | m + 1 => D.bind fun a => (iidSample D m).map fun xs => (Fin.cons a xs : Fin (m + 1) → X)

end MultiThinkCoT


