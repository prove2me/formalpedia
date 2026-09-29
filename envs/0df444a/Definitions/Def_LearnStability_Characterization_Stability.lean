-- Prove2me | Definitions.Def_LearnStability_Characterization_Stability
-- name    : LearnStability_Characterization_Stability
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T18:08:04.498145+00:00
-- url     : https://prove2.me/theorems/8a563392-6845-4525-80cc-c78ee108d35a
-- title:
--   Uniform-RO stability (Definition 4) and average-RO stability (Definition 5)
-- statement:
--   For a sample $S=(z_1,\dots,z_m)$ and a replacement vector $S'=(z_1',\dots,z_m')$, write $S^{(i)}=(z_1,\dots,z_{i-1},z_i',z_{i+1},\dots,z_m)$ for the sample with its $i$-th point replaced by $z_i'$.
--
--   1. (Definition 4) A rule $A$ is **uniform-RO stable with rate $\varepsilon_{\rm stable}$** if for every $m\ge1$, every $S$, every replacement vector $S'$ and every $z'\in\mathcal Z$,
--   $$\frac1m\sum_{i=1}^m\bigl|f(A(S^{(i)});z')-f(A(S);z')\bigr|\le\varepsilon_{\rm stable}(m).$$
--   2. (Definition 5) A rule $A$ is **average-RO stable with rate $\varepsilon_{\rm stable}$ under $\mathcal D$** if for every $m\ge1$,
--   $$\Bigl|\frac1m\sum_{i=1}^m\mathbb E_{S\sim\mathcal D^m,\,(z_1',\dots,z_m')\sim\mathcal D^m}\bigl[f(A(S^{(i)});z_i')-f(A(S);z_i')\bigr]\Bigr|\le\varepsilon_{\rm stable}(m).$$
--
--   Uniform-RO stability is a worst-case condition over all samples, replacements and test points, and involves no distribution; average-RO stability is an in-expectation condition in which the replacement point $z_i'$ is also the test point. "RO" stands for replace-one.
--
--   **Formalization Note.** $S^{(i)}$ is `Function.update S i (S' i)`. In Definition 5 the pair $(S,S')$ is drawn from the product measure $\mathcal D^m\otimes\mathcal D^m$.
-- source:
--   Shalev-Shwartz, Shamir, Srebro and Sridharan, Learnability, Stability and Uniform Convergence, JMLR 11 (2010), p. 2648, Definitions 4 and 5

import Mathlib
import Definitions.Def_LearnStability_Characterization_Setting

open MeasureTheory

namespace LearnStability.Characterization

variable {H Z : Type*} [MeasurableSpace Z]

/-- Definition 4 (p. 2648): `A` is uniform-RO stable with rate `ε` if for every `m ≥ 1`, every
sample `S = (z_1, …, z_m)`, every replacement vector `S' = (z'_1, …, z'_m)` and every test
point `z'`,
`(1/m) ∑_i |f(A(S^{(i)}); z') − f(A(S); z')| ≤ ε(m)`,
where `S^{(i)}` is `S` with its `i`-th point replaced by `z'_i`. -/
def UniformROStable (f : H → Z → ℝ) (A : Rule H Z) (ε : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ S S' : Fin m → Z, ∀ z' : Z,
    (∑ i, |f (A m (Function.update S i (S' i))) z' - f (A m S) z'|) / m ≤ ε m

/-- Definition 5 (p. 2648): `A` is average-RO stable with rate `ε` under `D` if for every
`m ≥ 1`,
`|(1/m) ∑_i E_{S∼D^m, (z'_1,…,z'_m)∼D^m}[f(A(S^{(i)}); z'_i) − f(A(S); z'_i)]| ≤ ε(m)`. -/
def AverageROStable (f : H → Z → ℝ) (A : Rule H Z) (D : Measure Z) (ε : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    |(∑ i, ∫ p, (f (A m (Function.update p.1 i (p.2 i))) (p.2 i) - f (A m p.1) (p.2 i))
        ∂((sampleLaw D m).prod (sampleLaw D m))) / m| ≤ ε m

end LearnStability.Characterization


