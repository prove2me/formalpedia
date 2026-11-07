-- Prove2me | Definitions.Def_EffRobustLearn_weightedERM
-- name    : EffRobustLearn_weightedERM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:32:51.696609+00:00
-- url     : https://prove2.me/theorems/2ba4bdd5-23ed-4686-83cc-4aaddf3a3b1f
-- title:
--   The sampler of Fact 3.2 (Weighted ERM)
-- statement:
--   Given a dataset $\bar S$ of size $M$ and weights $w$, the algorithm of Fact 3.2 draws $N=\lceil C_F(b^2/\varepsilon^2)(M+\log(1/\delta))\rceil$ independent samples, where $(x,\mathrm{sign}(w(x,y))y)$ is sampled with probability $|w(x,y)|/\sum_{(x',y')\in\bar S}|w(x',y')|$. It then runs unweighted ERM on this synthetic dataset. Its objective is $\frac1{|\bar S|}\sum_{(x,y)\in\bar S}w(x,y)c(x)y$.
--
--   **Formalization Note** The randomness is an explicit seed of i.i.d. uniform coordinates on $[0,1]$. Each draw is the inverse CDF of one coordinate, over the indices in their fixed order. The paper's $O(\cdot)$ is the constant $C_F$. If all weights vanish no index is drawn and the output is $O([\,])$. The record holds the output concept, one oracle call, and the unit-cost work $M+2N+1$.
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), Fact 3.2, p.12 (PDF p.13)

import Mathlib
import Definitions.Def_EffRobustLearn_toPM

open MeasureTheory

namespace EffRobustLearn

/-- The outcome of one run of the sampler of Fact 3.2: the concept returned, the number of oracle calls and the work. -/
structure SamplerRun (X : Type*) where
  concept : X → Bool
  calls : ℕ
  work : ℕ

/-- The size `N = ⌈C_F (b²/ε²)(|S̄| + log(1/δ))⌉` of the synthetic dataset of Fact 3.2, Klivans, Stavropoulos, Tikhonov, Vasilyan, *Efficient Robust Learning at the Information-Theoretic Limit*, arXiv:2609.17655 (held version, sha256 312a0857…), p.12. The paper's `O(·)` is the constant `C_F`,
which every theorem quantifies existentially. `⌈·⌉₊` is `0` on a negative argument, which happens only for `δ > 1`. -/
noncomputable def sampleSize (CF b ε δ : ℝ) (M : ℕ) : ℕ :=
  ⌈CF * (b ^ 2 / ε ^ 2) * ((M : ℝ) + Real.log (1 / δ))⌉₊

open Classical in
/-- One draw from the distribution `|w_i| / ∑_j |w_j|` on the indices `Fin M`, by the inverse CDF of a seed `u ∈ [0, 1]`:
the first index `i` in the fixed order with `u ∑_j |w_j| < ∑_{j≤i} |w_j|`.

**Formalization Note.** For `u < 1` and weights not all zero this picks `i` with probability `|w_i| / ∑_j |w_j|`, and only an index with `w_i ≠ 0`.
It returns `none` exactly when no index qualifies: all weights are zero, or `u = 1` (a null event). -/
noncomputable def drawIndex {M : ℕ} (w : Fin M → ℝ) (u : ℝ) : Option (Fin M) :=
  (List.finRange M).find? fun i => decide (u * ∑ j, |w j| < ∑ j ∈ Finset.Iic i, |w j|)

/-- The synthetic example of Fact 3.2 for index `i`: `(x, sign(w(x,y)) y)`. -/
noncomputable def synthPoint {X : Type*} {M : ℕ} (data : Fin M → X × Bool) (w : Fin M → ℝ) (i : Fin M) : X × Bool :=
  ((data i).1, if w i < 0 then !(data i).2 else (data i).2)

/-- The synthetic dataset of Fact 3.2 from `N` independent seed coordinates. -/
noncomputable def synthDataset {X : Type*} {M : ℕ} (data : Fin M → X × Bool) (w : Fin M → ℝ) (N : ℕ)
    (ω : ℕ → unitInterval) : List (X × Bool) :=
  (List.range N).filterMap fun j => (drawIndex w (ω j : ℝ)).map (synthPoint data w)

/-- The algorithm of Fact 3.2 (Weighted ERM), p.12: generate a dataset of `N = sampleSize CF b ε δ M` independent samples
from `S̄`, where `(x, sign(w(x,y)) y)` is sampled with probability `|w(x,y)| / ∑ |w(x',y')|`, and run unweighted ERM on it.

**Formalization Note.** The randomness is the explicit seed `ω`, with coordinates i.i.d. uniform on `[0, 1]` under `seedStreamLaw`. If all weights vanish no index
is ever drawn and the output is `O []`, which ranges over all of `C` as `O` ranges over ERM oracles. `calls` is the one oracle call. `work` is `|S̄| + 2N + 1` in the unit-cost model: one
pass over the weights, a draw and a write per synthetic example, and the call itself. -/
noncomputable def weightedERM {X : Type*} {M : ℕ} (O : List (X × Bool) → X → Bool) (CF b ε δ : ℝ)
    (data : Fin M → X × Bool) (w : Fin M → ℝ) (ω : ℕ → unitInterval) : SamplerRun X where
  concept := O (synthDataset data w (sampleSize CF b ε δ M) ω)
  calls := 1
  work := M + 2 * sampleSize CF b ε δ M + 1

/-- The objective of Fact 3.2: `(1/|S̄|) ∑_{(x,y)∈S̄} w(x,y) c(x) y`. -/
noncomputable def weightedObjective {X : Type*} {M : ℕ} (data : Fin M → X × Bool) (w : Fin M → ℝ)
    (c : X → Bool) : ℝ :=
  (1 / (M : ℝ)) * ∑ i, w i * pm (c (data i).1) * pm (data i).2

/-- The law of the seed of `weightedERM`: i.i.d. uniform coordinates on `[0, 1]`. -/
noncomputable def seedStreamLaw : Measure (ℕ → unitInterval) :=
  Measure.infinitePi fun _ => (volume : Measure unitInterval)

end EffRobustLearn


