-- Prove2me | Definitions.Def_PrivateUniformGen_Characterization_Bounds
-- name    : PrivateUniformGen_Characterization_Bounds
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:08:59.705477+00:00
-- url     : https://prove2.me/theorems/23dca694-ff33-4b07-a2b6-2d96d9b69192
-- title:
--   Threshold expressions and interior-point utility
-- statement:
--   The iterated logarithm $\log^* x$ is the least number of applications of $\log_2$ needed to reach a value at most one; it is zero for $x\le1$. Let $d=\operatorname{NBDim}(C)$, $h=h_{\mathrm{fin}}(C)$ and $c=\operatorname{CDim}(C)$, using finite projections only under the relevant finiteness assumptions. The exact selection threshold is
--
--   $$c+\frac{8h(2^d+1)}{\varepsilon}\max\left\{\ln\frac{2(2^d+1)}{\varepsilon},\ \ln\frac{2^d+1}{\delta}+\frac{\varepsilon}{4}\right\}.$$
--
--   The two asymptotic scales are $h2^d(d+\log_2(1/\varepsilon)+\log_2(1/\delta))/\varepsilon$ for selection and $d2^d(d+\log_2(1/(\varepsilon\delta)))/\varepsilon$ for generation. Selection utility means almost-sure infinite output contained in the closure whenever the input is realizable and its distinct support exceeds the threshold. Infiniteness on every input is a separate predicate.
--
--   For a dataset $y$ in an ordered finite domain, the interior event comprises outputs between its minimum and maximum, inclusive. Existential lower and upper input witnesses encode this event without default extrema on empty sets. All uses assume positive input length. These are expressions and utility predicates, not assumed estimates or results.
-- source:
--   Di Wang, Peng Ye, STOC 2027 submission #178 (October 2026), Section 3, p. 8; Theorems 1.2 and 5.16, pp. 3, 17; Lemmas 6.4 and 6.9, pp. 21, 24. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/178.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Robust

open MeasureTheory

namespace PrivateUniformGen.Characterization

/-- Section 3, p. 8: the least number of base-two logs to reach at most one.
    For x ≤ 1 the value is 0; on x ≥ 1 the defining set is nonempty. -/
noncomputable def logStar (x : ℝ) : ℕ :=
  sInf {k : ℕ | (Real.logb 2)^[k] x ≤ 1}

/-- Almost-sure infiniteness on every input, including unrealizable inputs. -/
def InfiniteEveryInput {X : Type*} {n : ℕ} (A : Mechanism X (Set X) n) : Prop :=
  ∀ S, ∀ᵐ Z ∂(A S : Measure (Set X)), Z.Infinite

/-- Selection utility at a distinct-support threshold; input elements need not be excluded. -/
def SelectionUtility {X : Type*} (C : LanguageClass X) {n : ℕ}
    (A : Mechanism X (Set X) n) (threshold : ℝ) : Prop :=
  ∀ S, (∃ L ∈ C.languages, Set.range S ⊆ L) → threshold ≤ (support S).card →
    ∀ᵐ Z ∂(A S : Measure (Set X)), Z.Infinite ∧ Z ⊆ closure C (Set.range S)

/-- Exact natural-log threshold from Theorem 5.16, p. 17. -/
noncomputable def selectionThreshold {X : Type*} (C : LanguageClass X) (ε δ : ℝ) : ℝ :=
  let d := (nbDim C ⊤).toNat
  let M : ℝ := 2 ^ d + 1
  (cdimInt C : ℝ) + 8 * (hellyNat C : ℝ) * M / ε *
    max (Real.log (2 * M / ε)) (Real.log (M / δ) + ε / 4)

/-- The scale in the final clause of Theorem 5.16; log means log base two. -/
noncomputable def selectionScale {X : Type*} (C : LanguageClass X) (ε δ : ℝ) : ℝ :=
  let d := (nbDim C ⊤).toNat
  (hellyNat C : ℝ) * 2 ^ d / ε *
    ((d : ℝ) + Real.logb 2 (1 / ε) + Real.logb 2 (1 / δ))

/-- The privacy term in Theorem 1.2, p. 3. -/
noncomputable def generationScale {X : Type*} (C : LanguageClass X) (ε δ : ℝ) : ℝ :=
  let d := (nbDim C ⊤).toNat
  (d : ℝ) * 2 ^ d / ε * ((d : ℝ) + Real.logb 2 (1 / (ε * δ)))

/-- On Fin N, order-preserving relabeling of [N] as {0,...,N-1}.
    The two existential clauses express min y ≤ z ≤ max y without empty infima. -/
def InteriorEvent {m N : ℕ} (y : Fin m → Fin N) : Set (Fin N) :=
  {z | (∃ i, y i ≤ z) ∧ ∃ j, z ≤ y j}

end PrivateUniformGen.Characterization


