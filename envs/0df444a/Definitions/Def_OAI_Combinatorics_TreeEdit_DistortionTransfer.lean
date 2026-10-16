-- Prove2me | Definitions.Def_OAI_Combinatorics_TreeEdit_DistortionTransfer
-- name    : OAI_Combinatorics_TreeEdit_DistortionTransfer
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:39:20.128731+00:00
-- url     : https://prove2.me/theorems/7fe7d5f2-85c3-462e-b95d-d792a52ee66c
-- title:
--   Expansion and contraction factors of a map from binary words into $\ell_1$
-- statement:
--   Let $W$ be a finite set of binary words, equipped with the unit-cost edit distance $\operatorname{ed}$ (the least number of single-symbol insertions, deletions and substitutions turning one word into the other), and let $\ell_1=\ell_1(\mathbb{N})$ be the space of absolutely summable real sequences with norm $\|v\|_1=\sum_n|v_n|$. For a map $f:W\to\ell_1$ define:
--
--   1. **Expansion (stretch)**
--
--      $$\operatorname{str}(f)=\sup_{x,y\in W,\ x\ne y}\frac{\|f(x)-f(y)\|_1}{\operatorname{ed}(x,y)}.$$
--
--   2. **Contraction**
--
--      $$\operatorname{con}(f)=\sup_{x,y\in W,\ x\ne y}\frac{\operatorname{ed}(x,y)}{\|f(x)-f(y)\|_1}.$$
--
--   The distortion of $f$ is by definition the product $\operatorname{str}(f)\operatorname{con}(f)$, and the least $\ell_1$ distortion $c_1(W)$ is the infimum of the distortion over injective maps $f$. Splitting the distortion into these two factors lets a lower bound for $c_1(W)$ be proved by normalisation: for injective $f$ and all $x,y\in W$ one has $\|f(x)-f(y)\|_1\le\operatorname{str}(f)\operatorname{ed}(x,y)$ and $\operatorname{ed}(x,y)\le\operatorname{con}(f)\|f(x)-f(y)\|_1$, and an averaged displacement inequality then bounds the product from below.
--
--   **Formalization Note** The Lean names are `stretch W f` and `contraction W f`, for `f : W → RealL1` with `RealL1 = lp (fun _ : ℕ => ℝ) 1`. Both are `sSup` of finite sets of real ratios; if $W$ has fewer than two elements these sets are empty and the value is $0$, and a ratio with zero denominator is $0$ by Lean's division convention, which matters only for the contraction of a non-injective $f$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/DistortionTransfer.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/DistortionTransfer.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TreeEdit mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison
import Definitions.Def_OAI_Combinatorics_TreeEdit_CyclicWords
import Definitions.Def_OAI_Combinatorics_TreeEdit_TreeArithmetic
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleTree
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleSeparation
import Definitions.Def_OAI_Combinatorics_TreeEdit_RandomCircle
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleFourier
import Definitions.Def_OAI_Combinatorics_TreeEdit_SampledSpectrum
import Definitions.Def_OAI_Combinatorics_TreeEdit_PrimeSupply
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleObstruction
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleParameters
import Definitions.Def_OAI_Combinatorics_TreeEdit_Delimiter

namespace OAI

namespace TreeEdit

universe u

attribute [local instance] Classical.propDecidable

noncomputable def stretch (W : Finset (List Bool)) (f : W → RealL1) : ℝ :=
  sSup {r : ℝ | ∃ x y : W, x ≠ y ∧ r = dist (f x) (f y) / (ed x.val y.val : ℝ)}

noncomputable def contraction (W : Finset (List Bool)) (f : W → RealL1) : ℝ :=
  sSup {r : ℝ | ∃ x y : W, x ≠ y ∧ r = (ed x.val y.val : ℝ) / dist (f x) (f y)}

end TreeEdit

end OAI


