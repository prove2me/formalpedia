-- Prove2me | Definitions.Def_OAI_Combinatorics_FiniteCircle_Distortion
-- name    : OAI_Combinatorics_FiniteCircle_Distortion
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T13:00:22.315531+00:00
-- url     : https://prove2.me/theorems/7bd819cf-95c0-4837-99eb-52e1de150a5d
-- title:
--   Expansion and contraction ratios of an embedding into $\ell^1$, and finite vectors as $\ell^1$ sequences
-- statement:
--   Let $\ell^1=\ell^1(\mathbb{N})$ be the Banach space of real sequences $u=(u_n)_{n\ge0}$ with $\|u\|=\sum_n|u_n|<\infty$. Let $X$ be a set of indices, $\mathrm{word}:X\to\alpha^{\ast}$ an assignment of finite words over an alphabet $\alpha$, $\operatorname{ed}$ the edit distance (fewest insertions, deletions and substitutions), and $f:X\to\ell^1$ a map.
--
--   1. **Expansion ratios.**
--   $$
--   U(f)=\Bigl\{\frac{\|f(x)-f(y)\|}{\operatorname{ed}(\mathrm{word}(x),\mathrm{word}(y))}\ :\ x,y\in X,\ x\ne y\Bigr\}.
--   $$
--   2. **Contraction ratios.**
--   $$
--   L(f)=\Bigl\{\frac{\operatorname{ed}(\mathrm{word}(x),\mathrm{word}(y))}{\|f(x)-f(y)\|}\ :\ x,y\in X,\ x\ne y\Bigr\}.
--   $$
--   The distortion of $f$ is $\sup U(f)\cdot\sup L(f)$, the product of the largest expansion and the largest contraction.
--   3. **Finite vectors as sequences.** For $M\in\mathbb{N}$ and $v\in\mathbb{R}^M$, the sequence $(v_0,\dots,v_{M-1},0,0,\dots)\in\ell^1$; its norm is $\sum_{i<M}|v_i|$.
--
--   Naming the two ratio sets makes it possible to bound each supremum separately; for a finite index set both are finite sets of reals. The finite-vector map turns embeddings into $\mathbb{R}^M$ with the $\ell^1$ norm, such as the histogram embeddings of the upper bound, into $\ell^1(\mathbb{N})$-valued embeddings to which the definition of distortion applies.
--
--   **Formalization Note** `upperRates word f` and `lowerRates word f` are sets of reals; the quotients use Lean's convention $r/0=0$, so a pair with equal words (if `word` is not injective) contributes $0$ to the expansion ratios and a pair with $f(x)=f(y)$ contributes $0$ to the contraction ratios. `RealL1` is `lp (fun _ : ℕ => ℝ) 1`, and `finiteL1 M v` is the finite sum of the sequences `lp.single 1 i (v i)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/Distortion.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/Distortion.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FiniteCircle mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Primes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Fourier
import Definitions.Def_OAI_Combinatorics_FiniteCircle_DyadicShifts
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TreeBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Translations

namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

noncomputable def upperRates {α X : Type*} (word : X → List α) (f : X → RealL1) : Set ℝ :=
  {r | ∃ x y : X, x ≠ y ∧ r = ‖f x-f y‖/(editDistance (word x) (word y):ℝ)}
noncomputable def lowerRates {α X : Type*} (word : X → List α) (f : X → RealL1) : Set ℝ :=
  {r | ∃ x y : X, x ≠ y ∧ r = (editDistance (word x) (word y):ℝ)/‖f x-f y‖}

noncomputable def finiteL1 (M : ℕ) (v : Fin M → ℝ) : RealL1 :=
  ∑ i, lp.single 1 i.val (v i)

end FiniteCircle

end OAI


