-- Prove2me | Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
-- name    : OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:17:48.817139+00:00
-- url     : https://prove2.me/theorems/7a6de7d1-83bc-45e0-ba91-0c08c3756334
-- title:
--   Iterated differences of $1/x$ via lists of shifted reciprocal products
-- statement:
--   All lists below are finite lists of real numbers.
--
--   1. **Reciprocal product.** For a list $\mathbf a=(a_1,\dots,a_m)$ and $x\in\mathbb{R}$,
--
--      $$P_{\mathbf a}(x)=\prod_{j=1}^{m}\frac{1}{x+a_j},$$
--
--      so that $P_{\varnothing}(x)=1$ and $P_{(a,a_1,\dots,a_m)}(x)=\frac{1}{x+a}\,P_{(a_1,\dots,a_m)}(x)$.
--
--   2. **Difference expansion.** For $h\in\mathbb{R}$ and $\mathbf a=(a_1,\dots,a_m)$, $E_h(\mathbf a)$ is the list of $m$ lists whose $i$-th member ($1\le i\le m$) is
--
--      $$\bigl(a_1,\dots,a_{i-1},\,a_i,\,a_i+h,\,a_{i+1}+h,\dots,a_m+h\bigr),$$
--
--      a list of length $m+1$. Thus $E_h(\varnothing)$ is empty, and $E_h(\mathbf a)$ always has exactly $m$ members.
--
--   3. **Iterated differences.** For $\mathbf h=(h_1,\dots,h_k)$ and $f:\mathbb{R}\to\mathbb{R}$, set $\Delta_{\varnothing}f=f$ and
--
--      $$(\Delta_{(h_1,\dots,h_k)}f)(x)=(\Delta_{(h_2,\dots,h_k)}f)(x)-(\Delta_{(h_2,\dots,h_k)}f)(x+h_1),$$
--
--      so that $\Delta_{\mathbf h}=\Delta_{h_1}\circ\cdots\circ\Delta_{h_k}$ with $(\Delta_h g)(x)=g(x)-g(x+h)$.
--
--   4. **Reciprocal terms.** The list of lists $T(\mathbf h)$ is defined by $T(\varnothing)=\bigl((0)\bigr)$, a single list whose only entry is $0$, and $T(h_1,h_2,\dots,h_k)$ is the concatenation, in order, of the lists $E_{h_1}(\mathbf a)$ over all members $\mathbf a$ of $T(h_2,\dots,h_k)$.
--
--   The expansion $E_h$ encodes the telescoping identity $P_{\mathbf a}(x)-P_{\mathbf a}(x+h)=h\sum_{\mathbf b\in E_h(\mathbf a)}P_{\mathbf b}(x)$, valid when all the factors $x+a_j$ and $x+a_j+h$ are nonzero. Iterating it gives, for $x>0$ and all $h_i\ge 0$,
--
--   $$\Delta_{\mathbf h}\Bigl(\frac1x\Bigr)=h_1h_2\cdots h_k\sum_{\mathbf a\in T(\mathbf h)}P_{\mathbf a}(x),$$
--
--   where $T(\mathbf h)$ consists of $k!$ lists of length $k+1$ with entries in $[0,h_1+\dots+h_k]$. In the surrounding development this yields the two-sided bounds $k!\,h_1\cdots h_k\,V^{-(k+1)}\le\Delta_{\mathbf h}(1/x)\le k!\,h_1\cdots h_k\,U^{-(k+1)}$ whenever all $h_i\ge 0$, $0<U\le x$ and $x+h_1+\dots+h_k\le V$, which control the phase $Z/n$ after repeated van der Corput differencing.
--
--   **Formalization Note** The Lean names are `reciprocalProduct` (with the simp lemmas `reciprocalProduct_nil` and `reciprocalProduct_cons`), `expandDifference` (with `expandDifference_length`), `backwardDifferences` and `reciprocalTerms`. In `reciprocalProduct` a factor with x + a = 0 equals 0, by Lean's convention for division by zero.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/ReciprocalDifferences.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/ReciprocalDifferences.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ShortEgyptianFractions mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative

namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

noncomputable def reciprocalProduct (as : List ℝ) (x : ℝ) : ℝ :=
  (as.map (fun a => 1 / (x + a))).prod

@[simp] theorem reciprocalProduct_nil (x : ℝ) : reciprocalProduct [] x = 1 := rfl
@[simp] theorem reciprocalProduct_cons (a : ℝ) (as : List ℝ) (x : ℝ) :
    reciprocalProduct (a :: as) x = 1 / (x + a) * reciprocalProduct as x := rfl

def expandDifference (h : ℝ) : List ℝ → List (List ℝ)
  | [] => []
  | a :: as => (a :: (a + h) :: as.map (· + h)) ::
      (expandDifference h as).map (a :: ·)

@[simp] theorem expandDifference_length (h : ℝ) (as : List ℝ) :
    (expandDifference h as).length = as.length := by
  induction as with
  | nil => rfl
  | cons a as ih => simpa only [expandDifference, List.length_cons, List.length_map] using congrArg (· + 1) ih

def backwardDifferences : List ℝ → (ℝ → ℝ) → ℝ → ℝ
  | [], f => f
  | h :: hs, f => fun x => backwardDifferences hs f x - backwardDifferences hs f (x + h)

def reciprocalTerms : List ℝ → List (List ℝ)
  | [] => [[0]]
  | h :: hs => (reciprocalTerms hs).flatMap (expandDifference h)

end ShortEgyptian

end OAI


