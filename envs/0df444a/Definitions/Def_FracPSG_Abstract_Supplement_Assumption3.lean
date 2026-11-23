-- Prove2me | Definitions.Def_FracPSG_Abstract_Supplement_Assumption3
-- name    : FracPSG_Abstract_Supplement_Assumption3
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T05:56:38.526277+00:00
-- url     : https://prove2.me/theorems/87a3d59d-a56b-42b9-9ea9-56432d62944a
-- title:
--   Assumption 3 — $f^n=f^l+\iota_C$ with local Lipschitz continuity, regularity or strict differentiability (p. 13)
-- statement:
--   Consider the fractional program $\min_{x\in S} f(x)/g(x)$ with numerator $f=f^s+f^n$ (Assumption 1) and denominator $g$, and write $\operatorname{dom} f=\{x: f(x)<+\infty\}$. **Assumption 3** asks that
--   $$f^n=f^l+\iota_C,$$
--   where $C$ is a nonempty closed subset of $\mathcal H$ with $C\cap S\neq\varnothing$, and that one of the following holds:
--
--   1. $f^l$ is locally Lipschitz continuous on $\mathcal H$ and $C=S=\mathcal H$;
--   2. $f^l$ is locally Lipschitz continuous on an open set containing $S\cap\operatorname{dom} f$, both $f^l$ and $C\cap S$ are regular at every point of $S\cap\operatorname{dom} f$, and $g$ is positive on an open set containing $S\cap\operatorname{dom} f$;
--   3. $f^l$ is strictly differentiable on an open set containing $S\cap\operatorname{dom} f$, and $g$ is positive on an open set containing $S\cap\operatorname{dom} f$.
--
--   The assumption makes Lemma 3.2(ii) applicable at every point of $S\cap\operatorname{dom} f$, which turns lifted stationarity of the limits of Algorithm 1 into stationarity.
--
--   **Formalization Note** $f^l$ is extended-real-valued, as in the paper. "Locally Lipschitz continuous on an open set $O$" is: Lipschitz continuous around every point of $O$, which includes finiteness there. "Strictly differentiable on $O$" is: strictly differentiable at every point of $O$. A function is regular at $x$ in the sense of the published `FracPSG.Subseq.IsRegularAt` (finite at $x$, $\widehat\partial=\partial_L$), and a set in the sense of `IsSetRegularAt`. The identity $f^n=f^l+\iota_C$ is an equality of functions $\mathcal H\to(-\infty,+\infty]$.
-- source:
--   Boţ, Dao, Li, Extrapolated Proximal Subgradient Algorithms for Nonconvex and Nonsmooth Fractional Programs, arXiv:2003.04124v2, p. 13, Assumption 3

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_FracPSG_Subseq_Basic
import Definitions.Def_FracPSG_Subseq_EPSG
import Definitions.Def_FracPSG_Abstract_Supplement_Stationary

open Filter Topology
open scoped InnerProductSpace

namespace FracPSG.Abstract.Supplement

open NonconvexSplitting.Shared FracPSG.Subseq

/-- Assumption 3 (Boţ–Dao–Li, arXiv:2003.04124v2, p. 13) for problem (P) with numerator
`f = fˢ + fⁿ` and denominator `g`: `fⁿ = fˡ + ι_C`, where `C` is a nonempty closed set with
`C ∩ S ≠ ∅` and one of the following holds (`dom f = {x | f x < +∞}`):
(a) `fˡ` is locally Lipschitz on `H` and `C = S = H`;
(b) `fˡ` is locally Lipschitz on an open set containing `S ∩ dom f`, `fˡ` and `C ∩ S` are regular
at every point of `S ∩ dom f`, and `g` is positive on an open set containing `S ∩ dom f`;
(c) `fˡ` is strictly differentiable on an open set containing `S ∩ dom f`, and `g` is positive on an
open set containing `S ∩ dom f`. -/
def Assumption3 {N : ℕ} (S : Set (EuclideanSpace ℝ (Fin N)))
    (fs : EuclideanSpace ℝ (Fin N) → ℝ) (fn : EuclideanSpace ℝ (Fin N) → EReal)
    (g : EuclideanSpace ℝ (Fin N) → ℝ) : Prop :=
  ∃ fl : EuclideanSpace ℝ (Fin N) → EReal, ∃ C : Set (EuclideanSpace ℝ (Fin N)),
    C.Nonempty ∧ IsClosed C ∧ (C ∩ S).Nonempty ∧ fn = addInd fl C ∧
    ((∀ x, IsLipschitzAround fl x) ∧ C = Set.univ ∧ S = Set.univ ∨
     (∃ O, IsOpen O ∧ (∀ x ∈ S, objF fs fn x ≠ ⊤ → x ∈ O) ∧ ∀ x ∈ O, IsLipschitzAround fl x) ∧
       (∀ x ∈ S, objF fs fn x ≠ ⊤ → IsRegularAt fl x ∧ IsSetRegularAt (C ∩ S) x) ∧
       (∃ O, IsOpen O ∧ (∀ x ∈ S, objF fs fn x ≠ ⊤ → x ∈ O) ∧ ∀ x ∈ O, 0 < g x) ∨
     (∃ O, IsOpen O ∧ (∀ x ∈ S, objF fs fn x ≠ ⊤ → x ∈ O) ∧ ∀ x ∈ O, IsStrictlyDiffAt fl x) ∧
       (∃ O, IsOpen O ∧ (∀ x ∈ S, objF fs fn x ≠ ⊤ → x ∈ O) ∧ ∀ x ∈ O, 0 < g x))

end FracPSG.Abstract.Supplement


