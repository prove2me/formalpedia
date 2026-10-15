-- Prove2me | Definitions.Def_OAI_Combinatorics_PerfectMatching_Calculus
-- name    : OAI_Combinatorics_PerfectMatching_Calculus
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T00:45:57.02618+00:00
-- url     : https://prove2.me/theorems/cd32cb0a-1254-4082-a3a8-3c9dd0162bdd
-- title:
--   Entropy derivative along a line and the barrier $h-8m(1-e^{-h/m})$
-- statement:
--   Let $I$ be a finite index set and $H(z)=\sum_{i\in I}-z_i\log z_i$ the entropy of a real vector $z\in\mathbb{R}^I$, with $0\log0=0$.
--
--   1. *Entropy derivative along a line.* For $x,v\in\mathbb{R}^I$ and $t\in\mathbb{R}$ put
--   $$
--   D_{x,v}(t)=-\sum_{i\in I}v_i\log\big(x_i+t v_i\big)-\sum_{i\in I}v_i .
--   $$
--   This is the derivative of $t\mapsto H(x+tv)$ at every $t$ such that $x_i+tv_i>0$ for each $i$ with $v_i\neq0$. Coordinates with $v_i=0$ do not move and contribute nothing.
--   2. *The nonlinear entropy barrier.* For parameters $m$ and $h$,
--   $$
--   \Phi_m(h)=h-8m\big(1-e^{-h/m}\big).
--   $$
--   3. *Its derivative in $h$.* For $m\neq0$,
--   $$
--   \Phi_m'(h)=1-8e^{-h/m}.
--   $$
--
--   The barrier encodes the main comparison between the entropy $h=H(y)$ of an edge marginal $y$ of perfect matchings on $2m$ vertices and the largest entropy $H_{\max}$ of a law of perfect matchings with that marginal. The claimed bound $H(y)-H_{\max}\le 8m(1-e^{-H(y)/m})$ is the statement $\Phi_m(H(y))\le H_{\max}$. The line derivative is the first-order term in the variational analysis of entropy along marginal paths.
--
--   **Formalization Note** The three functions are `entropyLineD x v t`, `entropyBarrier m h` and `entropyBarrierD m h`. They are total real functions: Lean's logarithm satisfies $\log 0=0$ and $\log s=\log|s|$ for $s<0$, and $h/m=0$ when $m=0$. In the intended use $m>0$ and the arguments of the logarithm are positive.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/Calculus.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/Calculus.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MatchingEntropy mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Duality

namespace OAI

/-!
Derivatives of entropy and log-partition, and the nonlinear entropy barrier.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

/-- The explicit first derivative along a supported affine marginal path. -/
def entropyLineD {ι : Type*} [Fintype ι] (x v : ι → ℝ) (t : ℝ) : ℝ :=
  -∑ i, v i * Real.log (x i+t*v i) - ∑ i, v i

def entropyBarrier (m h : ℝ) : ℝ := h-8*m*(1-Real.exp (-h/m))
def entropyBarrierD (m h : ℝ) : ℝ := 1-8*Real.exp (-h/m)

end MatchingEntropy

end

end OAI


