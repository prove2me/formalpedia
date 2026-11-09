-- Prove2me | Definitions.Def_OnlinePerceptronIsolation_Binary_Uniqueness
-- name    : OnlinePerceptronIsolation_Binary_Uniqueness
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:54:05.75047+00:00
-- url     : https://prove2.me/theorems/c79b1cd2-6db9-42ed-ac3f-ebbda3caad97
-- title:
--   Signed Gaussian score and unique signing event
-- statement:
--   Given columns $Y_1,\ldots,Y_r\in\mathbb R^m$ and a signing $z\in\{-1,+1\}^r$, set
--   $$S(Y,z)=\frac1{\sqrt r}\sum_{i=1}^r z_iY_i.$$
--   For a measurable sign map $\phi:\mathbb R^m\to\{-1,+1\}$ and threshold $\theta\in\mathbb R^m$, let $z_i=\phi(Y_i)$. The event $U_{\phi,\theta}$ says that this $z$ is feasible, $S(Y,z)\ge\theta$ coordinatewise, and that every feasible signing equals $z$. The sign-cube condition is explicit, so invalid real outputs do not count. This event is the finite-dimensional target of the uniqueness estimates. Its probability uses the actual independent Gaussian columns, not an arbitrary input law. The score is total at $r=0$, while every estimate has $r\ge2$ or $r\ge3$.
-- source:
--   Shuangping Li, Gabe Schoenbach, STOC 2027 submission #485 (October 2026), Definition 3.5, Eq. (3.7), printed p.9, PDF p.11; Eq. (3.9), printed p.10, PDF p.12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/485.pdf

import Mathlib
import Definitions.Def_OnlinePerceptronIsolation_Binary_Solutions
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace OnlinePerceptronIsolation.Binary

/-- The actual normalized signed sum of a matrix's columns, equation (3.9). -/
noncomputable def signingScore {m r : ℕ} (Y : Fin m × Fin r → ℝ)
    (z : Fin r → ℝ) : Fin m → ℝ :=
  fun j => (∑ i : Fin r, z i * Y (j, i)) / Real.sqrt r

/-- Definition 3.5: feasibility and uniqueness among the ENTIRE sign cube. -/
def uniquenessEvent {m r : ℕ} (ϕ : (Fin m → ℝ) → ℝ) (θ : Fin m → ℝ) :
    Set (Fin m × Fin r → ℝ) :=
  {Y | let z := fun i => ϕ (fun j => Y (j, i))
       IsSigning z ∧ θ ≤ signingScore Y z ∧
         ∀ z' : Fin r → ℝ, IsSigning z' → θ ≤ signingScore Y z' → z' = z}

end OnlinePerceptronIsolation.Binary


