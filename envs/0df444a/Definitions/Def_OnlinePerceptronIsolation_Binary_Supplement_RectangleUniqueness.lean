-- Prove2me | Definitions.Def_OnlinePerceptronIsolation_Binary_Supplement_RectangleUniqueness
-- name    : OnlinePerceptronIsolation_Binary_Supplement_RectangleUniqueness
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:09:58.161389+00:00
-- url     : https://prove2.me/theorems/0f344896-2b19-4eaf-93b3-66554741e666
-- title:
--   Definition 4.4 — uniqueness event for rectangles
-- statement:
--   Let $\phi:\mathbb R^m\to\{-1,+1\}$ be measurable, let $Y_1,\ldots,Y_r$ be independent standard Gaussian columns, and let $B\subseteq\mathbb R^m$ be any rectangle. Write
--   $$z_i=\phi(Y_i),\qquad S(Y,z)=\frac1{\sqrt r}\sum_{i=1}^rz_iY_i.$$
--   The event $U_{\phi,B}$ requires that $z$ is a signing, that $S(Y,z)\in B$, and that every signing $z'$ with $S(Y,z')\in B$ equals $z$. The normalized sum is the published signingScore. Uniqueness ranges over the entire sign cube, without a stability or algorithmic restriction.
-- source:
--   Shuangping Li, Gabe Schoenbach, STOC 2027 submission #485 (October 2026), Definition 4.4, Eq. (4.33), printed p. 16, PDF p. 18; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/485.pdf

import Mathlib
import Definitions.Def_OnlinePerceptronIsolation_Binary_Supplement_Rectangle
import Definitions.Def_OnlinePerceptronIsolation_Binary_Uniqueness
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace OnlinePerceptronIsolation.Binary.Supplement

/-- Definition 4.4: the chosen signs are feasible and unique in the entire sign cube. -/
def rectangleUniquenessEvent {m r : ℕ} (ϕ : (Fin m → ℝ) → ℝ) (B : Rectangle m) :
    Set (Fin m × Fin r → ℝ) :=
  {Y | let z := fun i => ϕ (fun j => Y (j, i))
       IsSigning z ∧ signingScore Y z ∈ B.carrier ∧
         ∀ z' : Fin r → ℝ, IsSigning z' → signingScore Y z' ∈ B.carrier → z' = z}

end OnlinePerceptronIsolation.Binary.Supplement


