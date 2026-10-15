-- Prove2me | Definitions.Def_OAI_Combinatorics_Sensitivity_HammingBase
-- name    : OAI_Combinatorics_Sensitivity_HammingBase
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:19:30.502976+00:00
-- url     : https://prove2.me/theorems/a3097a5f-bd37-4093-ad82-33b23ca261de
-- title:
--   Unions of equal-radius Hamming balls as Boolean predicates
-- statement:
--   Let $I$ be a finite set of coordinates and identify Boolean values with $\{0,1\}$. For $x, y \in \{0,1\}^I$ let $d_H(x,y) = |\{ i \in I : x_i \ne y_i \}|$ be the Hamming distance. Given a finite index set $C$, centers $(z_c)_{c \in C}$ in $\{0,1\}^I$ and a radius $R \in \mathbb{N}$, the ball predicate accepts exactly the points of the union of the Hamming balls of radius $R$ around the centers:
--
--   $$
--   \mathrm{Ball}_{z,R}(x) = 1 \iff \exists\, c \in C:\ d_H(x, z_c) \le R .
--   $$
--
--   A larger radius accepts more inputs, so radii that decrease with an index produce a nested family of predicates. When the centers are far apart, a ball predicate has small sensitivity on the inputs it rejects, which makes such predicates suitable as the initial family in the recursive construction separating block sensitivity from sensitivity.
--
--   **Formalization Note** The predicate is `ballPredicate centers R x : Bool`, defined with `decide`, and the distance is Mathlib's `hammingDist`. Both the coordinate type and the center index type are finite types.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity/HammingBase.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Sensitivity/HammingBase.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SensitivitySeparation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SensitivitySeparation

namespace OAI

/-! Hamming balls used by the initial nested predicates. -/

noncomputable section
open scoped Classical

namespace Paper320

variable {I C : Type} [Fintype I]

/-- The union of equal-radius Hamming balls. -/
def ballPredicate [Fintype C] (centers : C → I → Bool) (R : ℕ)
    (x : I → Bool) : Bool :=
  decide (∃ c, hammingDist x (centers c) ≤ R)

end Paper320

end

end OAI


