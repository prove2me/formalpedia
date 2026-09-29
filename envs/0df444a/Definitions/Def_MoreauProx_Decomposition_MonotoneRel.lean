-- Prove2me | Definitions.Def_MoreauProx_Decomposition_MonotoneRel
-- name    : MoreauProx_Decomposition_MonotoneRel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:10:17.595288+00:00
-- url     : https://prove2.me/theorems/e9358d32-7edd-4dad-9956-660b742886de
-- title:
--   Monotone and maximal monotone relations on a real Hilbert space
-- statement:
--   Let $H$ be a real Hilbert space and $\mathcal R$ a binary relation on $H$ (a subset of $H \times H$).
--
--   1. $\mathcal R$ is **monotone** (*monotonique*, in the sense of G. J. Minty) if
--   $$ x\,\mathcal R\,y \ \text{ and } \ x'\,\mathcal R\,y' \ \Longrightarrow\ (x - x' \mid y - y') \ge 0. $$
--   2. A monotone relation $\mathcal R$ is **maximal monotone** if it admits no strict monotone extension: every monotone relation $\mathcal R'$ with $\mathcal R \subseteq \mathcal R'$ satisfies $\mathcal R' \subseteq \mathcal R$.
--
--   Maximal monotone relations are the setting of Minty's theorem, which Moreau compares with his decomposition theorem in §12.
-- source:
--   Moreau, Proximité et dualité dans un espace hilbertien, Bull. Soc. Math. France 93 (1965), p. 296, §12.a

import Mathlib

namespace MoreauProx.Decomposition

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A binary relation `R` on `H` is monotone (« monotonique », Moreau 1965, 12.a, p. 296) if
`x R y` and `x' R y'` imply `(x − x' | y − y') ≥ 0`. -/
def IsMonotoneRel (R : H → H → Prop) : Prop :=
  ∀ x y x' y', R x y → R x' y' → 0 ≤ ⟪x - x', y - y'⟫_ℝ

/-- A monotone relation is maximal (Moreau 1965, 12.a, p. 296) if it has no strict monotone
extension: every monotone relation containing `R` is contained in `R`. -/
def IsMaximalMonotoneRel (R : H → H → Prop) : Prop :=
  IsMonotoneRel R ∧
    ∀ R' : H → H → Prop, IsMonotoneRel R' → (∀ x y, R x y → R' x y) → ∀ x y, R' x y → R x y

end MoreauProx.Decomposition


