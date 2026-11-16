-- Prove2me | Definitions.Def_QThermalClassical_Supplement_powerLawJ
-- name    : QThermalClassical_Supplement_powerLawJ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:39:03.014418+00:00
-- url     : https://prove2.me/theorems/873f7b51-336c-4c34-b644-fbf87276a62c
-- title:
--   Power-law couplings $J_{x,y}=(1+\|x-y\|_2)^{-\alpha}$
-- statement:
--   On the lattice $\Lambda_L=\{1,\dots,L\}^D$, the couplings of Theorem 35's power-law bullet: $J_{x,x}=0$ and, for $x\neq y$,
--   $$
--   J_{x,y}=\frac{1}{(1+\|x-y\|_2)^{\alpha}},
--   $$
--   with $\|\cdot\|_2$ the Euclidean norm.
--
--   **Formalization Note** Coordinates are $0,\dots,L-1$, which leaves every difference unchanged; $\alpha$ is any real number.
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), Theorem 35, power-law bullet, p.84

import Mathlib

set_option autoImplicit false

namespace QThermalClassical.Supplement

/-- The power-law couplings of Theorem 35's third bullet on the lattice `Λ_L = {1, …, L}^D`
(as `Fin D → Fin L`): `J_{x,x} = 0` and `J_{x,y} = 1 / (1 + ‖x − y‖₂)^α` for `x ≠ y`, with
`‖·‖₂` the Euclidean norm of the coordinate difference.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), Theorem 35, power-law bullet, p.84.

**Formalization Note.** Coordinates are `0, …, L − 1` instead of `1, …, L`, which leaves every
difference unchanged. `α` is any real number; the power is `Real.rpow` of a base `≥ 1`. -/
noncomputable def powerLawJ (D L : ℕ) (α : ℝ) : (Fin D → Fin L) → (Fin D → Fin L) → ℝ :=
  fun x y => if x = y then 0 else
    (1 + Real.sqrt (∑ i, (((x i : ℕ) : ℝ) - ((y i : ℕ) : ℝ)) ^ 2)) ^ (-α)

end QThermalClassical.Supplement


