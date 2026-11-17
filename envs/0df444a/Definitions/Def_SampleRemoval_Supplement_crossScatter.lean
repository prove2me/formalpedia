-- Prove2me | Definitions.Def_SampleRemoval_Supplement_crossScatter
-- name    : SampleRemoval_Supplement_crossScatter
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:18:29.086755+00:00
-- url     : https://prove2.me/theorems/75cdf9db-1097-411e-b8a9-78ca910b503d
-- title:
--   Simple-regression cross-scatter $F(S)$
-- statement:
--   For retained planar observations $S$, the **cross-scatter** is
--
--   $$F(S)=\sum_{i\in S}x_iy_i-\frac{(\sum_{i\in S}x_i)(\sum_{i\in S}y_i)}{|S|}.$$
--
--   Whenever the simple-regression slope is defined, its sign is the sign of $F(S)$. All theorem uses have $|S|\ge2$.
-- source:
--   Xu, Gao, Hu, Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares, STOC 2027 submission (manuscript sha256 dcd33acebc1ccdc626c7ee41bfabc29795abe2e1cd9267d8cbd66d98f81c4b26), Sections 2 and 5, pp.3,8 (PDF pp.5,10)

import Mathlib

set_option autoImplicit false

namespace SampleRemoval.Supplement

/-- The simple-regression cross-scatter `F(S) = Σ_S xᵢyᵢ - (Σ_S xᵢ)(Σ_S yᵢ)/|S|`
(Xu, Gao, Hu, STOC 2027 submission, eq. (1), p.4 (PDF p.6)). At `S=∅` all sums vanish,
so the total real division convention also gives zero; every theorem uses sets of size at least two. -/
noncomputable def crossScatter {n : ℕ} (p : Fin n → ℝ × ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ i ∈ S, (p i).1 * (p i).2 -
    ((∑ i ∈ S, (p i).1) * (∑ i ∈ S, (p i).2)) / (S.card : ℝ)

end SampleRemoval.Supplement


