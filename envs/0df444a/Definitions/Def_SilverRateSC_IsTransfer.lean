-- Prove2me | Definitions.Def_SilverRateSC_IsTransfer
-- name    : SilverRateSC_IsTransfer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:45:57.739455+00:00
-- url     : https://prove2.me/theorems/73182ae9-9937-43f6-800a-060859b4b099
-- title:
--   The transfer conditions (8) of a local hard function
-- statement:
--   Let $\Phi_i$ be a local hard function, $\ell_i$ its input threshold, $D_i$ the incoming excess, $h_1,\dots,h_{m_{\rm gap}}$ the gap stepsizes, $b_i$ the checkpoint stepsize, $f_j$ the contributions, and $\ell_{i+1}$ an outgoing threshold. Run the updates (9) from $(X_0,Y_0)=(\ell_i+D_i,0)$. The **transfer conditions** are
--   $$X_j\ge\ell_i,\quad 0\le Y_j\le\ell_{i+1}\quad(0\le j\le m_{\rm gap}),\qquad Y_{m_{\rm gap}+1}=\ell_{i+1}+D_{i+1},\quad D_{i+1}>0.$$
--   They say the excess above the threshold is handed to the next coordinate: the pair $(\ell_{i+1},D_{i+1})$ becomes the input of $\Phi_{i+1}$.
--
--   **Formalization Note** $D_{i+1}$ is not a free parameter: it is defined as $Y_{m_{\rm gap}+1}-\ell_{i+1}$ (the auxiliary `outExcess`), and the predicate asks it to be positive.
-- source:
--   Liu, Ye, Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case, arXiv:2609.26873 (sha256 1e325f28…), §3, (8), p.14

import Mathlib
import Definitions.Def_SilverRateSC_localIter

namespace SilverRateSC

/-- The outgoing excess `D_{i+1} := Y_{m_gap+1} − ℓ_{i+1}` of the local trajectory (9) started at
`(ℓ_i + D_i, 0)` with gap stepsizes `hs` and checkpoint stepsize `b`. -/
noncomputable def outExcess (κ : ℝ) (Φ : EuclideanSpace ℝ (Fin 2) → ℝ) (hs : List ℝ) (b : ℝ)
    (ℓ D ℓ' : ℝ) (f : ℕ → ℝ) : ℝ :=
  localIter κ Φ (hs ++ [b]) f !₂[ℓ + D, 0] (hs.length + 1) 1 - ℓ'

/-- **The transfer conditions** (8) for a local hard function `Φ_i`: starting from
`(X_0, Y_0) = (ℓ_i + D_i, 0)`, the iterations (9) with gap stepsizes `h_1, …, h_{m_gap}`
(`= hs`), checkpoint stepsize `b_i` and contributions `f_j` satisfy
`X_j ≥ ℓ_i`, `0 ≤ Y_j ≤ ℓ_{i+1}` (`0 ≤ j ≤ m_gap`), `Y_{m_gap+1} = ℓ_{i+1} + D_{i+1}`, `D_{i+1} > 0`.

Liu, Ye, *Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case*,
arXiv:2609.26873, §3, "Notation and setup", (8), pp. 13–14.

**Formalization Note** `D_{i+1}` is not a free parameter: it is defined by
`Y_{m_gap+1} = ℓ_{i+1} + D_{i+1}`, i.e. it is `outExcess κ Φ hs b ℓ D ℓ' f`, and the predicate
asks it to be positive. `ℓ` is `ℓ_i`, `D` is `D_i`, `ℓ'` is `ℓ_{i+1}`. -/
def IsTransfer (κ : ℝ) (Φ : EuclideanSpace ℝ (Fin 2) → ℝ) (hs : List ℝ) (b : ℝ)
    (ℓ D ℓ' : ℝ) (f : ℕ → ℝ) : Prop :=
  (∀ j ≤ hs.length,
      ℓ ≤ localIter κ Φ (hs ++ [b]) f !₂[ℓ + D, 0] j 0 ∧
      0 ≤ localIter κ Φ (hs ++ [b]) f !₂[ℓ + D, 0] j 1 ∧
      localIter κ Φ (hs ++ [b]) f !₂[ℓ + D, 0] j 1 ≤ ℓ') ∧
    0 < outExcess κ Φ hs b ℓ D ℓ' f

end SilverRateSC


