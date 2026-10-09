-- Prove2me | Definitions.Def_LimitedPriceChanges_LowerBound_Hierarchy
-- name    : LimitedPriceChanges_LowerBound_Hierarchy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T16:03:36.157575+00:00
-- url     : https://prove2.me/theorems/533f3db2-6ad3-4b83-971f-84fcaf82174f
-- title:
--   Hierarchical parameter family and nearest-instance selection
-- statement:
--   Let $\mathcal H=\{\pm1\}^{m+1}$. For $\zeta\in\mathcal H$ and $\ell=0,\ldots,m$, set
--   $$\varepsilon_\ell=T^{-\ell/[2(m+1)]},\qquad z_\zeta=\frac12+\frac14\sum_{\ell=0}^{m}\zeta_\ell\varepsilon_\ell.$$
--   A nearest-instance selection $\widehat\zeta(p)$ minimizes $|z_\zeta^{-1}-p|$ over the finite set $\mathcal H$ for each price $p$.
--
--   This family supplies the alternatives in the paper's lower-bound argument. **Formalization Note** A Boolean value encodes each sign, with true representing $+1$. The selection may break ties arbitrarily, and a sorry-free local check establishes its existence. The exponent is real division.
-- source:
--   Chen, Chao and Wang, Data-Based Dynamic Pricing and Inventory Control with Censored Demand and Limited Price Changes, SSRN 2700747 (revision of 2020-02-10), p. 36, (50)–(51)

import Mathlib
import Definitions.Def_LimitedPriceChanges_LowerBound_Model

namespace LimitedPriceChanges.LowerBound

/-- A vector in the paper's H={±1}^{m+1}, encoded by bits. -/
abbrev SignVector (m : ℕ) := Fin (m + 1) → Bool

def sign (b : Bool) : ℝ := if b then 1 else -1

/-- The scale epsilon_l in (50). -/
noncomputable def eps (m T : ℕ) (l : Fin (m + 1)) : ℝ :=
  (T : ℝ) ^ (-(l.val : ℝ) / (2 * ((m : ℝ) + 1)))

/-- Parameter z_zeta in (50), with l from zero through m. -/
noncomputable def zz (m T : ℕ) (ζ : SignVector m) : ℝ :=
  1 / 2 + (1 / 4 : ℝ) * ∑ l : Fin (m + 1), sign (ζ l) * eps m T l

/-- The arg-min condition in (51), allowing every tie-breaking selection. -/
def IsNearest (m T : ℕ) (zsel : ℝ → SignVector m) : Prop :=
  ∀ p ζ, |(zz m T (zsel p))⁻¹ - p| ≤ |(zz m T ζ)⁻¹ - p|

end LimitedPriceChanges.LowerBound


