-- Prove2me | Definitions.Def_TractableComposite_phiAt
-- name    : TractableComposite_phiAt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:50:59.621976+00:00
-- url     : https://prove2.me/theorems/a8374cc2-8936-44f0-a4d2-a1839f879be3
-- title:
--   Ticked oracle query of $\phi$
-- statement:
--   Charges one tick and returns $\phi(x)$. The paper counts the evaluation of (15), which needs $dn+1$ values of $\phi$, as $O(dn)$ operations, so a value of $\phi$ costs $O(1)$: oracle access.
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), (15), p.11, and Corollary 1, p.12

import Mathlib
import Definitions.Def_LNTopology_Hermetization_tick

namespace TractableComposite

/-- **Ticked oracle query of the outer-function.** `phiAt φ x` charges one tick and returns `φ(x)`.
He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), (15), p.11 (the `dn + 1` values `φ(𝒱·ₙ(π,k))`), Corollary 1, p.12.

**Formalization Note.** Reading R3: the paper counts the evaluation of (15) as `O(dn)` operations although
it needs `dn + 1` values of `φ`, so a value of `φ` costs `O(1)` (oracle access). -/
noncomputable def phiAt {d : ℕ} (φ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : StateM ℕ ℝ := do
  LNTopology.Hermetization.tick 1
  pure (φ x)

end TractableComposite


