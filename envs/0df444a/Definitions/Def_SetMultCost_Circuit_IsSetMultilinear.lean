-- Prove2me | Definitions.Def_SetMultCost_Circuit_IsSetMultilinear
-- name    : SetMultCost_Circuit_IsSetMultilinear
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:53:44.462092+00:00
-- url     : https://prove2.me/theorems/9255fe35-1ad8-40e9-86d8-99216263bce4
-- title:
--   Set-multilinear circuit
-- statement:
--   A circuit is **set-multilinear** when the polynomial computed at every node is set-multilinear with respect to some subset of the parts.
--
--   This is a condition on values at nodes, as on the page, not on the syntax of the gates.
-- source:
--   Behera, Forbes, Saptharishi, Tavenas, On the Cost of Set-Multilinearisation in Positive Characteristic, STOC 2027 submission (manuscript sha256 841308db…), §2, p.8

import Mathlib
import Definitions.Def_SetMultCost_Circuit
import Definitions.Def_SetMultCost_IsSetMultilinearOn

namespace SetMultCost

/-- **Set-multilinear circuit.** Behera, Forbes, Saptharishi, Tavenas, *On the Cost of Set-Multilinearisation in Positive
Characteristic*, STOC 2027 submission (manuscript sha256 841308db…), §2, p.8: "A circuit is said to be a set-multilinear circuit
if the polynomial computed at every node is a set-multilinear polynomial with respect to a subset
of the d parts." -/
def Circuit.IsSetMultilinear {σ ι F : Type*} [CommRing F] [DecidableEq ι] (Φ : Circuit σ F)
    (part : σ → ι) : Prop :=
  ∀ v, ∃ T : Finset ι, IsSetMultilinearOn part T (Φ.nodeValue v)

end SetMultCost


