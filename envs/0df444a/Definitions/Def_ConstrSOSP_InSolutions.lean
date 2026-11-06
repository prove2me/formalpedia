-- Prove2me | Definitions.Def_ConstrSOSP_InSolutions
-- name    : ConstrSOSP_InSolutions
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:01:49.089339+00:00
-- url     : https://prove2.me/theorems/fbb5e72d-e2c7-45c9-8ac9-a41e140710b7
-- title:
--   The set Solutions
-- statement:
--   $\mathrm{Solutions}=\{k\in\{1,\dots,2^n\}: C(k)<k \text{ or } (C(k)>k \text{ and } C(C(k))=C(k))\}$: the Iter solutions.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), §5.3, p.29

import Mathlib
import Definitions.Def_ConstrSOSP_Circuit_app

namespace ConstrSOSP

/-- **The set Solutions** (arXiv:2604.02285, 2 Nov 2026, §5.3, p.29: "Solutions =
{k ∈ {1, 2, …, 2ⁿ} : [C(k) < k or (C(k) > k and C(C(k)) = C(k))]}"), the Iter solutions. -/
def InSolutions (C : Circuit) (k : ℕ) : Prop :=
  1 ≤ k ∧ k ≤ 2 ^ C.n ∧ (C.app k < k ∨ (k < C.app k ∧ C.app (C.app k) = C.app k))

end ConstrSOSP


