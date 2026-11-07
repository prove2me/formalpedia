-- Prove2me | Definitions.Def_QPSpinParisi_gamHat
-- name    : QPSpinParisi_gamHat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:00:35.848359+00:00
-- url     : https://prove2.me/theorems/b99dd056-9cd7-481a-9b77-3483758fe6ff
-- title:
--   The extension by $0$ of a function on $[0,1)$
-- statement:
--   The function on $\mathbb R$ that equals $\gamma$ on $[0,1)$ and $0$ elsewhere. It is a device to write the integrals over $[0,1]$ of a function defined on $[0,1)$, which do not see the point $1$.
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), §2.1, p.4 (PDF p.4)

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- The extension by `0` to `ℝ` of a function `γ` on `[0, 1)` (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), §2.1, p.4, PDF p.4), used only under integrals over
`[0, 1]`, which do not see the point `1`. -/
noncomputable def gamHat (γ : Ico (0 : ℝ) 1 → ℝ) : ℝ → ℝ :=
  fun t => if h : t ∈ Ico (0 : ℝ) 1 then γ ⟨t, h⟩ else 0

end QPSpinParisi


