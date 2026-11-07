-- Prove2me | Definitions.Def_QPSpinParisi_alHat
-- name    : QPSpinParisi_alHat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:00:32.759209+00:00
-- url     : https://prove2.me/theorems/59ca773c-65aa-4614-8405-58366ca75b89
-- title:
--   The extension by $0$ of a function on $[0,1]$
-- statement:
--   The function on $\mathbb R$ that equals $\alpha$ on $[0,1]$ and $0$ elsewhere, used for integrals over $[0,1]$.
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), (3.15), p.17 (PDF p.17)

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- The extension by `0` to `ℝ` of a function `α` on `[0, 1]` (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), (3.15), p.17, PDF p.17), used only under integrals over
`[0, 1]`. -/
noncomputable def alHat (α : Icc (0 : ℝ) 1 → ℝ) : ℝ → ℝ :=
  fun t => if h : t ∈ Icc (0 : ℝ) 1 then α ⟨t, h⟩ else 0

end QPSpinParisi


