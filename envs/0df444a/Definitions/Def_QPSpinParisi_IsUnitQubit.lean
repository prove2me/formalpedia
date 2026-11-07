-- Prove2me | Definitions.Def_QPSpinParisi_IsUnitQubit
-- name    : QPSpinParisi_IsUnitQubit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:00:28.786818+00:00
-- url     : https://prove2.me/theorems/29054fe8-eef1-4d18-98e0-085b9dbae78d
-- title:
--   A normalized one-qubit ket
-- statement:
--   A vector $f\in\mathbb C^2$ is a one-qubit pure state when $|f(0)|^2+|f(1)|^2=1$. The paper writes this as $|\langle\phi|\phi\rangle|^2=1$, which is the same condition, since $\langle\phi|\phi\rangle\ge0$.
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), §2.1, p.3 (PDF p.3)

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- `f` is a normalized one-qubit ket: `|ϕ⟩ ∈ S¹` (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), §2.1, p.3, PDF p.3).

**Formalization Note** The printed condition `|⟨ϕ|ϕ⟩|² = 1` says the same thing, since `⟨ϕ|ϕ⟩ ≥ 0`. -/
def IsUnitQubit (f : Bool → ℂ) : Prop :=
  ∑ b : Bool, ‖f b‖ ^ 2 = 1

end QPSpinParisi


