-- Prove2me | Definitions.Def_QPSpinParisi_IsMinB
-- name    : QPSpinParisi_IsMinB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:18:57.510682+00:00
-- url     : https://prove2.me/theorems/b9ebe12e-eab2-49f2-b4ce-491af28650b1
-- title:
--   $\alpha$ minimizes $P_{\xi,\beta}$ on $\mathcal M$
-- statement:
--   The predicate that $\alpha\in\mathcal M$ and $P_{\xi,\beta}(\alpha)\le P_{\xi,\beta}(\alpha')$ for every $\alpha'\in\mathcal M$. By Lemma 3.5 exactly one such $\alpha$ exists, written $\alpha_{\xi,\beta}$.
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), Lemma 3.5, p.17 (PDF p.17)

import Mathlib
import Definitions.Def_QPSpinParisi_PfB
import Definitions.Def_QPSpinParisi_MSet

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- `α` minimizes `P_{ξ,β}` over `M` (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), Lemma 3.5, p.17, PDF p.17). -/
def IsMinB {c : ℕ → ℝ} (W : BrownianNoise c) (β : ℝ) (α : Icc (0 : ℝ) 1 → ℝ) : Prop :=
  α ∈ MSet ∧ ∀ α' ∈ MSet, PfB W β α ≤ PfB W β α'

end QPSpinParisi


