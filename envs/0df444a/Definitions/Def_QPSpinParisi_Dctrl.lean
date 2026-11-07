-- Prove2me | Definitions.Def_QPSpinParisi_Dctrl
-- name    : QPSpinParisi_Dctrl
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:06:27.707848+00:00
-- url     : https://prove2.me/theorems/c2813da5-fd42-4d97-910b-0023a7223bad
-- title:
--   The control class $D[s,1]$
-- statement:
--   For $0\le s<1$, $D[s,1]$ is the collection of all progressively measurable processes $u:[s,1]\to\mathbb R^3$ with respect to the Brownian filtration with
--   $$\|u(r)\|\le1\quad\text{for almost every }r.$$
--
--   **Formalization Note** The processes are indexed by all times, and only their values on $[s,1]$ are read. A process on $[s,1]$ extends by $0$, so nothing changes.
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), §2.1, p.4 (PDF p.4)

import Mathlib
import Definitions.Def_QPSpinParisi_BrownianNoise_filt
import Definitions.Def_QPSpinParisi_E3

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- The control class `D[s, 1]` (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), §2.1, p.4, PDF p.4): progressively measurable processes with respect to the
Brownian filtration, with `‖u(r)‖ ≤ 1` for almost every `r ∈ [s, 1]`.

**Formalization Note** The processes are indexed by `ℝ≥0`. `D[s,1]` depends only on `u` on `[s,1]`, and a process on `[s,1]`
extends by `0`, so progressivity on all of `ℝ≥0` changes nothing. The norm is Euclidean (`E3`). -/
def Dctrl {c : ℕ → ℝ} (W : BrownianNoise c) (s : ℝ) : Set (ℝ≥0 → W.Ω → E3) :=
  {u | IsStronglyProgressive W.filt u ∧
    ∀ᵐ ω ∂W.P, ∀ᵐ r ∂(volume.restrict (Icc s 1)), ‖u r.toNNReal ω‖ ≤ 1}

end QPSpinParisi


