-- Prove2me | Definitions.Def_QPSpinParisi_qOv
-- name    : QPSpinParisi_qOv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:00:43.809589+00:00
-- url     : https://prove2.me/theorems/0c2187a1-5968-4036-8993-ab084d335bd9
-- title:
--   The overlap $q(s,t)$, (3.2)
-- statement:
--   For $s,t\in(S^2)^n$, the scalar overlap is
--   $$q(s,t)=\operatorname{Tr}R(s,t)=\frac1n\sum_{i=1}^ns_i\cdot t_i.$$
--   It is $1$ at $s=t$, and the covariance of the comparison field $Y_n$ is a function of it.
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), (3.2), p.11 (PDF p.11)

import Mathlib
import Definitions.Def_RGGDetect_unifSphere

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- The scalar overlap `q(s,t) = Tr R(s,t) = (1/n) ∑_i s_i · t_i` (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), (3.2), p.11, PDF p.11). -/
noncomputable def qOv {n : ℕ} (s t : RGGDetect.Config n 3) : ℝ :=
  (∑ i : Fin n, RGGDetect.ip (s i) (t i)) / n

end QPSpinParisi


