-- Prove2me | Definitions.Def_QPSpinParisi_AX
-- name    : QPSpinParisi_AX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:07:05.153412+00:00
-- url     : https://prove2.me/theorems/11f5f7c2-9881-43ba-b203-4c482823c362
-- title:
--   The free energy $A^X_n(\beta)$
-- statement:
--   The free energy of $X_n$ at inverse temperature $\beta$:
--   $$A^X_n(\beta)=\frac1n\mathbb E\log\int_{(S^2)^n}\exp\{\beta X_n(s)\}\,\nu^{\otimes n}(ds),$$
--   where $\nu$ is the normalized surface measure on $S^2$.
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), p.11 (PDF p.11)

import Mathlib
import Definitions.Def_QPSpinParisi_Xn
import Definitions.Def_QPSpinParisi_gaussMeas

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- The free energy `A^X_n(β) = (1/n) E log ∫_{(S²)ⁿ} exp{β X_n(s)} ν^{⊗n}(ds)` (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), p.11, PDF p.11), where `ν` is
the normalized surface measure on `S²` (`RGGDetect.unifSphere 3`, `RGGDetect.prior n 3` is `ν^{⊗n}`). -/
noncomputable def AX (c : ℕ → ℝ) (n : ℕ) (β : ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∫ α, Real.log (∫ s, Real.exp (β * Xn c n α s) ∂(RGGDetect.prior n 3)) ∂(gaussMeas n)

end QPSpinParisi


