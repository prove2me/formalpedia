-- Prove2me | Definitions.Def_QPSpinParisi_alStieltjes
-- name    : QPSpinParisi_alStieltjes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:01:56.784336+00:00
-- url     : https://prove2.me/theorems/9b850041-7fcf-43fb-a8f8-75d9443ae39c
-- title:
--   The Stieltjes function of $\alpha\in\mathcal M$
-- statement:
--   The extension of $\alpha\in\mathcal M$ to $\mathbb R$, constant outside $[0,1]$, as a Stieltjes function. Its measure is the $d\alpha$ of (3.28). On $(0,1]$ this measure has the atom $1-\alpha(1^-)$ at $1$. A possible atom at $0$ does not matter, since (3.28) integrates $\xi$ and $\xi(0)=0$.
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), (3.28), p.21 (PDF p.21)

import Mathlib
import Definitions.Def_QPSpinParisi_MSet

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- The Stieltjes function of `α ∈ M`, extended constantly outside `[0,1]`, whose measure is the `dα` of (3.28)
(Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), (3.28), p.21, PDF p.21).

**Formalization Note** On `Ioc 0 1` its measure has the atom `1 - α(1-)` at `1`. A possible atom at `0` does not matter in
(3.28), since `ξ(0) = 0`. -/
noncomputable def alStieltjes (α : Icc (0 : ℝ) 1 → ℝ) (hα : α ∈ MSet) : StieltjesFunction ℝ where
  toFun := fun t => α (projIcc 0 1 zero_le_one t)
  mono' := hα.1.comp (monotone_projIcc _)
  right_continuous' x :=
    (continuousWithinAt_Ioi_iff_Ici.1 (hα.2.2.1 _)).comp continuous_projIcc.continuousWithinAt
      (fun _ hy => mem_Ici.2 (monotone_projIcc _ (mem_Ici.1 hy)))

end QPSpinParisi


