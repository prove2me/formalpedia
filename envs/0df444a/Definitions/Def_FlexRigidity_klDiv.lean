-- Prove2me | Definitions.Def_FlexRigidity_klDiv
-- name    : FlexRigidity_klDiv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:14:54.142312+00:00
-- url     : https://prove2.me/theorems/f2304e8e-311c-4f31-8c3f-9d6ae2f6c608
-- title:
--   Kullback–Leibler divergence $D(Q\|P)$ (base 2)
-- statement:
--   For distributions $Q,P$ on a finite set,
--   $$D(Q\|P)=\sum_cQ(c)\log\frac{Q(c)}{P(c)},$$
--   log base 2, with value $+\infty$ if $Q(c)>0=P(c)$ for some $c$, and $0\log0=0$.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), §2.1, p. 17

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

open Classical in
/-- **Kullback–Leibler divergence** (Arqand–Kundu–Tan, *Flexible rigidity*, arXiv:2610.00444,
artifact sha256 8c67699d…, §2.1, p. 17): `D(Q‖P) = Σ_c Q(c) log(Q(c)/P(c))`, log base 2, with value
`+∞` if `Q(c) > 0 = P(c)` for some `c`.

**Formalization Note** Terms with `Q(c) = 0` vanish (`0 · log(…) = 0`), the usual `0 log 0 = 0`
convention. Values in `EReal`. -/
def klDiv {C : Type} [Fintype C] (Q P : C → ℝ) : EReal :=
  if ∃ c, 0 < Q c ∧ P c = 0 then ⊤ else ((∑ c, Q c * Real.logb 2 (Q c / P c) : ℝ) : EReal)

end FlexRigidity


