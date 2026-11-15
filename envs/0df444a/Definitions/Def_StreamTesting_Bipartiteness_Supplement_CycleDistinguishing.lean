-- Prove2me | Definitions.Def_StreamTesting_Bipartiteness_Supplement_CycleDistinguishing
-- name    : StreamTesting_Bipartiteness_Supplement_CycleDistinguishing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T03:57:37.195222+00:00
-- url     : https://prove2.me/theorems/ec669159-a448-4a85-9289-b220290d094d
-- title:
--   Fixed-order cycle-promise distinguishing correctness
-- statement:
--   A cycle distinguisher accepts the long-cycle case and rejects the six-cycle-union case with success at least $2/3$:
--
--   $$G\cong C_n\Rightarrow\Pr[\mathrm{accept}]\ge2/3,\qquad G\cong\bigsqcup_{a=1}^{n/6}C_6\Rightarrow\Pr[\mathrm{accept}]\le1/3.$$
--
--   These inequalities hold for every labeling and each fixed stream order, averaging private coins only. There is no condition on other graphs. Boolean true denotes the long-cycle verdict.
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026), citation basis published; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; Theorem 11, printed/PDF p.15, proof pp.16–19.

import Definitions.Def_StreamTesting_Bipartiteness_Supplement_CyclePromise
import Definitions.Def_StreamTesting_Bipartiteness_Supplement_FixedAcceptance

noncomputable section

namespace StreamTesting.Bipartiteness.Supplement

def CycleDistinguisher {n : ℕ} (μ : RandomPolicy n) : Prop :=
  ∀ G : SimpleGraph (Fin n), ∀ σ : Order n,
    (IsLongCycle G → (2 : ℝ) / 3 ≤ fixedAcceptProb G μ σ) ∧
    (IsSixCycleUnion G → fixedAcceptProb G μ σ ≤ (1 : ℝ) / 3)

end StreamTesting.Bipartiteness.Supplement


