-- Prove2me | Definitions.Def_MemQueryFeas_Np
-- name    : MemQueryFeas_Np
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:32:41.974204+00:00
-- url     : https://prove2.me/theorems/4ba399ca-bbf6-42c1-9f60-f6e57ede18f7
-- title:
--   Number of phases $N_p$
-- statement:
--   Each layer-$(p-1)$ phase contains $N_p$ layer-$p$ phases, where
--   $$
--   N_p=\Big\lfloor\frac{\log(1/\varepsilon)}{2Pp\log d}\Big\rfloor ,
--   $$
--   with $\log$ the base-2 logarithm.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), §3.1, p.7 (PDF p.8)

import Mathlib

namespace MemQueryFeas

/-- **Number of layer-`p` phases `N_p`.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), §3.1, p.7 (PDF p.8): "each layer-`(p − 1)` phase
contains exactly `N_p` layer-`p` phases …, where `N_p = ⌊log(1/ϵ)/(2Pp log d)⌋`" (log is base 2,
Notations p.7).

**Formalization Note.** `⌊·⌋₊` is the floor into `ℕ` (`0` on negative values). -/
noncomputable def Np (d : ℕ) (ε : ℝ) (P p : ℕ) : ℕ :=
  ⌊Real.logb 2 (1 / ε) / (2 * P * p * Real.logb 2 d)⌋₊

end MemQueryFeas


