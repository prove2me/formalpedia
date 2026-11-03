-- Prove2me | Definitions.Def_FreeOrderEPTAS_OPT
-- name    : FreeOrderEPTAS_OPT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:25:24.121564+00:00
-- url     : https://prove2.me/theorems/49fab13b-ae5a-43c6-94d5-b8e7b05d4167
-- title:
--   The optimum $\mathrm{OPT}$
-- statement:
--   $$\mathrm{OPT}=\max_{\sigma\in S_n}V(\sigma)=V(\sigma^*).$$
--   This is the benchmark of Theorem 3.1. The paper reduces adaptive inspection orders to permutations through Hill's theorem, which is not used here: the benchmark is the maximum over permutations, as on p.17.
--
--   **Formalization Note** A finite maximum over `Equiv.Perm (Fin n)`, which is nonempty also for $n=0$.
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, p.17

import Mathlib
import Definitions.Def_FreeOrderEPTAS_V

namespace FreeOrderEPTAS

/-- `OPT = V(σ*)` (arXiv:2007.13121v3, p.17): the maximum of `V` over all permutations. Adaptive
orders are not considered; the paper reduces to permutations through Hill's theorem. -/
noncomputable def OPT {n : ℕ} (I : Instance n) : ℝ :=
  (Finset.univ : Finset (Equiv.Perm (Fin n))).sup' Finset.univ_nonempty (V I)

end FreeOrderEPTAS


