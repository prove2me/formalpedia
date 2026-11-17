-- Prove2me | Definitions.Def_DSICCompComp_Supplement_IsRevenueOptimal
-- name    : DSICCompComp_Supplement_IsRevenueOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:33:20.310132+00:00
-- url     : https://prove2.me/theorems/6f32919c-392b-46c9-a296-537b3185c092
-- title:
--   Revenue-optimal DSIC/IR mechanism $(x^*, p^*)$ on a finite support
-- statement:
--   $(x^*, p^*)$ is a **revenue-optimal DSIC/IR mechanism** if it is an optimal solution of the DSIC revenue LP: $(x^*, p^*) \in P^+(D)$ and
--
--   $$
--   \sum_{v} f(v) \sum_i p_i(v) \;\le\; \sum_{v} f(v) \sum_i p^*_i(v) \qquad \text{for all } (x, p) \in P^+(D).
--   $$
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), Theorem C.4, p.36 (pdf p.37)

import Mathlib
import Definitions.Def_DSICCompComp_Supplement_InPPlus
import Definitions.Def_DSICCompComp_Supplement_lpRevenue

namespace DSICCompComp

namespace Supplement

/-- `(x*, p*)` is a revenue-optimal DSIC/IR mechanism on the finite support
(Ryu–Weinberg–Xue, *The DSIC Competition Complexity of Additive Buyers over Independent Items*, STOC 2027
submission, manuscript of Nov. 3, 2026, sha256 bf61bfdb…,
Theorem C.4, p.36 (pdf p.37)): an optimal solution of the DSIC revenue LP, i.e. `(x*, p*) ∈ P⁺(D)`
and its revenue is at least that of every `(x, p) ∈ P⁺(D)`. -/
def IsRevenueOptimal {n m : ℕ} (E : FiniteSetting n m) (sol : LPSolution E) : Prop :=
  InPPlus E sol ∧ ∀ sol' : LPSolution E, InPPlus E sol' → lpRevenue E sol' ≤ lpRevenue E sol

end Supplement

end DSICCompComp


