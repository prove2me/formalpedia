-- Prove2me | Definitions.Def_DSICCompComp_Supplement_virtualWelfare
-- name    : DSICCompComp_Supplement_virtualWelfare
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:29:33.747188+00:00
-- url     : https://prove2.me/theorems/c9b7d884-eae1-4da6-812c-bc7fe0ef1e7d
-- title:
--   Virtual welfare $\mathbb E[\sum_i x_i(v)\cdot\Phi^\lambda_i(v)]$
-- statement:
--   The virtual welfare of an allocation $x$ with respect to the virtual value function $\Phi^\lambda$ is
--
--   $$
--   \mathbb E\Big[\sum_i x_i(v)\cdot \Phi^\lambda_i(v)\Big] \;=\; \sum_{v \in \mathrm{supp}(D)} f(v) \sum_{i=1}^n \sum_{j=1}^m x_{ij}(v)\, \Phi^\lambda_{ij}(v).
--   $$
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), Theorem C.4, p.36 (pdf p.37)

import Mathlib
import Definitions.Def_DSICCompComp_Supplement_LPSolution
import Definitions.Def_DSICCompComp_Supplement_virtualValue

namespace DSICCompComp

namespace Supplement

/-- The virtual welfare of an allocation `x` with respect to `Φ^λ` (Ryu–Weinberg–Xue, *The DSIC Competition Complexity of Additive Buyers over Independent Items*, STOC 2027
submission, manuscript of Nov. 3, 2026, sha256 bf61bfdb…,
Theorem C.4, p.36 (pdf p.37)):
`E[∑_i x_i(v)·Φ^λ_i(v)] = ∑_{v ∈ supp(D)} f(v) · ∑_i ∑_j x_ij(v)·Φ^λ_ij(v)`.

**Formalization Note** It depends only on the allocation part `sol.x` of `sol`. -/
noncomputable def virtualWelfare {n m : ℕ} (E : FiniteSetting n m)
    (lam : (i : Fin n) → ((k : Fin n) → E.S k) → Option (E.S i) → ℝ) (sol : LPSolution E) : ℝ :=
  ∑ v : (i : Fin n) → E.S i,
    jointPMF E v * ∑ i, ∑ j, sol.x (fun k => some (v k)) i j * virtualValue E lam v i j

end Supplement

end DSICCompComp


