-- Prove2me | Definitions.Def_DSICCompComp_Supplement_virtualValue
-- name    : DSICCompComp_Supplement_virtualValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:28:54.570135+00:00
-- url     : https://prove2.me/theorems/5f37077a-7425-442a-8094-de14b37eb4ac
-- title:
--   Virtual value function $\Phi^\lambda$ (Definition C.3)
-- statement:
--   For a dual solution $\lambda$, the virtual value function $\Phi^\lambda$ is defined coordinate-wise: for all bidders $i$, items $j$ and value profiles $v \in \mathrm{supp}(D)$,
--
--   $$
--   \Phi^\lambda_{ij}(v) \;:=\; v_{ij} - \frac{1}{f(v)} \sum_{v'_i \in \mathrm{supp}(D_i)} \lambda^{v_{-i}}_i(v'_i, v_i)\,\big(v'_{ij} - v_{ij}\big).
--   $$
--
--   Note the division by the joint PMF $f(v)$, not by $f_i(v_i)$, and that the sum runs over $\mathrm{supp}(D_i)$ only.
--
--   **Formalization Note** The paper defines $\Phi^\lambda$ for flow-conserving $\lambda$; the same formula is defined here for every $\lambda$. Dual solutions are encoded as in `FlowConservation`.
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), Definition C.3, p.36 (pdf p.37)

import Mathlib
import Definitions.Def_DSICCompComp_Supplement_jointPMF

namespace DSICCompComp

namespace Supplement

/-- The virtual value function `Φ^λ` of a dual solution `λ` (Ryu–Weinberg–Xue, *The DSIC Competition Complexity of Additive Buyers over Independent Items*, STOC 2027
submission, manuscript of Nov. 3, 2026, sha256 bf61bfdb…,
Definition C.3, p.36 (pdf p.37)): for all bidders `i`, items `j` and value profiles `v`,
`Φ^λ_ij(v) := v_ij − (1/f(v)) ∑_{v'_i ∈ supp(D_i)} λ^{v_{-i}}_i(v'_i, v_i)(v'_ij − v_ij)`.

**Formalization Note** Dual solutions are encoded as in `FlowConservation`. The page defines `Φ^λ`
for flow-conserving `λ`; the same formula is defined here for every `λ` and used only with
flow-conserving ones. `f(v) > 0` on `supp(D)`, so the division is genuine. -/
noncomputable def virtualValue {n m : ℕ} (E : FiniteSetting n m)
    (lam : (i : Fin n) → ((k : Fin n) → E.S k) → Option (E.S i) → ℝ)
    (v : (k : Fin n) → E.S k) (i : Fin n) (j : Fin m) : ℝ :=
  (v i : Fin m → ℝ) j - (jointPMF E v)⁻¹ *
    ∑ u : E.S i, lam i (Function.update v i u) (some (v i)) * ((u : Fin m → ℝ) j - (v i : Fin m → ℝ) j)

end Supplement

end DSICCompComp


