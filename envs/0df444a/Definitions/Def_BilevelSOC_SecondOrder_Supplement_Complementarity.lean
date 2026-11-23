-- Prove2me | Definitions.Def_BilevelSOC_SecondOrder_Supplement_Complementarity
-- name    : BilevelSOC_SecondOrder_Supplement_Complementarity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:37:54.414131+00:00
-- url     : https://prove2.me/theorems/2b7d578b-9188-45a9-a4ea-98c008aebe98
-- title:
--   §4.4 — complementarity branches, strict MFCQ and projected KKT cone
-- statement:
--   For published bilevel data $D$, a feasible reference pair $z$, and a lower multiplier $\bar\lambda$, define
--
--   $$I^{0-}=\{i:\bar\lambda_i=0,\ g_i(z)<0\},\quad I^{+0}=\{i:\bar\lambda_i>0,\ g_i(z)=0\},\quad I^{00}=\{i:\bar\lambda_i=0,\ g_i(z)=0\}.$$
--
--   Strict MFCQ is exactly (4.9): any $\mu$ with $\sum_i\mu_i\nabla_y g_i(z)=0$, zero components off the active set, and nonnegative components on $I^{00}$ must vanish. Components on $I^{+0}$ are unrestricted. The KKT feasible set imposes upper and lower feasibility and lower multiplier membership; $\Pi$ drops the multiplier coordinate. The KKT linearization cone contains all three complementarity branches: zero multiplier derivative on $I^{0-}$, zero constraint derivative on $I^{+0}$, and nonnegative multiplier derivative, nonpositive constraint derivative and zero product on $I^{00}$. It also contains every active upper inequality and the linearized lower stationarity equation.
--
--   These definitions give the complete projected cone in Lemma 4.15 and the full augmented exclusion system in Theorem 4.18. **Formalization Note** The primal pair and multiplier are grouped as a nested product; all $q$ multipliers remain independent real coordinates, including when $q=0$.
-- source:
--   Mehlitz & Zemkoho, Sufficient Optimality Conditions in Bilevel Programming, arXiv:1911.01647v1, pp. 3–4, 6–10, 12–17, §4.4

import Mathlib
import Definitions.Def_BilevelSOC_SecondOrder_Supplement_Multipliers
open scoped Topology

namespace BilevelSOC.SecondOrder.Supplement
variable {n m p q : ℕ}
def i0minus (D : Data n m p q) (z : E n × Y m) (lam : Fin q → ℝ) : Set (Fin q) :=
  {i | lam i = 0 ∧ D.g i z < 0}
def iplus0 (D : Data n m p q) (z : E n × Y m) (lam : Fin q → ℝ) : Set (Fin q) :=
  {i | 0 < lam i ∧ D.g i z = 0}
def i00 (D : Data n m p q) (z : E n × Y m) (lam : Fin q → ℝ) : Set (Fin q) :=
  {i | lam i = 0 ∧ D.g i z = 0}
noncomputable def StrictMFCQ (D : Data n m p q) (z : E n × Y m) (lam : Fin q → ℝ) : Prop :=
  ∀ μ : Fin q → ℝ, (∑ i, μ i • yGrad (D.g i) z) = 0 →
    (∀ i, i ∉ actg D z → μ i = 0) → (∀ i ∈ i00 D z lam, 0 ≤ μ i) → μ = 0
noncomputable def kktFeas (D : Data n m p q) : Set ((E n × Y m) × (Fin q → ℝ)) :=
  {w | (∀ i, D.G i w.1 ≤ 0) ∧ w.1.2 ∈ lowerFeas D w.1.1 ∧ w.2 ∈ multipliers D w.1}
def projection : ((E n × Y m) × (Fin q → ℝ)) → E n × Y m := Prod.fst
noncomputable def kktLinCone (D : Data n m p q) (z : E n × Y m) (lam : Fin q → ℝ) :
    Set ((E n × Y m) × (Fin q → ℝ)) :=
  {w | (∀ i ∈ actG D z, fderiv ℝ (D.G i) z w.1 ≤ 0) ∧
    yHess (lagrangian D lam) z w.1 + (∑ i, w.2 i • yGrad (D.g i) z) = 0 ∧
    (∀ i ∈ i0minus D z lam, w.2 i = 0) ∧
    (∀ i ∈ iplus0 D z lam, fderiv ℝ (D.g i) z w.1 = 0) ∧
    ∀ i ∈ i00 D z lam, 0 ≤ w.2 i ∧ fderiv ℝ (D.g i) z w.1 ≤ 0 ∧
      w.2 i * fderiv ℝ (D.g i) z w.1 = 0}
end BilevelSOC.SecondOrder.Supplement


