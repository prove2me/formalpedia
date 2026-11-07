-- Prove2me | Definitions.Def_ContinualCounting_IsDP
-- name    : ContinualCounting_IsDP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:45.644183+00:00
-- url     : https://prove2.me/theorems/e28e3742-3938-4902-be35-e14388c94c28
-- title:
--   Definition 1 — $(\varepsilon,\delta)$-differential privacy on $\{0,1\}^n$
-- statement:
--   Two binary vectors $x,x'\in\{0,1\}^n$ are **neighbouring** if they differ in exactly one coordinate. A mechanism $M$, that is, a law $M(x)$ on $\mathbb R^n$ for each input $x\in\{0,1\}^n$, is **$(\varepsilon,\delta)$-DP** if for every measurable $S\subseteq\mathbb R^n$ and all neighbouring $x,x'$,
--   $$\Pr[M(x)\in S]\le e^{\varepsilon}\Pr[M(x')\in S]+\delta.$$
--
--   This is the privacy notion under which the lower bound of the mission is proved. The neighbouring relation is symmetric, so both orders of every pair are covered.
--
--   **Formalization Note** The paper fixes $\varepsilon>0$ and $\delta\in[0,1)$ in the definition. These appear as hypotheses of the theorems. Bits are `Bool`, coordinates are `Fin n`.
-- source:
--   Bairaktari, Dahl, Larsen, The Binary Tree Mechanism is Optimal for Differentially Private Continual Counting, arXiv:2607.00876 (sha256 986e6426…), Definition 1 and the neighbouring relation, p.2 (PDF p.3)

import Mathlib
import Definitions.Def_ContinualCounting_IsApproxDP

set_option autoImplicit false

open MeasureTheory

namespace ContinualCounting

/-- Two binary vectors are neighbouring if they differ in exactly one coordinate (Bairaktari, Dahl,
Larsen, arXiv:2607.00876, sha256 986e6426…, p.2). Bits are `Bool`, coordinates `Fin n`. -/
def Neighbor {n : ℕ} (x x' : Fin n → Bool) : Prop :=
  (Finset.univ.filter fun i => x i ≠ x' i).card = 1

instance {n : ℕ} (x x' : Fin n → Bool) : Decidable (Neighbor x x') := by
  unfold Neighbor; infer_instance

/-- **Definition 1 (Differential Privacy [DMNS06]).** Bairaktari, Dahl, Larsen, arXiv:2607.00876
(sha256 986e6426…), p.2: "Fix ε > 0 and δ ∈ [0, 1). A mechanism M is (ε, δ)-DP if for any measurable
set S ⊆ R^n, Pr[M(x) ∈ S] ≤ e^ε Pr[M(x′) ∈ S] + δ for all pairs of neighboring inputs
x, x′ ∈ {0, 1}^n."

**Formalization Note.** A mechanism is a family of laws on `Fin n → ℝ`, one per input; there is no
measurability side condition because the input type is finite. Being probability measures is
a separate hypothesis of every theorem. `Neighbor` is symmetric, so both orders of each pair are
covered. The range of `ε, δ` is a hypothesis of the theorems, see `IsApproxDP`. -/
def IsDP {n : ℕ} (M : (Fin n → Bool) → Measure (Fin n → ℝ)) (ε δ : ℝ) : Prop :=
  IsApproxDP Neighbor M ε δ

end ContinualCounting


