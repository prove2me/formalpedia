-- Prove2me | Definitions.Def_CompetingSellers_utilP
-- name    : CompetingSellers_utilP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:48.918261+00:00
-- url     : https://prove2.me/theorems/8ab4ed11-8cb6-4747-8b53-30dbdd1df773
-- title:
--   Monopolist utility $\mathrm{util}_P(v)$, induced allocation rules $z^\pm_P$, the gap $\mathrm{Aug}_P$, implementability
-- statement:
--   For a pricing function $P$ and a value $v$, the buyer's **monopolist utility** is $\mathrm{util}_P(v)=\max_{x\in[0,1]}\{v x-P(x)\}$, over the available allocations. The **upper** and **lower induced allocation rules** $z^+_P(v)$, $z^-_P(v)$ are the largest and smallest maximizers. The **augmentation-induced utility gap** is
--   $$\mathrm{Aug}_P(v,w)=\mathrm{util}_P(w)-\mathrm{util}_P(\max(0,w-v))\qquad(2).$$
--   An allocation rule $z:[0,\infty)\to[0,1]$ **implements** $P$ if $z(\hat v)\in\arg\max_{x\in[0,1]}\{\hat v x-P(x)\}$ for all $\hat v\ge0$, and is **implementable** if it implements some proper pricing function.
--
--   These are the single-seller quantities in terms of which the paper describes the buyer's behaviour against two sellers (Lemma 3.1).
--
--   **Formalization Note** The maximum is a real supremum over $\{x\in[0,1]:P(x)<\infty\}$; $z^\pm$ are the supremum and infimum of the set of maximizers.
-- source:
--   Babaioff, Grofman, Lucier, Saxena, On Competing Sellers with Substitutable Goods (manuscript, sha256 75c874b3…), §2 Allocation Rules and Implementability, p.17 (PDF 20); p.18; eq. (2), p.19

import Mathlib
import Definitions.Def_CompetingSellers_IsProperPricing

set_option autoImplicit false

open scoped ENNReal

namespace CompetingSellers

/-- **Monopolist utility** `util_P(v) = max_{x∈[0,1]} {v·x − P(x)}` (p.18).
Babaioff, Grofman, Lucier, Saxena, *On Competing Sellers with Substitutable Goods*
(manuscript, sha256 75c874b3…), p.18 (PDF 21): "For an auxiliary single-seller value `v ≥ 0`,
let `util_M(v) = max_{x∈[0,1]} {v · x − P_M(x)}` … denote the buyer's maximum utility from `M`
alone."

**Formalization Note.** The maximum is taken over the available allocations
(`x ∈ [0, 1]`, `P x ≠ ∞`) as a real supremum; the set is bounded above by `max v 0`, and nonempty
for proper `P` (`P 0 = 0`). -/
noncomputable def utilP (P : ℝ → ℝ≥0∞) (v : ℝ) : ℝ :=
  sSup ((fun x => v * x - (P x).toReal) '' {x | x ∈ Set.Icc (0 : ℝ) 1 ∧ P x ≠ ⊤})

/-- The set of utility-maximizing allocations `arg max_{x∈[0,1]} {v x − P(x)}`. -/
def argmaxP (P : ℝ → ℝ≥0∞) (v : ℝ) : Set ℝ :=
  {x | x ∈ Set.Icc (0 : ℝ) 1 ∧ P x ≠ ⊤ ∧ v * x - (P x).toReal = utilP P v}

/-- Upper induced allocation rule `z⁺_P(v)` (p.17): the largest maximizing allocation. -/
noncomputable def zPlus (P : ℝ → ℝ≥0∞) (v : ℝ) : ℝ := sSup (argmaxP P v)

/-- Lower induced allocation rule `z⁻_P(v)` (p.17): the smallest maximizing allocation. -/
noncomputable def zMinus (P : ℝ → ℝ≥0∞) (v : ℝ) : ℝ := sInf (argmaxP P v)

/-- Augmentation-induced utility gap (eq. (2), p.19):
`Aug_P(v, w) = util_P(w) − util_P(max(0, w − v))`. -/
noncomputable def augP (P : ℝ → ℝ≥0∞) (v w : ℝ) : ℝ := utilP P w - utilP P (max 0 (w - v))

/-- **Implementation** (p.17): "An allocation rule `z` implements a proper pricing function `P_M`
if `z(v̂) ∈ arg max_{x∈[0,1]} {v̂ · x − P_M(x)}` for all `v̂ ≥ 0`." An allocation rule is a map
`z : [0, ∞) → [0, 1]`, here `ℝ → ℝ` read on `[0, ∞)`. -/
def Implements (z : ℝ → ℝ) (P : ℝ → ℝ≥0∞) : Prop :=
  ∀ v, 0 ≤ v → z v ∈ argmaxP P v

/-- "An allocation rule is implementable if it implements some proper pricing function" (p.17). -/
def Implementable (z : ℝ → ℝ) : Prop :=
  ∃ P, IsProperPricing P ∧ Implements z P

end CompetingSellers


