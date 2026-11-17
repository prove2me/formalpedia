-- Prove2me | Definitions.Def_MMSDelta2_Supplement_GoodsLangOn
-- name    : MMSDelta2_Supplement_GoodsLangOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:06:11.475273+00:00
-- url     : https://prove2.me/theorems/dc217b1b-def4-4e86-a8cf-d04d67276d17
-- title:
--   The MMS existence problem for additive goods restricted to a class of instances
-- statement:
--   Let $\mathcal C$ be a class of additive instances. The language $\mathrm{Goods}_{\mathcal C}$ consists of the binary codes of the additive **goods** instances $v$ with $n\ge 1$ agents, any number $m$ of goods and nonnegative rational values $v_i(g)\ge 0$ such that $v\in\mathcal C$ and $v$ admits an MMS allocation: an allocation $(A_1,\dots,A_n)$ of all goods with
--   $$v_i(A_i)\ \ge\ \mathrm{MMS}_i=\max_{(P_1,\dots,P_n)}\ \min_{j\in[n]} v_i(P_j)\qquad\text{for every agent } i.$$
--
--   It is the decision problem of Theorems 6.6, 1.2 and 1.3 restricted to the class named by their "even for …" clause (five agents with two valuation functions, three agents, bounded values with two agent types).
--
--   **Formalization Note** Same shape as the published `MMSDelta2.MMSLang` (the case $\mathcal C$ = all instances): the code is the base `instCode`, the MMS allocation is the base `HasMMSAllocation`, and a string that encodes no instance, or an instance with a negative value or outside $\mathcal C$, is not in the language.
-- source:
--   Gupta, Seetharaman, The Existence of Maximin Share Allocations is Δ₂ᴾ-complete, arXiv:2609.15841 (held version, sha256 a43b06b9…), Theorems 6.6, 1.2, 1.3 (pp.26, 40, 43; PDF pp.28, 42, 45); goods instances, §4, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_MMSDelta2_instCode
import Definitions.Def_MMSDelta2_HasMMSAllocation

namespace MMSDelta2.Supplement

/-!
# The MMS existence problem for additive goods, restricted to a class of instances

S. Gupta, S. Seetharaman, *The Existence of Maximin Share Allocations is Δ₂ᴾ-complete*,
arXiv:2609.15841 (held version, sha256 a43b06b9…), Theorems 6.6, 1.2, 1.3 (pp.26, 40, 43;
PDF pp.28, 42, 45): "Deciding whether an additive goods instance admits an MMS allocation is …,
even for …"; goods instances have nonnegative valuations (p.12), values are rational (p.11).

**Formalization Note.** Same shape as the published `MMSDelta2.MMSLang`: the codes
`instCode n m v` of the instances with `n ≥ 1` agents and nonnegative rational item values that
lie in the class `C` and admit an MMS allocation (`MMSDelta2.HasMMSAllocation`). A string that
encodes no instance, an instance with a negative value, or an instance outside `C` is not in the
language. With `C` always true this is `MMSLang`.
-/

/-- Codes of additive goods instances (`n ≥ 1`, values `≥ 0`) of the class `C` that admit an MMS
allocation. -/
def GoodsLangOn (C : (n m : ℕ) → (Fin n → Fin m → ℚ) → Prop) : Set (List Bool) :=
  {w | ∃ (n m : ℕ) (v : Fin n → Fin m → ℚ), 1 ≤ n ∧ (∀ i g, 0 ≤ v i g) ∧ C n m v ∧
    HasMMSAllocation v ∧ w = instCode n m v}

end MMSDelta2.Supplement


