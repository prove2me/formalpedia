-- Prove2me | Definitions.Def_MMSDelta2_Supplement_ChoresLangOn
-- name    : MMSDelta2_Supplement_ChoresLangOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:06:46.573498+00:00
-- url     : https://prove2.me/theorems/163a0429-696f-4f23-b713-d1938bfd068a
-- title:
--   The MMS existence problem for additive chores
-- statement:
--   In a **chores** instance the valuations are nonpositive and larger values are still preferred; with costs $c_i=-v_i$,
--   $$\mathrm{MMS}_i=\max_{(P_1,\dots,P_n)}\min_{j\in[n]} v_i(P_j)=-\min_{(P_1,\dots,P_n)}\max_{j\in[n]} c_i(P_j),$$
--   and an allocation $A$ is an MMS allocation iff $c_i(A_i)\le\min_{(P_1,\dots,P_n)}\max_j c_i(P_j)$ for every agent $i$.
--
--   For a class $\mathcal C$ of instances, the language $\mathrm{Chores}_{\mathcal C}$ consists of the binary codes of the additive chores instances $v$ with $n\ge 1$ agents, any number of chores and nonpositive rational values $v_i(g)\le 0$ such that $v\in\mathcal C$ and $v$ admits an MMS allocation. The named special cases are
--
--   1. $\mathrm{Chores}$: all chores instances;
--   2. $\mathrm{Chores}_5$: instances with exactly five agents;
--   3. $\mathrm{Chores}_3$: instances with exactly three agents.
--
--   These are the decision problems of Theorem 1.5 and Corollary 9.2.
--
--   **Formalization Note** The MMS allocation is the base mission's `HasMMSAllocation`, stated in values ($v_i(A_i)\ge\mathrm{MMS}_i$) with no sign assumption; on nonpositive values it is exactly the cost formulation above. The code `instCode` carries the sign of each value. Non-codes, instances with a positive value and instances outside $\mathcal C$ are not in the language.
-- source:
--   Gupta, Seetharaman, The Existence of Maximin Share Allocations is Δ₂ᴾ-complete, arXiv:2609.15841 (held version, sha256 a43b06b9…), §4 'Goods and chores', p.12 (PDF p.14); Theorem 1.5, p.4 (PDF p.6); Corollary 9.2, p.46 (PDF p.48)

import Mathlib
import Definitions.Def_MMSDelta2_instCode
import Definitions.Def_MMSDelta2_HasMMSAllocation

namespace MMSDelta2.Supplement

/-!
# The MMS existence problem for additive chores

S. Gupta, S. Seetharaman, *The Existence of Maximin Share Allocations is Δ₂ᴾ-complete*,
arXiv:2609.15841 (held version, sha256 a43b06b9…), §4, p.12 (PDF p.14): "In a chores instance, the
valuations are nonpositive, and larger values are still preferred", with
`MMS_i = max_{(P_1,…,P_n)} min_j v_i(P_j) = −min_{(P_1,…,P_n)} max_j c_i(P_j)` and "an allocation
`A` is an MMS allocation for a chores instance iff `c_i(A_i) ≤ min max c_i(P_j)` for every agent
`i`"; Corollary 9.2, p.46 (PDF p.48).

**Formalization Note.** The published `MMSDelta2.HasMMSAllocation` is stated in values
(`v_i(A_i) ≥ MMS_i` with `MMS_i = max min v_i(P_j)`) and makes no sign assumption, so on an
instance with nonpositive values it is exactly the paper's chores MMS allocation. The language
consists of the codes `instCode n m v` of the instances with `n ≥ 1` agents and nonpositive
rational item values that lie in the class `C` and admit an MMS allocation; the code carries the
sign of each value. Non-codes, instances with a positive value, and instances outside `C` are not in
the language.
-/

/-- Codes of additive chores instances (`n ≥ 1`, values `≤ 0`) of the class `C` that admit an MMS
allocation. -/
def ChoresLangOn (C : (n m : ℕ) → (Fin n → Fin m → ℚ) → Prop) : Set (List Bool) :=
  {w | ∃ (n m : ℕ) (v : Fin n → Fin m → ℚ), 1 ≤ n ∧ (∀ i g, v i g ≤ 0) ∧ C n m v ∧
    HasMMSAllocation v ∧ w = instCode n m v}

/-- Codes of all additive chores instances that admit an MMS allocation. -/
def ChoresLang : Set (List Bool) := ChoresLangOn (fun _ _ _ => True)

/-- Codes of five-agent additive chores instances that admit an MMS allocation. -/
def ChoresLang5 : Set (List Bool) := ChoresLangOn (fun n _ _ => n = 5)

/-- Codes of three-agent additive chores instances that admit an MMS allocation. -/
def ChoresLang3 : Set (List Bool) := ChoresLangOn (fun n _ _ => n = 3)

end MMSDelta2.Supplement


