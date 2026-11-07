-- Prove2me | Definitions.Def_MMSDelta2_MMSLang
-- name    : MMSDelta2_MMSLang
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:58:21.280315+00:00
-- url     : https://prove2.me/theorems/740a242d-038a-4690-bf9a-6874c28da448
-- title:
--   The MMS existence problem for additive goods: general and five-agent languages
-- statement:
--   The decision problem of Theorem 1.1 is: given an additive goods instance, decide whether it admits an MMS allocation. A **goods instance** has nonnegative values. As languages over $\{0,1\}$:
--
--   1. $\mathrm{MMS}$ is the set of codes of additive instances with $n\ge1$ agents, any number $m\ge0$ of goods and nonnegative rational item values $v_i(g)\ge0$ that admit an MMS allocation;
--   2. $\mathrm{MMS}_5$ is the same set restricted to instances with exactly $n=5$ agents.
--
--   A string that encodes no instance, or encodes an instance with a negative value, belongs to neither language. Checking that a string is the code of a goods instance takes polynomial time.
--
--   **Formalization Note** Codes are `instCode`. The condition $n\ge1$ excludes only the degenerate instance without agents.
-- source:
--   Gupta, Seetharaman, The Existence of Maximin Share Allocations is Δ₂ᴾ-complete, arXiv:2609.15841 (held version, sha256 a43b06b9…), Theorem 1.1, p.3 (PDF p.5); goods instances, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_MMSDelta2_instCode
import Definitions.Def_MMSDelta2_HasMMSAllocation

namespace MMSDelta2

/-!
# The MMS existence problem for additive goods, in general and for five agents

S. Gupta, S. Seetharaman, *The Existence of Maximin Share Allocations is Δ₂ᴾ-complete*,
arXiv:2609.15841 (held version, sha256 a43b06b9…), Theorem 1.1, p.3 (PDF p.5): "Deciding whether an
additive goods instance admits an MMS allocation"; goods instances have nonnegative valuations
(p.12), values are rational (p.11).

**Formalization Note.** The language consists of the codes `instCode n m v` of the instances with
`n ≥ 1` agents, any number `m` of goods and nonnegative rational item values that admit an MMS
allocation. A string that encodes no instance, or an instance with a negative value, is not in the
language. `n ≥ 1` excludes only the degenerate instance with no agents. `MMSLang5` is the
restriction to `n = 5`.
-/

/-- Codes of additive goods instances (`n ≥ 1`, values `≥ 0`) that admit an MMS allocation. -/
def MMSLang : Set (List Bool) :=
  {w | ∃ (n m : ℕ) (v : Fin n → Fin m → ℚ), 1 ≤ n ∧ (∀ i g, 0 ≤ v i g) ∧ HasMMSAllocation v ∧
    w = instCode n m v}

/-- Codes of five-agent additive goods instances that admit an MMS allocation. -/
def MMSLang5 : Set (List Bool) :=
  {w | ∃ (m : ℕ) (v : Fin 5 → Fin m → ℚ), (∀ i g, 0 ≤ v i g) ∧ HasMMSAllocation v ∧
    w = instCode 5 m v}

end MMSDelta2


