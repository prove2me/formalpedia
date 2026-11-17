-- Prove2me | Definitions.Def_MMSDelta2_Supplement_numTypes
-- name    : MMSDelta2_Supplement_numTypes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:05:14.612837+00:00
-- url     : https://prove2.me/theorems/ac95f7c0-ac8e-4d71-8caf-52e4fb2b82f3
-- title:
--   The number of agent types of an additive instance
-- statement:
--   Let $v=(v_i)_{i\in[n]}$ be an additive instance with $n$ agents and $m$ goods, agent $i$ valuing good $g$ at $v_i(g)\in\mathbb Q$. Two agents have the **same type** if they have identical valuation functions, and the **number of agent types** is the number of distinct valuation functions:
--   $$\mathrm{numTypes}(v)=\bigl|\{v_i : i\in[n]\}\bigr|.$$
--
--   This is the parameter restricted in Theorems 6.6 and 1.3 ("two distinct valuation functions", "two agent types").
--
--   **Formalization Note** An instance is `v : Fin n → Fin m → ℚ`; the valuation function of agent `i` is the row `v i`, and the count is the cardinality of the image of `v`.
-- source:
--   Gupta, Seetharaman, The Existence of Maximin Share Allocations is Δ₂ᴾ-complete, arXiv:2609.15841 (held version, sha256 a43b06b9…), §1.1, p.3 (PDF p.5)

import Mathlib

namespace MMSDelta2.Supplement

/-!
# The number of agent types of an additive instance

S. Gupta, S. Seetharaman, *The Existence of Maximin Share Allocations is Δ₂ᴾ-complete*,
arXiv:2609.15841 (held version, sha256 a43b06b9…), §1.1, p.3 (PDF p.5): "We say that two agents
have the same type if they have identical valuation functions; thus, the number of agent types is
the number of distinct valuation functions in the input."

**Formalization Note.** An additive instance is `v : Fin n → Fin m → ℚ` (the base mission's
convention); agent `i`'s valuation function is the row `v i`, so the number of agent types is the
number of distinct rows.
-/

/-- The number of agent types of `v`: the number of distinct valuation functions `v i` (p.3). -/
def numTypes {n m : ℕ} (v : Fin n → Fin m → ℚ) : ℕ :=
  (Finset.univ.image v).card

end MMSDelta2.Supplement


