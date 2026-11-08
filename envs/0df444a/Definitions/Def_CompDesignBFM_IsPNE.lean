-- Prove2me | Definitions.Def_CompDesignBFM_IsPNE
-- name    : CompDesignBFM_IsPNE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:20.716959+00:00
-- url     : https://prove2.me/theorems/d88134a2-47f2-4319-bcf2-878aa5ee22af
-- title:
--   Pure Nash equilibrium of the marginal-contribution game
-- statement:
--   A set $S$ is a **pure Nash equilibrium** of the marginal-contribution game with costs $c$ if $p^F_i(S)\ge c_i$ for $i\in S$ and $p^F_i(S\cup\{i\})\le c_i$ for $i\notin S$: no selected agent gains by leaving and no other agent gains by joining.
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, §1.2.1, p.5 (PDF 7)

import Mathlib
import Definitions.Def_CompDesignBFM_mcPay

namespace CompDesignBFM

/-- A pure Nash equilibrium of the marginal-contribution game with costs `c`
(Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, §1.2.1, p.5, PDF 7): `pᵢ(S) ≥ cᵢ` for `i ∈ S` and `pᵢ(S ∪ {i}) ≤ cᵢ` for `i ∉ S`. -/
def IsPNE {n : ℕ} (F : Finset (Fin n) → ℝ) (B : ℝ) (c : Fin n → ℝ) (S : Finset (Fin n)) : Prop :=
  (∀ i ∈ S, c i ≤ mcPay F B S i) ∧ ∀ i, i ∉ S → mcPay F B (insert i S) i ≤ c i

end CompDesignBFM


