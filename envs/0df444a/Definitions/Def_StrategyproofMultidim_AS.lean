-- Prove2me | Definitions.Def_StrategyproofMultidim_AS
-- name    : StrategyproofMultidim_AS
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:12:23.858078+00:00
-- url     : https://prove2.me/theorems/3e076db3-4fca-44f2-b9a1-fcd54eafb1e8
-- title:
--   Agent sovereignty (AS)
-- statement:
--   A mechanism satisfies **agent sovereignty** if every buyer can change its own decision on any object by changing only its report for that object: for every positive profile $v$, buyer $i$ and object $k$ there exist positive values $a,b$ such that
--   $$d_i^k((a,v_i^{-k}),v_{-i})\neq d_i^k((b,v_i^{-k}),v_{-i}).$$
-- source:
--   Basu, Mukherjee, Strategyproof multidimensional mechanism design without unit demand, IIM Calcutta WPS No 875 (April 2022), Definition 2, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_StrategyproofMultidim_Mechanism
import Definitions.Def_StrategyproofMultidim_PosProfile

namespace StrategyproofMultidim

/-- **Agent sovereignty (AS)** (Definition 2, p.7).
Basu, Mukherjee, *Strategyproof multidimensional mechanism design without unit demand*,
IIM Calcutta WPS No 875 (April 2022), p.7: "Definition 2. A mechanism μ satisfies agent sovereignty (AS) if ∀i ∈ N, ∀k ∈ M,
∀vᵢ⁻ᵏ ∈ ℝᵐ⁻¹₊₊, and ∀ v₋ᵢ ∈ Πⱼ≠ᵢVⱼ, there exist vᵢᵏ, wᵢᵏ > 0 such that:
dᵢᵏ((vᵢᵏ, vᵢ⁻ᵏ), v₋ᵢ) ≠ dᵢᵏ((wᵢᵏ, vᵢ⁻ᵏ), v₋ᵢ)."

For every positive profile `v`, buyer `i` and object `k` there are positive values `a, b` such
that buyer `i`'s decision on object `k` differs between the profiles obtained from `v` by
setting `vᵢᵏ := a` and `vᵢᵏ := b`.

**Formalization Note.** The data `(vᵢ⁻ᵏ, v₋ᵢ)` of the definition are the entries of the positive
profile `v` other than `vᵢᵏ`; the entry `vᵢᵏ` of `v` itself is overwritten. -/
def AS {n m : ℕ} (μ : Mechanism n m) : Prop :=
  ∀ v, PosProfile v → ∀ (i : Fin n) (k : Fin m), ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
    μ.q (Function.update v i (Function.update (v i) k a)) i k ≠
      μ.q (Function.update v i (Function.update (v i) k b)) i k

end StrategyproofMultidim


