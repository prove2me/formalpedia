-- Prove2me | Definitions.Def_GibbsCongestion_loadClass
-- name    : GibbsCongestion_loadClass
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:01:27.708193+00:00
-- url     : https://prove2.me/theorems/6ce88e89-b46a-4d1c-9aed-227af3f68cd8
-- title:
--   The map $s\mapsto z(s)\in\mathcal L$
-- statement:
--   The map sending a strategy profile $s\in\mathcal P^n$ to its strategy load profile $z(s)\in\mathcal L$. Its fibres are the classes $\Omega_\alpha=\mathcal S(\alpha)$, the partition of the state space used in the decomposition argument of the proof of Theorem 4.4.
--
--   **Formalization Note** The definition carries the (structural) proof that $z(s)$ has non-negative entries at most $n$ summing to $n$.
-- source:
--   Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, §2.1, p.7; §4, p.15; proof of Theorem 4.4, p.17

import Mathlib
import Definitions.Def_GibbsCongestion_strategyLoad
import Definitions.Def_GibbsCongestion_loadProfiles

namespace GibbsCongestion

/-- The map `s ↦ z(s)` from strategy profiles to their strategy load profiles in `L`
(Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, §2.1, p.7 and §4, p.15). Its fibres are the classes `S(α) = {s : z(s) = α}`, the
partition `Ω_α = S(α)` used in the proof of Theorem 4.4 (p.17). -/
noncomputable def loadClass {E : Type*} [DecidableEq E] (P : Finset (Finset E)) (n : ℕ) (s : Fin n → P) :
    loadProfiles P n :=
  ⟨strategyLoad s, by
    simp only [loadProfiles, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
    refine ⟨fun p => Nat.lt_succ_of_le ?_, ?_⟩
    · exact (Finset.card_filter_le _ _).trans (by simp)
    · unfold strategyLoad
      rw [← Finset.card_eq_sum_card_fiberwise (fun i _ => Finset.mem_univ (s i))]
      simp⟩

end GibbsCongestion


