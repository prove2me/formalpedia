-- Prove2me | Definitions.Def_MPBSelect_Problem_Xi
-- name    : MPBSelect_Problem_Xi
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:26:18.004779+00:00
-- url     : https://prove2.me/theorems/d102401a-49ae-449c-bdd7-b94b528c739a
-- title:
--   The index set $\Xi=\{(i,\theta_b): i\ne i^*,\ i\ne i^b\}$
-- statement:
--   For an MPB problem with conditional optima $i^b$ and most probable best $i^*$, let
--   $$
--   \Xi=\{(i,\theta_b): i\ne i^*,\ i\ne i^b\}
--   $$
--   be the set of solution–parameter pairs in which $i$ is neither the MPB nor the conditional optimum at $\theta_b$. The objective of the relaxed OCBA problem (20) is a minimum over $\Xi$.
--
--   $\Xi$ is nonempty: since $k\ge2$ some $j\ne i^*$ exists, $i^*$ has positive preference probability and is therefore $i^b$ for some $b$, and then $(j,\theta_b)\in\Xi$. This is proved in the definition file and makes the minimum in (20) well defined.
--
--   **Formalization Note** A pair $(i,\theta_b)$ is `(i, b) : Fin k × Fin B`, and $\Xi$ is a `Finset`.
-- source:
--   Kim, Kim, Song, Selection of the Most Probable Best, arXiv:2207.07533v2, §4.2, p.14

import Mathlib
import Definitions.Def_MPBSelect_Problem

namespace MPBSelect

open Finset

/-- **The index set `Ξ` of problem (20).**
Kim, Kim, Song, *Selection of the Most Probable Best*, arXiv:2207.07533v2, §4.2, p.14:
"Ξ := {(i,θb) | i ≠ i∗, i ≠ i^b}".

`Ξ` is the set of solution-parameter pairs `(i, θ_b)` with `i` neither the MPB nor the
conditional optimum at `θ_b`.

**Formalization Note** A pair `(i, θ_b)` is `(i, b) : Fin k × Fin B`. -/
def Problem.Xi {k B : ℕ} (P : Problem k B) : Finset (Fin k × Fin B) :=
  univ.filter (fun x => x.1 ≠ P.istar ∧ x.1 ≠ P.ib x.2)

/-- `Ξ` is nonempty: since `k ≥ 2` some `j ≠ i*` exists, `i*` has positive preference
probability, so `i* = i^b` for some `b`, and `(j, θ_b) ∈ Ξ`. -/
theorem Problem.Xi_nonempty {k B : ℕ} (P : Problem k B) : P.Xi.Nonempty := by
  have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr P.two_le_k
  obtain ⟨j, hj⟩ := exists_ne P.istar
  have hlt := P.istar_spec j hj
  have h0 : 0 ≤ prefProb P.p P.ib j := by
    unfold prefProb
    refine Finset.sum_nonneg fun b _ => ?_
    split_ifs
    · exact (P.p_pos b).le
    · exact le_rfl
  have hpos : 0 < prefProb P.p P.ib P.istar := lt_of_le_of_lt h0 hlt
  have : ∃ b, P.ib b = P.istar := by
    by_contra hne
    simp only [not_exists] at hne
    have : prefProb P.p P.ib P.istar = 0 := by
      unfold prefProb
      exact Finset.sum_eq_zero fun b _ => if_neg (hne b)
    linarith
  obtain ⟨b, hb⟩ := this
  exact ⟨(j, b), by simp [Problem.Xi, hj, hb]⟩

end MPBSelect


