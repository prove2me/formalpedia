-- Prove2me | Definitions.Def_CausalFailureRank_G
-- name    : CausalFailureRank_G
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:14:13.37939+00:00
-- url     : https://prove2.me/theorems/8c159184-66c5-40fa-8e66-f4bdbe5d4b6e
-- title:
--   Relaxed one-penalty value $G_{i,R}(\lambda)$, eqs. (19), (20)
-- statement:
--   With a single penalty $\lambda>0$ for task failure, $G_{N+1,R}=0$; $G_g=G_{i+1,R}$; $G_b=\lambda$ if $S_i\cap R=\emptyset$ and $G_b=\min_{r\in S_i\cap R}G_{i+1,R\setminus\{r\}}$ otherwise; and
--   $$G_{i,R}=\min\{\lambda,\ G_g+J_i(G_b-G_g)\}.$$
--   It is the comparison value of the lower bound of the price law.
--
--   **Formalization Note** Defined by this recursion. The paper's further claim that it is the exact value of the relaxed problem is not used by the theorem and is not an item.
-- source:
--   Zang, Li, Jin, Xu, Causal Failure Rank Determines Statistical Depth, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), App. B.2, eqs. (19), (20), p.16

import Mathlib
import Definitions.Def_CausalFailureRank_J

namespace CausalFailureRank

variable {N q : ℕ}

open scoped Classical in
/-- The bad continuation of eq. (19), p.16, as a function of the continuation values: `λ` if
`S_i ∩ R = ∅`, else the minimum over `r ∈ S_i ∩ R` of the continuation at `R \ {r}`. -/
noncomputable def badCont (I : Instance N q) (i : Fin N) (R : Finset (Fin q)) (lam : ℝ)
    (cont : Finset (Fin q) → ℝ) : ℝ :=
  if h : (I.S i ∩ R).Nonempty then (I.S i ∩ R).inf' h fun r => cont (R.erase r) else lam

/-- **The relaxed value `G_{i,R}(λ)`.** Zang, Li, Jin, Xu, *Causal Failure Rank Determines Statistical
Depth*, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), App. B.2, eqs. (19),
(20), p.16: `G_{N+1,R} = 0` and `G_{i,R} = min {λ, G_g + J_i(G_b - G_g)}`.

**Formalization Note.** Defined by the recursion (20); it is not the value of a policy class. This
mission uses only its lower half (Lemma B.2), not the paper's proof that (20) is the exact value
of the relaxed problem. `J` is finite on `t ≥ 0` by Lemma B.1, so `toReal` is harmless there; 0-based
stages make the terminal `i ≥ N`. -/
noncomputable def G (I : Instance N q) (i : ℕ) (R : Finset (Fin q)) (lam : ℝ) : ℝ :=
  if h : i < N then
    min lam (G I (i + 1) R lam +
      (J I ⟨i, h⟩ (badCont I ⟨i, h⟩ R lam (fun R' => G I (i + 1) R' lam) - G I (i + 1) R lam)).toReal)
  else 0
termination_by N - i
decreasing_by all_goals omega

/-- `G_b` of eq. (19), p.16. -/
noncomputable def Gb (I : Instance N q) (i : Fin N) (R : Finset (Fin q)) (lam : ℝ) : ℝ :=
  badCont I i R lam fun R' => G I (i.val + 1) R' lam

end CausalFailureRank


