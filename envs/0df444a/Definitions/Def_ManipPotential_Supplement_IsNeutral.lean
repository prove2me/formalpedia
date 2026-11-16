-- Prove2me | Definitions.Def_ManipPotential_Supplement_IsNeutral
-- name    : ManipPotential_Supplement_IsNeutral
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:08:08.484482+00:00
-- url     : https://prove2.me/theorems/45ee9e8d-bdbc-46f4-aa48-a0bc972ebcae
-- title:
--   Neutral SCC
-- statement:
--   For a candidate permutation $\pi : C \to C$ and a profile $\succ_N$, let $\pi(\succ_N)$ be the profile $\succ'_N$ with $c \succ_i c'$ iff $\pi(c) \succ'_i \pi(c')$. An SCC $F$ is **neutral** if for every candidate permutation $\pi$, profile $\succ_N$ and candidate $c$,
--   $$c \in F(\succ_N) \iff \pi(c) \in F(\pi(\succ_N)).$$
--
--   **Formalization Note** With rankings as maps from candidates to positions, the relabelled ballot puts $\pi(c)$ at the position $c$ had, i.e. it is $r \circ \pi^{-1}$.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 3, "Tie(breaker)s", p.10

import Mathlib
import Definitions.Def_ManipPotential_Supplement_SCC

namespace ManipPotential.Supplement

/-- A neutral SCC (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 3, "Tie(breaker)s", p.10): for every candidate permutation `π`,
profile `≻_N` and candidate `c`, `c ∈ F(≻_N)` iff `π(c) ∈ F(π(≻_N))`, where `π(≻_N)` is the profile
`≻'_N` with `c ≻_i c'` iff `π(c) ≻'_i π(c')`.

**Formalization Note** With rankings as position maps, the relabelled ballot `r'` puts `π c` where
`r` put `c`: `r' (π c) = r c`, i.e. `r' = π⁻¹ ≫ r` (`π.symm.trans r`). -/
def IsNeutral {m : ℕ} (F : SCC m) : Prop :=
  ∀ (π : Equiv.Perm (Fin m)) (P : List (Ranking m)) (c : Fin m),
    c ∈ F P ↔ π c ∈ F (P.map (fun r => π.symm.trans r))

end ManipPotential.Supplement


