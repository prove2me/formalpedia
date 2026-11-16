-- Prove2me | Definitions.Def_BlockSSM_Supplement_tau
-- name    : BlockSSM_Supplement_tau
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:02:49.235415+00:00
-- url     : https://prove2.me/theorems/ac81a103-5777-4a50-b3d9-afaa10ef304b
-- title:
--   The subspace-cover cost $\tau_b(r)$
-- statement:
--   With $\widehat Q=\mathbb F_2^r$, define
--   $$
--   \tau_b(r)=\min\Bigl\{\sum_j|U_j|\;:\;U_j\le\widehat Q,\ |U_j|\le b,\ \bigcup_jU_j=\widehat Q\Bigr\},
--   $$
--   the minimum over finite families of subspaces of size at most $b$ covering $\widehat Q$, with value $\infty$ when no family exists (for instance $b=1$: the only subspace of size one is $\{0\}$). Here $|U_j|$ is the number of elements of $U_j$, a power of $2$.
--
--   Theorem 15 identifies $\tau_b(r)$ with $D_b(G_{p,r})$.
--
--   **Formalization Note** Infimum in $\mathbb N\cup\{\infty\}$; stated for every $r$ (the paper uses $r\ge2$).
-- source:
--   C. Geng, The State Complexity of Block-Diagonal State Space Models, STOC 2027 submission manuscript (sha256 f9071794…), §7, p.7 (PDF p.8)

import Mathlib

namespace BlockSSM.Supplement

/-- **The subspace-cover cost `τ_b(r)`.** Geng, *The State Complexity of Block-Diagonal State Space Models*, STOC 2027 submission manuscript (sha256 f9071794…), §7, p.7 (PDF p.8): "For r ≥ 2 define
τ_b(r) = min { ∑_j |U_j| : U_j ≤ Q̂, |U_j| ≤ b, ⋃_j U_j = Q̂ }. For b = 1 this value is infinite:
the only subspace of size one is {0}."

**Formalization Note.** `Q̂ = F₂^r`; `U_j` ranges over finite families of `F₂`-subspaces,
`|U_j|` is the cardinality of `U_j` (a power of 2, not its dimension). The minimum is taken in
`ℕ∞`, `⊤` when no family is feasible (e.g. `b ≤ 1`). Stated for all `r`; the paper uses it for
`r ≥ 2`. -/
noncomputable def tau (r : ℕ) (b : ℕ∞) : ℕ∞ :=
  sInf {D : ℕ∞ | ∃ (k : ℕ) (U : Fin k → Submodule (ZMod 2) (Fin r → ZMod 2)),
    (∀ j, (Nat.card (U j) : ℕ∞) ≤ b) ∧ (⋃ j, (U j : Set (Fin r → ZMod 2))) = Set.univ ∧
    D = ((∑ j, Nat.card (U j) : ℕ) : ℕ∞)}

end BlockSSM.Supplement


