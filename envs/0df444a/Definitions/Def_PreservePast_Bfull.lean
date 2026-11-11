-- Prove2me | Definitions.Def_PreservePast_Bfull
-- name    : PreservePast_Bfull
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T10:42:34.099314+00:00
-- url     : https://prove2.me/theorems/0c6f387e-4829-4dc1-8ea0-a4fa67ebaaab
-- title:
--   Least register size $B_{\mathrm{full}}(K,n,m,r;\epsilon,\xi,R,\beta)$
-- statement:
--   $B_{\mathrm{full}}(K,n,m,r;\epsilon,\xi,R,\beta)$ is the least register size $B$ for which some randomized $B$-bit retained-state protocol achieves the protective-update task for histories of $K$ tasks, rank $r$, accuracy $\epsilon$, fit tolerance $\xi$, radius $R$ and failure probability $\beta$.
--
--   **Formalization Note** The infimum of a set of natural numbers (coin spaces in `Type`); Lean's `sInf ∅ = 0`. The mission's statements therefore never use this number alone: lower bounds are stated for every achieving width and upper bounds exhibit an achieving code. A verification file derives the two-sided bound (16) for this infimum from the goal theorem.
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb…d00fa), §3.1, p.6 (PDF p.8)

import Mathlib
import Definitions.Def_PreservePast_RandAchieves

open MeasureTheory

namespace PreservePast

/-- **The least register size** `B_full(K, n, m, r; ϵ, ξ, R, β)`.
P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), §3.1, p.6 (PDF p.8): "Let B_full(K, n, m, r; ϵ, ξ, R, β) be the least such register size."

The infimum of the widths `B` for which some randomized `B`-bit protocol (`RandAchieves`)
achieves the task with parameters `(K, r, ε, ξ, R, β)` for the checkpoint `W₀`.

**Formalization Note.** The infimum of a set of natural numbers; Lean's `sInf ∅ = 0`, so the
statements of this mission never use `Bfull` alone: the goal states its lower bound for every
achieving width and exhibits an achieving code for its upper bound. Coin spaces live in `Type`. -/
noncomputable def Bfull {m n : ℕ} (W₀ : Matrix (Fin m) (Fin n) ℝ) (K r : ℕ) (ε ξ R β : ℝ) : ℕ :=
  sInf {B : ℕ | ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
    (enc : (Fin K → Task W₀) → Ω → Fin (2 ^ B))
    (dec : Fin (2 ^ B) → Ω → (Fin n → ℝ) → (Fin m → ℝ) → Matrix (Fin m) (Fin n) ℝ),
    RandAchieves P enc dec r ε ξ R β}

end PreservePast


