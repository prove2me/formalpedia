-- Prove2me | Definitions.Def_NondualOpt_FOAlgorithm
-- name    : NondualOpt_FOAlgorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:58:53.849708+00:00
-- url     : https://prove2.me/theorems/071b4c1e-30f2-4e32-b908-cc71a3b31f9c
-- title:
--   A deterministic $T$-query first-order algorithm on $B_p^d$
-- statement:
--   A **deterministic first-order algorithm** with $T$ queries in $B_p^d$ consists of
--
--   1. query maps: at round $t$ it queries a point $x_t\in B_p^d$ that is a function of the $t$ oracle answers $(f(x_s),g_s)$, $s<t$, received so far;
--   2. an output map: after the $T$ answers it outputs a point $\hat x_T\in B_p^d$ that is a function of all answers.
--
--   This is the class of algorithms "ALG" in the minimax error (4) and the "deterministic algorithm" of Corollary 7.
--
--   **Formalization Note** Determinism is the typing: queries and output are plain functions of the answers. Rounds are indexed from $0$.
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, §2, (4), p.7; Corollary 7, p.12

import Mathlib
import Definitions.Def_NondualOpt_lpBall

open scoped ENNReal

namespace NondualOpt

/-- A deterministic first-order algorithm with `T` queries in `B_p^d`. At round `t` (0-based) it
queries `query t h ∈ B_p^d`, where `h` lists the `t` oracle answers `(f(x_s), g_s)` received so
far; after `T` rounds it outputs `output h ∈ B_p^d`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, §2, (4), p.7 ("ALG outputs `x̂_T ∈ X`
after `T` queries", "At every query `x ∈ X`"), and Corollary 7, p.12 ("a deterministic algorithm").

**Formalization Note.** Determinism is the typing: queries and output are plain functions of the
answers received. Rounds are indexed from `0`. -/
structure FOAlgorithm (d T : ℕ) (p : ℝ≥0∞) where
  /-- The query at round `t`, from the `t` answers received so far. -/
  query : (t : Fin T) → (Fin t → ℝ × (Fin d → ℝ)) → (Fin d → ℝ)
  /-- The output after all `T` answers. -/
  output : (Fin T → ℝ × (Fin d → ℝ)) → (Fin d → ℝ)
  query_mem : ∀ t h, query t h ∈ lpBall p d
  output_mem : ∀ h, output h ∈ lpBall p d

end NondualOpt


