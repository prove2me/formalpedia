-- Prove2me | Definitions.Def_NewtonLCP_LPOracle
-- name    : NewtonLCP_LPOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:28:42.952283+00:00
-- url     : https://prove2.me/theorems/0549e437-5933-4deb-80ef-5b11060e155b
-- title:
--   The LP oracle LPSolve
-- statement:
--   For fixed $(M,q)$ and index sets $I,J\subseteq[n]$, the linear program solved by LPSolve is
--
--   $$Mx+q=s,\quad x,s\ge0_n,\quad x_I=0_I,\quad s_J=0_J .$$
--
--   An **LP oracle** maps $(I,J)$ to a point $(x,s)$ or to "infeasible". It is **correct** if every returned point is feasible for the LP above and "infeasible" is returned only when the LP has no feasible point.
--
--   Algorithm 3 calls the oracle once with $I=J=\emptyset$ (line 15) and once per successful run of FixedKappaNewton (line 28); Theorem 1.2 counts these calls.
--
--   **Formalization Note** The theorems quantify over every correct oracle; any LP solver is one.
-- source:
--   Ma–Végh–Vladu, Newton Steps are Faster for Linear Complementarity Problems, STOC 2027 submission (manuscript sha256 a70e5eab…), Theorem 1.2, p.3; Algorithm 3 lines 15 and 28, p.32

import Mathlib
import Definitions.Def_NewtonLCP_LCP

namespace NewtonLCP

/-!
# The LP oracle `LPSolve`

Ma–Végh–Vladu, *Newton Steps are Faster for Linear Complementarity Problems*, STOC 2027
submission manuscript (sha256 a70e5eab…40f8), Theorem 1.2, p.3 (linear programs
`Mx + q = s, x, s ≥ 0ₙ, x_I = 0_I, s_J = 0_J`); Algorithm 3 lines 15 and 28, p.32.

**Formalization Note.** An LP oracle for fixed `(M, q)` is a function of the index sets
`I, J ⊆ [n]` returning `some (x, s)` or `none`. `IsLPOracle M q O` says: an answer `some (x, s)`
is a feasible point of `F(M, q)` with `x_I = 0`, `s_J = 0`, and the answer `none` is returned only
when no such point exists. Line 15 is the call with `I = J = ∅`. Any LP solver meets this
specification; the theorems quantify over every such oracle.
-/

/-- An LP oracle for an `n`-dimensional instance: `I ↦ J ↦ some (x, s)` or `none`. -/
abbrev LPOracle (n : ℕ) : Type :=
  Finset (Fin n) → Finset (Fin n) → Option ((Fin n → ℝ) × (Fin n → ℝ))

/-- `O` correctly solves every LP `Mx + q = s, x, s ≥ 0, x_I = 0, s_J = 0`. -/
def IsLPOracle {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (q : Fin n → ℝ) (O : LPOracle n) : Prop :=
  ∀ I J : Finset (Fin n),
    (∀ x s, O I J = some (x, s) →
      (x, s) ∈ Feas M q ∧ (∀ i ∈ I, x i = 0) ∧ (∀ j ∈ J, s j = 0)) ∧
    (O I J = none →
      ¬ ∃ x s, (x, s) ∈ Feas M q ∧ (∀ i ∈ I, x i = 0) ∧ (∀ j ∈ J, s j = 0))

end NewtonLCP


