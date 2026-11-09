-- Prove2me | Definitions.Def_NAMatchEst_pilot
-- name    : NAMatchEst_pilot
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:53:51.811967+00:00
-- url     : https://prove2.me/theorems/ce766833-22e2-483f-9c91-888b8f143717
-- title:
--   The pilot sampling scheme (Definition 3.10)
-- statement:
--   The **pilot sampling scheme** of Definition 3.10. Take $s_0:=\lceil nL/\alpha^2\rceil$ independent full-row samples $u_1,\dots,u_{s_0}$. For each vertex $v$ let
--
--   $$
--   X_v:=\sum_{j=1}^{s_0}\mathbf 1\{u_j\in U\text{ and } v\in N(u_j)\},
--   $$
--
--   and output $H:=\{v: X_v\ge\lceil 128L\rceil\}$. Membership $u_j\in U$ is read from the degree answer and $v\in N(u_j)$ from the row of $u_j$.
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Definition 3.10, p.26 (PDF 30)

import Mathlib
import Definitions.Def_NAMatchEst_RandAlg
import Definitions.Def_ShallowShadows_ShadowNorm_uniformDist
import Definitions.Def_NAMatchEst_L
import Definitions.Def_NAMatchEst_Delta
import Definitions.Def_NAMatchEst_rowQueries
import Definitions.Def_NAMatchEst_rowNbrs

namespace NAMatchEst

/-- The **pilot sampling scheme** (Definition 3.10). Take `s₀ := ⌈nL/α²⌉` independent full-row
samples `u₁, …, u_{s₀}`; for each `v` let `X_v := Σ_j 1{u_j ∈ U and v ∈ N(u_j)}`; output
`H := {v : X_v ⩾ ⌈128L⌉}`.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Definition 3.10, p.26 (PDF 30): "Take s0 := ⌈nL/α²⌉ independent full-row samples u1, . . . ,
us0. For each v ∈ V, define Xv := Σ_{j=1}^{s0} 1{uj ∈ U and v ∈ N(uj)}, H := {v : Xv ⩾ ⌈128L⌉}.
Only labels appearing in retained rows can have positive counts. Thus the sampled information
explicitly determines H."

**Formalization Note** `u_j ∈ U` is read from the degree answer (`< ∆`), and `v ∈ N(u_j)` from the
first `∆` positions of the row of `u_j`, which list all of `N(u_j)` when `u_j ∈ U`. -/
noncomputable def pilot (n : ℕ) [NeZero n] (α : ℝ) (k : ℕ) : RandAlg n (Finset (Fin n)) :=
  open Classical in
  { Ω := Fin ⌈n * L n / α ^ 2⌉₊ → Fin n
    dist := ShallowShadows.ShadowNorm.uniformDist _
    queries := fun ω => (List.ofFn fun j => rowQueries (ω j) (Delta k α)).flatten
    output := fun ω d m => Finset.univ.filter fun v =>
      ⌈128 * L n⌉₊ ≤ (Finset.univ.filter fun j =>
        (∃ x ∈ d (ω j), x < Delta k α) ∧ v ∈ rowNbrs m (ω j) (Delta k α)).card }

end NAMatchEst


