-- Prove2me | Definitions.Def_ApproxGKR_SCAccepts
-- name    : ApproxGKR_SCAccepts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:27:44.578373+00:00
-- url     : https://prove2.me/theorems/1844f84b-f86d-4e1d-8e49-b2ddd2c220d0
-- title:
--   One run of approximate sum-check: provers, verifier implementations and acceptance
-- statement:
--   Approximate sum-check for a polynomial $f$ in $n_v$ variables over $H^{n_v}$, with challenges $r\in\Omega_N^{n_v}$ (by index). A **prover** sends round polynomials $p_j$ ($j\ge1$) as functions of the challenges, and is *adapted* if $p_j$ depends only on $r_1,\dots,r_{j-1}$. A **verifier implementation** gives the computed residual of round $j$ and the computed next claim $Y_j$; it is *within $\Delta_0$* if the residual is within $\Delta_0$ of $Y_{j-1}-\sum_{a\in H}p_j(a)$ (with $Y_0$ the initial claim) and $Y_j$ within $\Delta_0$ of $p_j(r_j)$. The run **accepts** if every $p_j$ has degree at most $D$ and every computed residual has modulus at most $6\Delta_0$ (step 1, p.33).
-- source:
--   Das, Gupta, Mondal, More, Delegating Computation with Approximate Arithmetic: Interactive Proofs for Wizards (manuscript, sha256 78b2a36b…), §C.1 step 1, p.33; Lemma C.3, p.37

import Mathlib
import Definitions.Def_ApproxGKR_root

namespace ApproxGKR

/-! One run of approximate sum-check (step 1 of §C.1, p.33; Lemma C.3, p.37) for a polynomial in
`nv` variables, with challenges `r ∈ Ω_N^{nv}` given by indices. -/

/-- A sum-check prover: the round polynomial `p_j` (round `j ≥ 1`) as a function of the
challenge indices. -/
structure SCProver (nv N : ℕ) where
  poly : ℕ → (Fin nv → Fin N) → Polynomial ℂ

/-- The prover cannot see future challenges: `p_j` depends only on `r₁, …, r_{j−1}` ("Each
polynomial is sent before its challenge is sampled", p.32). Otherwise it is arbitrary (adaptive,
unbounded). -/
def SCProver.Adapted {nv N : ℕ} (P : SCProver nv N) : Prop :=
  ∀ (j : ℕ) (r r' : Fin nv → Fin N), (∀ v : Fin nv, (v : ℕ) + 1 < j → r v = r' v) →
    P.poly j r = P.poly j r'

/-- A sum-check verifier implementation: the computed residual of round `j` and the computed
next claim `Y_j`, as arbitrary functions of the challenges. -/
structure SCVerifier (nv N : ℕ) where
  res : ℕ → (Fin nv → Fin N) → ℂ
  Y : ℕ → (Fin nv → Fin N) → ℂ

/-- The claim `Y_j`: the initial claim `Y₀` for `j = 0`, the computed `Y_j` afterwards. -/
def scClaim {nv N : ℕ} (Y0 : ℂ) (V : SCVerifier nv N) (r : Fin nv → Fin N) (j : ℕ) : ℂ :=
  if j = 0 then Y0 else V.Y j r

/-- The verifier's arithmetic error is at most `∆₀` ("the tolerance and arithmetic error
specified above", Lemma C.3): the computed residual is within `∆₀` of `Y_{j−1} − Σ_{a∈H} p_j(a)`
and the computed next claim within `∆₀` of `p_j(r_j)` (step 1, p.33). -/
def SCVerifier.Within {nv N : ℕ} (V : SCVerifier nv N) (P : SCProver nv N) (Y0 : ℂ) (h : ℕ)
    (Δ₀ : ℝ) : Prop :=
  ∀ (r : Fin nv → Fin N) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ nv),
    ‖V.res j r - (scClaim Y0 V r (j - 1) - ∑ a : Fin h, (P.poly j r).eval (root h a.val))‖ ≤ Δ₀ ∧
    ‖V.Y j r - (P.poly j r).eval (root N (r ⟨j - 1, by omega⟩).val)‖ ≤ Δ₀

/-- **Acceptance of sum-check**: every round polynomial has degree at most `D` and every computed
residual has modulus at most `6∆₀` (step 1, p.33: "receive a degree-at-most-`D` polynomial `p_j`
and reject if the computed residual … has modulus greater than `6∆0`").

Das, Gupta, Mondal, More, *Delegating Computation with Approximate Arithmetic* (manuscript,
sha256 78b2a36b…), §C.1 step 1, p.33; Lemma C.3, p.37. -/
def SCAccepts {nv N : ℕ} (P : SCProver nv N) (V : SCVerifier nv N) (D : ℕ) (Δ₀ : ℝ)
    (r : Fin nv → Fin N) : Prop :=
  ∀ j, 1 ≤ j → j ≤ nv → (P.poly j r).natDegree ≤ D ∧ ‖V.res j r‖ ≤ 6 * Δ₀

end ApproxGKR


