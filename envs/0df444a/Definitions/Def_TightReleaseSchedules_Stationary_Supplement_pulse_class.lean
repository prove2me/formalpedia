-- Prove2me | Definitions.Def_TightReleaseSchedules_Stationary_Supplement_pulse_class
-- name    : TightReleaseSchedules_Stationary_Supplement_pulse_class
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T04:19:40.968136+00:00
-- url     : https://prove2.me/theorems/214171c8-5258-4185-b467-62f043125f88
-- title:
--   Total variation, change counts and the codebook pulse family
-- statement:
--   For a path $\theta_1,\dots,\theta_T\in\mathbb R^d$, its **total variation** is $\sum_{t=2}^{T}\|\theta_t-\theta_{t-1}\|_2$ and its **change count** is the number of rounds $t\in\{2,\dots,T\}$ with $\theta_t\neq\theta_{t-1}$ (a return to an earlier value counts).
--
--   Fix integers $K,N,h\ge1$ and a codebook $u_1,\dots,u_M\in\mathbb R^d$. The **pulse family** is the hard family of Theorem 6.1. Round $1$ has target $0$. Rounds $2,\dots,1+KNh$ are split into $K$ consecutive phases, each made of $N$ consecutive blocks of $h$ rounds. A path in the family is determined by an activity indicator $Z_p\in\{0,1\}$, a block $J_p\in\{1,\dots,N\}$ and a codeword index $V_p\in\{1,\dots,M\}$ for each phase $p$. If $Z_p=1$, the target is $u_{V_p}$ on block $J_p$ of phase $p$ and $0$ on the rest of the phase. If $Z_p=0$, the whole phase is $0$. All rounds after $1+KNh$ have target $0$.
--
--   **Formalization Note** Round $t$ is index $t-1$ of `Fin T`; block $j$ of phase $p$ (both $0$-based) occupies indices $1+(pN+j)h,\dots,(pN+j+1)h$. A pulse path is written as a sum over phases of indicator terms; the phase blocks are disjoint, so at most one term is nonzero.
-- source:
--   Jing Wang, When to Update a Pretrained Model: Tight Release Schedules under Distribution Shift, STOC 2027 submission #1096 (October 2026), §6 and Theorem 6.1 with proof Step 1, printed p.21, PDF p.22

import Definitions.Def_TightReleaseSchedules_Stationary_release_policy

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
noncomputable section

namespace TightReleaseSchedules.Stationary.Supplement

open TightReleaseSchedules.Stationary

/-- Total variation `∑_{t=2}^{T} ‖θ_t − θ_{t−1}‖₂` of a path (index `i` is round `i + 1`). -/
def totalVariation {T d : ℕ} (θ : Fin T → Vector d) : ℝ :=
  ∑ i : Fin T, if h : i.val + 1 < T then ‖θ ⟨i.val + 1, h⟩ - θ i‖ else 0

/-- The number of rounds `t ∈ {2, …, T}` with `θ_t ≠ θ_{t−1}` (returns to a previous value
count as changes). -/
def changeCount {T d : ℕ} (θ : Fin T → Vector d) : ℕ :=
  (Finset.univ.filter (fun i : Fin T => ∃ h : i.val + 1 < T, θ ⟨i.val + 1, h⟩ ≠ θ i)).card

/-- A path of the pulse construction (Theorem 6.1, proof Step 1): round 1 (index 0) has
target zero; rounds `2, …, 1 + KNh` form `K` phases of `N` blocks of length `h`; phase `p` is
active iff `Z p`, and then its target is `u (V p)` on its block `J p` (indices
`1 + (pN + J_p)h ≤ i < 1 + (pN + J_p + 1)h`) and zero elsewhere; remaining rounds are zero. -/
def pulsePath {T d K N M : ℕ} (h : ℕ) (u : Fin M → Vector d)
    (Z : Fin K → Bool) (J : Fin K → Fin N) (V : Fin K → Fin M) : Fin T → Vector d :=
  fun i => ∑ p : Fin K,
    if Z p = true ∧ 1 + (p.val * N + (J p).val) * h ≤ i.val ∧
        i.val < 1 + (p.val * N + (J p).val + 1) * h then u (V p) else 0

/-- The hard family of Theorem 6.1: all pulse paths for the codebook `u`. -/
def pulseFamily (T d K N M h : ℕ) (u : Fin M → Vector d) : Set (Fin T → Vector d) :=
  {θ | ∃ (Z : Fin K → Bool) (J : Fin K → Fin N) (V : Fin K → Fin M), θ = pulsePath h u Z J V}

end TightReleaseSchedules.Stationary.Supplement


