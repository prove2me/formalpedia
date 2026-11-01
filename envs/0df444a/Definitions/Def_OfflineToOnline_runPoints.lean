-- Prove2me | Definitions.Def_OfflineToOnline_runPoints
-- name    : OfflineToOnline_runPoints
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:34:11.147585+00:00
-- url     : https://prove2.me/theorems/ca0c1c98-016f-4a7e-9be1-2b8c4070daf3
-- title:
--   Points $z_t^{(i)}$ of $T$ runs of Algorithm 1 under a parameter policy
-- statement:
--   Fix an instance of Algorithm 1, a horizon $T$, a parameter policy $\theta$ that gives a parameter $\theta_t^{(i)}\in\mathbb R^{d_{\mathrm{param}}}$ for every run $t$ and subproblem $i$ as a function of the random seeds, and a seed realization $\omega=(\omega_{t,i})$. Run $t$ produces the points
--
--   $$
--   z_t^{(0)}=z^{(0)},\qquad z_t^{(i)}=\mathrm{update}\big(\theta_t^{(i)},\,z_t^{(i-1)},\,\omega_{t,i}\big)\quad(i=1,\dots,N),
--   $$
--
--   and outputs $z_t=z_t^{(N)}$. These are the points in which Definition 6 and Theorem 2 are stated.
--
--   **Formalization Note** Runs and subproblems are $0$-indexed: the paper's $\theta_t^{(i)}$ is the policy's value at subproblem index $i-1$, and $z_t^{(i)}$ is `runPoints I θ t i ω`. A helper `roundPoints` computes one round from that round's parameters and seeds.
-- source:
--   Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, Online Learning via Offline Greedy Algorithms: Applications in Market Design and Optimization, arXiv:2102.11050v4, Algorithm 1, p.14; Definition 6, p.16

import Mathlib
import Definitions.Def_OfflineToOnline_IGInstance

namespace OfflineToOnline

/-- One round of Algorithm 1 with given parameters: `z^(0) = z₀` and
`z^(i+1) = Local-update(θ^(i+1), z^(i))` (1-based `θ` on the page; here `θs ⟨i, _⟩`), driven by
the seeds `ωs`. Indices beyond `N` repeat `z^(N)`. -/
noncomputable def roundPoints {D Ω : Type*} [MeasurableSpace D] [MeasurableSpace Ω] {m d : ℕ}
    (I : IGInstance D Ω m d) (θs : Fin I.N → Fin m → ℝ) (ωs : Fin I.N → Ω) : ℕ → D
  | 0 => I.z₀
  | i + 1 =>
    if h : i < I.N then I.update (θs ⟨i, h⟩) (roundPoints I θs ωs i) (ωs ⟨i, h⟩)
    else roundPoints I θs ωs i

/-- The points of `T` runs of (a variant of) Algorithm 1 under a parameter policy `θ`:
`runPoints I θ t i ω = z_t^(i)` is the output of subproblem `i` in run `t` (and `z_t^(0) = z₀`),
when the seed of Local-update in subproblem `i + 1` of run `t` is `ω t i`. The run's output is
`z_t = runPoints I θ t N ω`.

Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, arXiv:2102.11050v4, Algorithm 1, p.14; Definition 6, p.16 ("z_t^(i) is the output of subproblem i ∈ [N] for run
t ∈ [T]").

Formalization Note: runs `t` and subproblems are `0`-indexed: the page's `θ_t^(i)` (`i ∈ [N]`) is
`θ t ⟨i − 1, _⟩ ω`, and the page's `z_t^(i)` is `runPoints I θ t i ω`. -/
noncomputable def runPoints {D Ω : Type*} [MeasurableSpace D] [MeasurableSpace Ω] {m d : ℕ}
    (I : IGInstance D Ω m d) {T : ℕ} (θ : Fin T → Fin I.N → (Fin T → Fin I.N → Ω) → Fin m → ℝ)
    (t : Fin T) (i : ℕ) (ω : Fin T → Fin I.N → Ω) : D :=
  roundPoints I (fun j => θ t j ω) (ω t) i

end OfflineToOnline


