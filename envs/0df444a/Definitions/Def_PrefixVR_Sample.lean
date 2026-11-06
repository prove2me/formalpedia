-- Prove2me | Definitions.Def_PrefixVR_Sample
-- name    : PrefixVR_Sample
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:35:45.581196+00:00
-- url     : https://prove2.me/theorems/e359c08d-2902-4ad5-9e7c-03528322718f
-- title:
--   Sample space of Algorithm 1 and its expectation
-- statement:
--   Fix $n\ge1$ and a horizon $T$. An outcome of Algorithm 1 consists of the output index $\tau\in[T]$ and, for every update $t=1,\dots,T$ with cycle position $r$, a prefix draw $j_t\in[r-1]$ and an active draw $i_t\in[n]$. The **sample space** is the finite product of these sets, and the **expectation** of a function $F$ of the outcome is its uniform average
--   $$
--   \mathbb E[F]=\frac1{|\Omega|}\sum_{\omega\in\Omega}F(\omega).
--   $$
--   Under this law all draws are independent and uniform, $\tau$ is uniform on $[T]$ and independent of the estimator samples, as the paper prescribes.
--
--   The module also defines $\tau(\omega)$ (`tau`), the draw sequence (`drawSeq`), the number $\max(r-1,1)$ of values of the prefix draw (`jCard`) and the expectation (`expect`).
--
--   **Formalization Note** When $r=1$ the paper draws no $j_t$ and the coordinate is a one-point dummy; when $r=n$ the paper draws no $i_t$ and the coordinate is unused. Adding unused independent coordinates changes no expectation. Indices are 0-based (`Fin`).
-- source:
--   Jiang, Wang, Yang, Li, Zhang, Memory-efficient Finite-sum Optimization without Full Gradient Refreshes (manuscript, sha256 ed33106a…), §3, p.4 (PDF p.4) sampling conventions; Algorithm 1, lines 1, 14, 17, p.5; App. A, p.12

import Mathlib
import Definitions.Def_PrefixVR_step

namespace PrefixVR

/-- The number of values of the prefix draw at update `t`: `j_t ∼ Unif([r − 1])` has `r − 1`
values (Algorithm 1, line 14, p.5). At `r = 1` nothing is drawn; a one-point dummy is used. -/
def jCard (n t : ℕ) : ℕ := max (cyclePos n t - 1) 1

/-- **The sample space of Algorithm 1 with horizon `T`.**
Jiang, Wang, Yang, Li, Zhang (manuscript, sha256 ed33106a…), §3, p.4: "All component indices are
sampled freshly after the new iterate has been computed, independently of previous draws. The
uniform output index τ is independent of the estimator samples and is not used to construct the
trajectory"; Algorithm 1, lines 1, 14, 17, p.5; App. A, p.12: "the sample tree up to T has
finitely many branches".

An outcome is `(τ − 1, (j_t − 1, i_t − 1)_{t=1}^T)`: the output index `τ ∈ [T]` and, for each
update `t = k + 1`, the prefix draw `j_t ∈ [r − 1]` and the active draw `i_t ∈ [n]`. The law of
the draws is the uniform law on this finite set (see `expect`), i.e. the product of the uniform
laws, so all draws are independent and uniform as the paper prescribes.

**Formalization Note.** When `r = 1` the prefix coordinate is a one-point dummy and when `r = n`
the active coordinate is drawn but unused; adding unused independent coordinates changes no
expectation. Indices are 0-based (`Fin`). -/
abbrev Sample (n T : ℕ) : Type :=
  Fin T × ((k : Fin T) → Fin (jCard n (k.val + 1)) × Fin n)

/-- The output index `τ ∈ {1, …, T}` of an outcome (Algorithm 1, line 1, p.5). -/
def tau {n T : ℕ} (ω : Sample n T) : ℕ := ω.1.val + 1

/-- The draws of an outcome as a sequence: `drawSeq ω k = (j_{k+1} − 1, i_{k+1} − 1)` for the
update `t = k + 1 ≤ T`, and an unused default beyond the horizon. -/
def drawSeq {n T : ℕ} [NeZero n] (ω : Sample n T) (k : ℕ) : ℕ × Fin n :=
  if hk : k < T then (((ω.2 ⟨k, hk⟩).1 : ℕ), (ω.2 ⟨k, hk⟩).2) else (0, Fin.ofNat n 0)

/-- **Expectation over all randomness of Algorithm 1 with horizon `T`**: the uniform average
`𝔼[F] = |Ω|⁻¹ ∑_{ω ∈ Ω} F(ω)` over `Ω = Sample n T`, i.e. the expectation over the output
index `τ` and all estimator samples (Theorem 1, p.6; App. A, p.12).

**Formalization Note.** The joint law of independent uniform draws on finite sets is the uniform
law on their product, so this is the paper's `𝔼`. For `T ≥ 1` and `n ≥ 1` the set is nonempty. -/
noncomputable def expect {n T : ℕ} (F : Sample n T → ℝ) : ℝ :=
  (Fintype.card (Sample n T) : ℝ)⁻¹ * ∑ ω, F ω

end PrefixVR


