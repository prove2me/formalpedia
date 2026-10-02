-- Prove2me | Definitions.Def_ProcessingNetworks_GlobalStability_AssemblySideBusiness
-- name    : ProcessingNetworks_GlobalStability_AssemblySideBusiness
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T18:11:26.318659+00:00
-- url     : https://prove2.me/theorems/110c03c5-a3b3-4ba6-a735-b17c2c22d3e7
-- title:
--   The assembly-with-side-business fluid model (Theorem 8.21's setting)
-- statement:
--   Figure 5.5's SPN: buffer 1 (external rate $\lambda_1$) holds components consumed one-at-a-time
--   by server 1's assembly activity together with a unit from buffer 2 (external rate $\lambda_2$);
--   server 2 alternatively sells buffer-2 units directly. Its fluid model consists of the base fluid
--   equations (6.1)–(6.6) for this SPN — with $T_a, T_s$ the cumulative service efforts of the
--   assembly and side-sale activities (nondecreasing from $0$, $1$-Lipschitz by the single-server
--   capacity bound), completions $T_a/m_1$ and $T_s/m_2$, and
--   $$
--   Z_1(t) = Z_1(0) + \lambda_1 t - T_a(t)/m_1, \qquad
--   Z_2(t) = Z_2(0) + \lambda_2 t - T_a(t)/m_1 - T_s(t)/m_2, \qquad Z \ge 0
--   $$
--   — together with, under the policy "assemble whenever both buffers are non-empty; sell directly
--   from buffer 2 whenever $Z_1 < Z_2$," the additional equations (8.36)-(8.39) that each fluid
--   limit path satisfies:
--   $$
--   \dot Z_1-\dot Z_2 = \lambda_1-\lambda_2 \ (Z_1{>}Z_2), \quad
--   \dot Z_1-\dot Z_2 = \lambda_1+\mu_2-\lambda_2 \ (Z_1{<}Z_2), \quad
--   \dot Z_1 = \lambda_1-\mu_1 \ (Z_1,Z_2{>}0), \quad
--   \dot Z_1 \le \lambda_1.
--   $$
--
--   **Formalization note.** This SPN has a genuinely multi-input assembly activity that Chapter
--   2's one-activity-per-buffer "unitary network" vocabulary cannot express, so — per this
--   mission's own `BRIEF.md` pitfall warning — it is not forced into `QueueingNetworkData`.
--   The additional equations (8.36)-(8.39), which the book itself presents as already-derived
--   ("using the proof techniques of Chapter 7") consequences of the true SPN dynamics, are stated
--   on the derivatives where they exist; the base equations (6.1)–(6.6) are what make every
--   solution Lipschitz (Lemma 8.3), so that these almost-everywhere derivative conditions have
--   force — without them a solution with a singular (Cantor-type) increasing part would satisfy
--   (8.36)-(8.39) vacuously and defeat every finite draining bound.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 150, Figure 5.5 and Eqs. (8.36)-(8.39)

import Mathlib

namespace ProcessingNetworks.GlobalStability

/-- The fluid model of the "assembly with complementary side business" SPN of Figure 5.5, Dai &
Harrison p. 150 (PDF p. 166): two buffers with external arrival rates `lam1`, `lam2`; server 1
performs assembly (one activity consuming a unit from each buffer, mean time `m1`); server 2
processes buffer-2 units alone for direct sale (mean time `m2`). This SPN has a genuinely
multi-input activity that Chapter 2's "unitary network" vocabulary (one activity per buffer) does
not cover, so it is restated locally via its already-derived additional fluid equations
(8.36)-(8.39) (obtained, the book notes, "using the proof techniques in Chapter 7" — not
re-derived here), on top of the base fluid equations (6.1)-(6.6) for this SPN: `Ta`, `Ts` are the
cumulative service efforts of the assembly and side-sale activities (nondecreasing from `0`,
`1`-Lipschitz by the capacity bound (6.6) with single servers), the completions are `Ta/m1` and
`Ts/m2` (6.4), and the buffer contents obey `Z1 = Z1(0) + λ1 t - Ta/m1`,
`Z2 = Z2(0) + λ2 t - Ta/m1 - Ts/m2` (6.1)/(6.3) with `Z ≥ 0` (6.2). -/
def AssemblySideBusinessFluidModel (lam1 lam2 m1 m2 : ℝ) (Z1 Z2 Ta Ts : ℝ → ℝ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → Z1 t = Z1 0 + lam1 * t - Ta t / m1) ∧
  (∀ t : ℝ, 0 ≤ t → Z2 t = Z2 0 + lam2 * t - Ta t / m1 - Ts t / m2) ∧
  (Ta 0 = 0 ∧ Ts 0 = 0) ∧
  (∀ s t : ℝ, 0 ≤ s → s ≤ t → 0 ≤ Ta t - Ta s ∧ Ta t - Ta s ≤ t - s) ∧
  (∀ s t : ℝ, 0 ≤ s → s ≤ t → 0 ≤ Ts t - Ts s ∧ Ts t - Ts s ≤ t - s) ∧
  (∀ t : ℝ, 0 ≤ t → 0 ≤ Z1 t ∧ 0 ≤ Z2 t) ∧
  (∀ t : ℝ, 0 < t → Z2 t < Z1 t →
    ∀ d1 d2 : ℝ, HasDerivAt Z1 d1 t → HasDerivAt Z2 d2 t → d1 - d2 = lam1 - lam2) ∧
  (∀ t : ℝ, 0 < t → Z1 t < Z2 t →
    ∀ d1 d2 : ℝ, HasDerivAt Z1 d1 t → HasDerivAt Z2 d2 t → d1 - d2 = lam1 + 1 / m2 - lam2) ∧
  (∀ t : ℝ, 0 < t → 0 < Z1 t → 0 < Z2 t → ∀ d1 : ℝ, HasDerivAt Z1 d1 t → d1 = lam1 - 1 / m1) ∧
  (∀ t : ℝ, 0 < t → ∀ d1 : ℝ, HasDerivAt Z1 d1 t → d1 ≤ lam1)

/-- Definition 6.3 (fluid model stability), specialized to the assembly-with-side-business fluid
model. -/
def AssemblySideBusinessFluidStable (lam1 lam2 m1 m2 : ℝ) : Prop :=
  ∃ γ : ℝ, 0 < γ ∧ ∀ Z1 Z2 Ta Ts : ℝ → ℝ,
    AssemblySideBusinessFluidModel lam1 lam2 m1 m2 Z1 Z2 Ta Ts →
    ∀ t : ℝ, γ * (Z1 0 + Z2 0) ≤ t → Z1 t = 0 ∧ Z2 t = 0

end ProcessingNetworks.GlobalStability


