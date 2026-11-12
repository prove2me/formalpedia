-- Prove2me | Definitions.Def_QPVEntanglement_Schedule
-- name    : QPVEntanglement_Schedule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:27:55.917287+00:00
-- url     : https://prove2.me/theorems/31656889-4d8a-4542-acb2-aff3ce4f7c7a
-- title:
--   Timing schedule of the slot-randomized BB84 protocol (Figure 3)
-- statement:
--   A **schedule** for $m$ rounds of $s$ slots with $R_H$ stored states fixes a slot spacing $\Delta>0$, round base times $\tau_k$ ($k<m$), send times $\sigma^0_h$ of the initial BB84 states (nondecreasing in the label $h<R_H$) and send times $\sigma^r_k$ of the replenishment state after round $k$ ($k\le m-2$). Slot $j$ of round $k$ has logical time $T_{k,j}=\tau_k+j\Delta$; if $V_b$ is selected, its instruction is emitted at $T_{k,j}-d_b$ and the honest response is due at $V_b$ at $T_{k,j}+d_b$. The schedule must satisfy
--
--   1. (S1) $\sigma^0_h+\ell_{01}\le \tau_0-D$: the initial states reach $V_1$ before the first round begins;
--   2. (S2) $\tau_k+(s-1)\Delta+D\le\sigma^r_k$: round $k$ is over before its replenishment is sent;
--   3. (S3) $\sigma^r_k+\ell_{01}\le\tau_{k+1}-D$: the replenishment reaches $V_1$ before round $k+1$ begins.
--
--   The experiment ends at $T_{\mathrm{end}}=\tau_{m-1}+(s-1)\Delta+D$. There are $N_L=R_H+(m-1)$ labels; the replenishment after round $k$ has label $R_H+k$.
--
--   These are protocol rules 2, 3 and 5 of the paper. The statements of the mission quantify over every schedule, which expresses that the protocol is slot-based and that its security does not depend on the inter-slot delay (Definition 3).
--
--   **Formalization Note** Rounds, slots and labels are $0$-based; no replenishment follows the last round.
-- source:
--   Behera, Goyal, Breaking the Bounded Entanglement Barrier for Quantum Position Verification, arXiv:2609.39234 (sha256 bdf2928d…), Figure 3, p.31; protocol rules 2, 3, 5, pp.30–32; Definition 3, p.29

import Mathlib
import Definitions.Def_QPVEntanglement_Geometry

set_option autoImplicit false

namespace QPVEntanglement

/-- Number of permanent BB84 labels: `R_H` initial ones and one replenishment after each round
but the last, `NL = R_H + (m − 1)` (p.36: "The initialization labels are `1, …, R_H`, and the
state added before round `k > 1` has label `R_H + k − 1`"). -/
abbrev NL (m RH : ℕ) : ℕ := RH + (m - 1)

/-- **Timing schedule of the slot-randomized BB84 protocol** (Figure 3, p.31; protocol rules 2,
3, 5, pp.30–32; Definition 3, p.29). Behera–Goyal, arXiv:2609.39234 (sha256 bdf2928d…),
Figure 3, p.31.

* `Δ > 0` is the slot spacing and `τ k` the base time of round `k`; the logical time of slot `j`
  of round `k` is `T k j = τ k + j·Δ` ("logical times `T₁ < ⋯ < T_s` with fixed spacing `Δ`",
  Definition 3);
* `σ0 h` is the time at which `V₀` sends the initial BB84 state of label `h` (monotone: "send
  the states to `P` in label order"), and `σr k` the time at which it sends the replenishment
  after round `k`;
* (S1) before the first round the verifiers wait until the initial states would reach `V₁`
  (rule 2); a round begins at its earliest instruction emission `T k 0 − D`;
* (S2) all operations of round `k` (its last deadline is at most `T k (s−1) + D`) finish before
  the replenishment is sent (rule 5);
* (S3) the replenishment would reach `V₁` before round `k + 1` begins (rule 2).

**Formalization Note.** Pinned model P2–P3 (BRIEF). Rounds, slots and labels are 0-based. The
paper never fixes concrete times; the theorems quantify over **every** schedule satisfying
(S1)–(S3) and every `Δ > 0`, which carries "slot-based" (the form `τ k + jΔ`) and
"inter-slot-delay independent" (every `Δ`, Definition 3). No replenishment is sent after the
last round (nothing tests it). -/
structure Schedule (G : Geometry) (m RH s : ℕ) where
  /-- slot spacing -/
  Δ : ℝ
  Δ_pos : 0 < Δ
  /-- base time of each round -/
  τ : Fin m → ℝ
  /-- send times of the initial states, in label order -/
  σ0 : Fin RH → ℝ
  σ0_mono : Monotone σ0
  /-- send time of the replenishment state after round `k` (`k ≤ m − 2`) -/
  σr : Fin (m - 1) → ℝ
  /-- (S1) initial states reach `V₁` before the first round begins -/
  S1 : ∀ (h : Fin RH) (k : Fin m), k.val = 0 → σ0 h + G.len ≤ τ k - G.D
  /-- (S2) round `k` is complete before its replenishment is sent -/
  S2 : ∀ k : Fin (m - 1), τ ⟨k.val, by omega⟩ + ((s : ℝ) - 1) * Δ + G.D ≤ σr k
  /-- (S3) the replenishment reaches `V₁` before round `k + 1` begins -/
  S3 : ∀ k : Fin (m - 1), σr k + G.len ≤ τ ⟨k.val + 1, by omega⟩ - G.D

namespace Schedule

variable {G : Geometry} {m RH s : ℕ}

/-- Logical time `T k j = τ k + j·Δ` of slot `j` of round `k` (rule 3: the time at which the
selected verifier's instruction reaches the claimed location). -/
noncomputable def T (S : Schedule G m RH s) (k : Fin m) (j : Fin s) : ℝ := S.τ k + (j : ℝ) * S.Δ

/-- Emission time `T k j − d_b` of `V_b`'s instruction for slot `j` of round `k` (rule 3, p.36). -/
noncomputable def emit (S : Schedule G m RH s) (k : Fin m) (b : Fin 2) (j : Fin s) : ℝ :=
  S.T k j - G.d b

/-- Honest-response deadline `T k j + d_b` at `V_b` for slot `j` of round `k` (rule 3, p.36). -/
noncomputable def deadline (S : Schedule G m RH s) (k : Fin m) (b : Fin 2) (j : Fin s) : ℝ :=
  S.T k j + G.d b

/-- End of the experiment: the latest possible deadline of the last round,
`τ (m−1) + (s−1)Δ + D` (`0` when there are no rounds). -/
noncomputable def Tend (S : Schedule G m RH s) : ℝ :=
  if h : 0 < m then S.τ ⟨m - 1, by omega⟩ + ((s : ℝ) - 1) * S.Δ + G.D else 0

/-- Send time of the BB84 state of label `h`: `σ0 h` for an initial label, `σr k` for the
replenishment label `R_H + k`. -/
noncomputable def sendTime (S : Schedule G m RH s) (h : Fin (NL m RH)) : ℝ :=
  if h1 : h.val < RH then S.σ0 ⟨h.val, h1⟩ else S.σr ⟨h.val - RH, by have := h.isLt; simp only [NL] at this; omega⟩

end Schedule

end QPVEntanglement


