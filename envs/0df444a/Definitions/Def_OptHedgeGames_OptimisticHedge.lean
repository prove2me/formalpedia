-- Prove2me | Definitions.Def_OptHedgeGames_OptimisticHedge
-- name    : OptHedgeGames_OptimisticHedge
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:39:25.683564+00:00
-- url     : https://prove2.me/theorems/59da2dcf-0114-45a0-a688-b2a321b6280a
-- title:
--   Optimistic Hedge (3) against a loss sequence, the regret (2), and the sums $D(T)$, $V(T)$ (4)
-- statement:
--   A player with $n$ actions runs **Optimistic Hedge** with learning rate $\eta$ against loss vectors $\ell^1,\ell^2,\dots$, with $\ell^0=0$: the first strategy $x^1$ is uniform and
--   $$
--   x^{t+1}(a)=\frac{x^t(a)\exp[-\eta(2\ell^t(a)-\ell^{t-1}(a))]}{\sum_c x^t(c)\exp[-\eta(2\ell^t(c)-\ell^{t-1}(c))]},\qquad\text{that is,}\quad x^{t+1}=E_{x^t}[-\eta(2\ell^t-\ell^{t-1})].
--   $$
--   The **regret** after $T$ rounds, the **total variation** and the **cumulative variance** are
--   $$
--   \mathrm{Reg}(T)=\sum_{t=1}^T\langle x^t,\ell^t\rangle-\min_a\sum_{t=1}^T\ell^t(a),\quad D(T)=\sum_{t=1}^T\|\ell^t-\ell^{t-1}\|^2_{x^t},\quad V(T)=\sum_{t=1}^T\|\ell^{t-1}\|^2_{x^t}.
--   $$
--   These are the quantities of the variance form of the RVU inequality (Lemma 3.1).
--
--   **Formalization Note** Rounds are indexed from $1$; the iterate at index $0$ is an unused value. The condition $\ell^0=0$ is a hypothesis on the sequence. `⨅ a` over `Fin n` is the minimum for $n\ge1$, the only case used.
-- source:
--   Dagan, Eisen, Erez & Koren, Optimistic Hedge in General-Sum Games, STOC 2027 submission manuscript (sha256 383e3793…), (2), (3), (4), p.4

import Mathlib
import Definitions.Def_OptHedgeGames_Notation

namespace OptHedgeGames

/-- The **uniform** strategy on `n` actions, with which Optimistic Hedge starts
(manuscript sha256 383e3793…, §2, p.4). -/
noncomputable def uniform (n : ℕ) : Fin n → ℝ :=
  fun _ => 1 / (n : ℝ)

/-- **Optimistic Hedge (3)** against a loss sequence `ℓ`: the strategy `xᵗ` of round `t ≥ 1`,
with `x¹` uniform and `xᵗ⁺¹ = E_{xᵗ}[−η(2ℓᵗ − ℓᵗ⁻¹)]`
(Dagan, Eisen, Erez & Koren, *Optimistic Hedge in General-Sum Games*, STOC 2027 submission
manuscript (sha256 383e3793…), (3), p.4).

**Formalization Note** Rounds are indexed from `1`, as in the paper; `ohIter η ℓ 0` is an unused
value (also uniform). The paper's `ℓ⁰ = 0` is `ℓ 0`, a hypothesis `ℓ 0 = 0` of the statements about
an arbitrary sequence (Lemma 3.1), and it holds by definition for the two-player run. -/
noncomputable def ohIter {n : ℕ} (η : ℝ) (ℓ : ℕ → Fin n → ℝ) : ℕ → Fin n → ℝ
  | 0 => uniform n
  | 1 => uniform n
  | t + 2 => tilt (ohIter η ℓ (t + 1)) (fun a => -η * (2 * ℓ (t + 1) a - ℓ t a))

/-- The **regret (2)** after `T` rounds of a player with strategies `x` and loss vectors `ℓ`,
`Reg(T) = Σ_{t=1}^T ⟨xᵗ, ℓᵗ⟩ − min_a Σ_{t=1}^T ℓᵗ(a)`
(manuscript sha256 383e3793…, (2), p.4).

**Formalization Note** `⨅ a : Fin n` over the finite type is the minimum for `n ≥ 1`; every statement
of the mission about regret assumes `1 ≤ n`. -/
noncomputable def reg {n : ℕ} (x ℓ : ℕ → Fin n → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, ∑ a, x t a * ℓ t a - ⨅ a, ∑ t ∈ Finset.Icc 1 T, ℓ t a

/-- The **total variation (4)**, `D(T) = Σ_{t=1}^T ∥ℓᵗ − ℓᵗ⁻¹∥²_{xᵗ}`, written with
`∥·∥²_p = Var_p` (manuscript sha256 383e3793…, (4), p.4).

**Formalization Note** `t - 1` is natural-number subtraction at `t ≥ 1`, so it is the paper's `t − 1`,
and `t = 1` reads `ℓ 0`. -/
noncomputable def totalVariation {n : ℕ} (x ℓ : ℕ → Fin n → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, var (x t) (ℓ t - ℓ (t - 1))

/-- The **cumulative variance (4)**, `V(T) = Σ_{t=1}^T ∥ℓᵗ⁻¹∥²_{xᵗ}`, written with
`∥·∥²_p = Var_p` (manuscript sha256 383e3793…, (4), p.4). The weight is the current strategy `xᵗ`,
and the loss is the previous one. -/
noncomputable def cumVariance {n : ℕ} (x ℓ : ℕ → Fin n → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, var (x t) (ℓ (t - 1))

end OptHedgeGames


