-- Prove2me | Definitions.Def_FocusSetRB_scaledCount
-- name    : FocusSetRB_scaledCount
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:17:53.18344+00:00
-- url     : https://prove2.me/theorems/b28e9c77-4eb4-49c3-a370-34a382df3de9
-- title:
--   Scaled state counts $x(D)$, $m(D)$, the slack $\delta(x,D)$, $h_W$, and one step of the $N$-armed system
-- statement:
--   Arms are indexed by $[N]$. A **system state** is a state vector $x\in\mathbb S^N$. For $D\subseteq[N]$:
--
--   1. the **scaled state-count vector on $D$** is $x(D,s)=\frac1N\sum_{i\in D}\mathbb 1\{x(i)=s\}$;
--   2. $m(D)=|D|/N$ is the fraction of arms in $D$;
--   3. the **slack** of $D$ is
--   $$
--   \delta(x,D)=\beta\big(1-m(D)\big)-\tfrac12\,\|x(D)-m(D)\mu^*\|_1 ;
--   $$
--   4. the **subset Lyapunov function** of the set-expansion policy is $h_W(x,D)=\|x(D)-m(D)\mu^*\|_W$.
--
--   One step of the system: the ideal actions $\hat A(i)\sim\bar\pi^*(\cdot\mid x(i))$ are drawn independently across arms, with joint law $\prod_i\bar\pi^*(\hat A(i)\mid x(i))$; given an action vector $A$, the arms move independently, the next state vector being $x'$ with probability $\prod_iP(x(i),A(i),x'(i))$. When the arms of $D$ take their ideal actions and the arms outside $D$ take actions $a_{\mathrm{out}}$, the action vector is $\hat A$ on $D$ and $a_{\mathrm{out}}$ off $D$.
--
--   **Formalization Note** Arms are `Fin N`, numbered from $0$. A system state is stored as its state vector, which carries the same information (p.6).
-- source:
--   Hong, Xie, Chen, Wang, Unichain and Aperiodicity are Sufficient for Asymptotic Optimality of Average-Reward Restless Bandits, arXiv:2402.05689v4, §3.2, p.6; §3.5, p.7; eq. (6), p.7; eq. (32), p.17; §3.1, p.5; Algorithm 1, line 3, p.8

import Mathlib
import Definitions.Def_FocusSetRB_W

namespace FocusSetRB

open Finset

variable {S : Type*} [Fintype S] [DecidableEq S] {N : ℕ}

/-- The **scaled state-count vector on `D`** (arXiv:2402.05689v4, §3.2, p.6):
`x(D, s) = (1/N) ∑_{i ∈ D} 𝟙{x(i) = s}` for a state vector `x ∈ 𝕊^N` and `D ⊆ [N]`.

**Formalization Note.** Arms are `Fin N` (0-based) for `[N]`; a system state is represented by
the state vector `x : Fin N → S` (the source notes that the system state and the state vector
carry the same information). -/
noncomputable def scaledCount (x : Fin N → S) (D : Finset (Fin N)) (s : S) : ℝ :=
  ((D.filter fun i => x i = s).card : ℝ) / N

/-- `m(D) = |D| / N`, the fraction of arms in `D` (arXiv:2402.05689v4, §3.5, p.7). -/
noncomputable def frac (D : Finset (Fin N)) : ℝ := (D.card : ℝ) / N

/-- `‖x(D) − m(D) μ*‖₁ = ∑_s |x(D, s) − m(D) μ*(s)|` (arXiv:2402.05689v4, eq. (6), p.7). -/
noncomputable def l1Dev (y : S → Bool → ℝ) (x : Fin N → S) (D : Finset (Fin N)) : ℝ :=
  ∑ s, |scaledCount x D s - frac D * muStar y s|

/-- The **slack** of `D` at system state `x` (arXiv:2402.05689v4, §4.2, eq. (6), p.7):
`δ(x, D) = β(1 − m(D)) − ½ ‖x(D) − m(D) μ*‖₁`, with `β = min{α, 1 − α}`. -/
noncomputable def slack (α : ℝ) (y : S → Bool → ℝ) (x : Fin N → S) (D : Finset (Fin N)) : ℝ :=
  beta α * (1 - frac D) - 1 / 2 * l1Dev y x D

/-- The subset Lyapunov function `h_W(x, D) = ‖x(D) − m(D) μ*‖_W` (arXiv:2402.05689v4,
eq. (32), p.17). -/
noncomputable def hW (M : SingleArmMDP S) (y : S → Bool → ℝ) (x : Fin N → S)
    (D : Finset (Fin N)) : ℝ :=
  normW M y (fun s => scaledCount x D s - frac D * muStar y s)

/-- The law of the **ideal actions** `Â(i) ∼ π̄*(· | x(i))`, sampled independently across arms
(arXiv:2402.05689v4, Algorithm 1, line 3, p.8): `P(Â) = ∏_i π̄*(Â(i) | x(i))`. -/
noncomputable def idealLaw (y : S → Bool → ℝ) (x : Fin N → S) (Ahat : Fin N → Bool) : ℝ :=
  ∏ i, piBar y (x i) (Ahat i)

/-- One step of the `N`-armed system (arXiv:2402.05689v4, §3.1, p.5): given the state vector `x`
and the action vector `A`, the arms move independently, so the next state vector is `x'` with
probability `∏_i P(x(i), A(i), x'(i))`. -/
noncomputable def stepProb (M : SingleArmMDP S) (x : Fin N → S) (A : Fin N → Bool)
    (x' : Fin N → S) : ℝ :=
  ∏ i, M.P (x i) (A i) (x' i)

/-- The action vector in which the arms of `D` take the ideal actions `Â` and the other arms take
the actions `aOut`; it encodes the conditioning "`A₀(i) ∼ π̄*(· | S₀(i))` for all `i ∈ D`" of
(12), (33) and (115) (arXiv:2402.05689v4, pp.13, 18, 48), the actions outside `D` being left
arbitrary. -/
def followOn (D : Finset (Fin N)) (Ahat aOut : Fin N → Bool) : Fin N → Bool :=
  fun i => if i ∈ D then Ahat i else aOut i

end FocusSetRB


