-- Prove2me | Definitions.Def_StationaryBwK_Play
-- name    : StationaryBwK_Play
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:50:33.755668+00:00
-- url     : https://prove2.me/theorems/9b4b78ce-4842-4f09-a0c3-8afa618c2773
-- title:
--   Pathwise objects of Algorithm 1: $\rho$, $T_A$, $\mathrm{REW}$, $\mathcal L_t(a,i)$, $Z_\tau(a)$
-- statement:
--   Fix one outcome of a run with $T$ rounds, budget $B$, rewards $R_t(a)$, consumptions $C_{t,i}(a)$, played actions $A_t\in[K]$ and choices $I_t\in[d]\cup\{0\}$ of the minimizing subroutine. This definition introduces:
--
--   1. the per-round budget $\rho=B/T$;
--   2. the **stopping round** $T_A=\max\{t\in[T]:\ \forall i\in[d],\ \sum_{\tau=1}^{t}C_{\tau,i}(A_\tau)\le B\}$, the last round in which the player receives a reward, with $T_A=0$ if no round qualifies;
--   3. the **total reward** $\mathrm{REW}=\sum_{t=1}^{T_A}R_t(A_t)$;
--   4. the **Lagrangian** $\mathcal L_t(a,i)=R_t(a)+\frac1\rho\mathbb 1[i\ne0](\rho-C_{t,i}(a))$ for $a\in[K]$, $i\in[d]\cup\{0\}$;
--   5. for given conditional means $r_t(a)$, $c_{t,i}(a)$, the process
--   $$Z_\tau(a)=\sum_{t=1}^{\tau}(R_t(a)-r_t(a))+\sum_{t=1}^{\tau}\frac{\mathbb 1[I_t>0]}{\rho}\big(c_{t,I_t}(a)-C_{t,I_t}(a)\big),\qquad \tau\in\{0\}\cup[T].$$
--
--   Algorithm 1 feeds $\mathcal L_t(A_t,I_t)$ to its maximizing subroutine and $\mathcal L_t(A_t,i)$ for every $i$ to its minimizing one; $T_A$ and $\mathrm{REW}$ are the quantities its guarantee is about, and $Z_\tau(a)$ is the martingale of the proof of Lemma 5.1.
--
--   **Formalization Note** Everything is evaluated at one outcome $\omega$ of an arbitrary type. $i\in[d]\cup\{0\}$ is `Option (Fin d)` with `none` $=0$. In $Z_\tau(a)$ the printed $C_{t,I_t}(A)$ is read as $C_{t,I_t}(a)$, as in the display that follows it.
-- source:
--   G. Fikioris and É. Tardos, Approximately Stationary Bandits with Knapsacks, arXiv:2302.14686v2 [cs.LG] (preprint, 8 Jul 2023), https://arxiv.org/abs/2302.14686v2, §2, pp.5–6 (ρ, T_A); §4, p.7 (REW), p.8 (Algorithm 1, L_t(a,i)); proof of Lemma 5.1, p.16 (Z_τ(a))

import Mathlib

namespace StationaryBwK

/-! # Pathwise objects of a run of Algorithm 1

Fikioris & Tardos, *Approximately Stationary Bandits with Knapsacks*, arXiv:2302.14686v2:
`ρ = B/T` (§2, p.5), the stopping round `T_A` (§2, p.6), the reward `REW` (§4, p.7), the
Lagrangian `L_t(a, i)` (§4, p.8, Algorithm 1 lines 5–6), and the process `Z_τ(a)` (proof of
Lemma 5.1, p.16).

**Formalization Note.** Everything here is evaluated at one outcome `ω : Ω` of an arbitrary type.
Rounds `t = 1, …, T` are natural numbers (round `0` unused). `R t ω a` is the reward `R_t(a)`,
`C t ω i a` the consumption `C_{t,i}(a)`, `A t ω : Fin K` the played action `A_t`, and
`I t ω : Option (Fin d)` the choice `I_t` of `Alg_min`, where `none` is the paper's `i = 0` and
`some i` is resource `i ∈ [d]`. -/

/-- `ρ = B / T` (p.5). -/
noncomputable def rho (T : ℕ) (B : ℝ) : ℝ := B / T

/-- `T_A = max {t ∈ [T] : ∀ i ∈ [d], Σ_{τ=1}^{t} C_{τ,i}(A_τ) ≤ B}` (p.6), the last round in which
the player receives a reward.

**Formalization Note.** If the set is empty (round 1 already exceeds a budget) then `T_A = 0`, so
that the player receives no reward. -/
noncomputable def stopTime {Ω : Type*} {d K : ℕ} (T : ℕ) (B : ℝ)
    (C : ℕ → Ω → Fin d → Fin K → ℝ) (A : ℕ → Ω → Fin K) (ω : Ω) : ℕ :=
  ((Finset.Icc 1 T).filter
    (fun t => ∀ i : Fin d, ∑ τ ∈ Finset.Icc 1 t, C τ ω i (A τ ω) ≤ B)).sup id

/-- `REW = Σ_{t=1}^{T_A} R_t(A_t)` (p.7). -/
noncomputable def rew {Ω : Type*} {d K : ℕ} (T : ℕ) (B : ℝ) (R : ℕ → Ω → Fin K → ℝ)
    (C : ℕ → Ω → Fin d → Fin K → ℝ) (A : ℕ → Ω → Fin K) (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.Icc 1 (stopTime T B C A ω), R t ω (A t ω)

/-- The penalty part `(1/ρ) 1[i ≠ 0] (ρ − C_{t,i}(a))` of the Lagrangian (p.8). -/
noncomputable def penalty {Ω : Type*} {d K : ℕ} (ρ : ℝ) (C : ℕ → Ω → Fin d → Fin K → ℝ)
    (t : ℕ) (ω : Ω) (a : Fin K) : Option (Fin d) → ℝ
  | none => 0
  | some i => (1 / ρ) * (ρ - C t ω i a)

/-- The Lagrangian `L_t(a, i) = R_t(a) + (1/ρ) 1[i ≠ 0] (ρ − C_{t,i}(a))` for `a ∈ [K]` and
`i ∈ [d] ∪ {0}` (p.8). -/
noncomputable def lagr {Ω : Type*} {d K : ℕ} (ρ : ℝ) (R : ℕ → Ω → Fin K → ℝ)
    (C : ℕ → Ω → Fin d → Fin K → ℝ) (t : ℕ) (ω : Ω) (a : Fin K) (j : Option (Fin d)) : ℝ :=
  R t ω a + penalty ρ C t ω a j

/-- The process of the proof of Lemma 5.1 (p.16), for `τ ∈ {0} ∪ [T]` and `a ∈ [K]`:
`Z_τ(a) = Σ_{t=1}^{τ} (R_t(a) − r_t(a)) + Σ_{t=1}^{τ} (1[I_t > 0]/ρ) (c_{t,I_t}(a) − C_{t,I_t}(a))`.

**Formalization Note.** `r t a ω` and `c t i a ω` are the conditional expected reward and
consumption, passed as arguments; in the random statements they are `rCond` and `cCond`. The
printed `C_{t,I_t}(A)` is read as `C_{t,I_t}(a)`, as in the display that follows it on p.16. -/
noncomputable def zProc {Ω : Type*} {d K : ℕ} (ρ : ℝ) (R : ℕ → Ω → Fin K → ℝ)
    (C : ℕ → Ω → Fin d → Fin K → ℝ) (r : ℕ → Fin K → Ω → ℝ) (c : ℕ → Fin d → Fin K → Ω → ℝ)
    (I : ℕ → Ω → Option (Fin d)) (τ : ℕ) (a : Fin K) (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.Icc 1 τ, (R t ω a - r t a ω) +
    ∑ t ∈ Finset.Icc 1 τ,
      (match I t ω with
        | none => 0
        | some i => (1 / ρ) * (c t i a ω - C t ω i a))

end StationaryBwK


