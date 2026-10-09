-- Prove2me | Definitions.Def_LinearMDPRL_Linear_LSVIUCB
-- name    : LinearMDPRL_Linear_LSVIUCB
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T01:44:05.560341+00:00
-- url     : https://prove2.me/theorems/fc8b83e8-9c67-4196-9170-42f150d86797
-- title:
--   Algorithm 1, p. 6 — LSVI-UCB: Gram matrix Λ^k_h, weights w^k_h, estimates Q^k_h, V^k_h, greedy policy; the interaction (pp. 4–5) and Regret(K) (p. 5)
-- statement:
--   This file defines **Least-Squares Value Iteration with UCB** (LSVI-UCB, Algorithm 1, p. 6), the protocol by which it interacts with an episodic MDP (pp. 4–5), and its regret (p. 5).
--
--   Let $\phi:\mathcal S\times\mathcal A\to\mathbb R^d$ be a feature map, $\lambda>0$ a regularization parameter and $(\beta_k)_{k\ge1}$ bonus parameters. Given the states $x^\tau_h$ and actions $a^\tau_h$ observed in episodes $\tau<k$, write $\phi^\tau_h=\phi(x^\tau_h,a^\tau_h)$. In episode $k$, for $h = H,\dots,1$, the algorithm computes
--   $$
--   \Lambda^k_h = \sum_{\tau=1}^{k-1}\phi^\tau_h(\phi^\tau_h)^\top + \lambda I,\qquad
--   w^k_h = (\Lambda^k_h)^{-1}\sum_{\tau=1}^{k-1}\phi^\tau_h\Big[r_h(x^\tau_h,a^\tau_h) + \max_a Q^k_{h+1}(x^\tau_{h+1},a)\Big],
--   $$
--   $$
--   Q^k_h(x,a) = \min\Big\{ (w^k_h)^\top\phi(x,a) + \beta_k\big[\phi(x,a)^\top(\Lambda^k_h)^{-1}\phi(x,a)\big]^{1/2},\ H\Big\},
--   $$
--   with $Q^k_{H+1}\equiv 0$, and sets $V^k_h(x)=\max_a Q^k_h(x,a)$. The greedy policy $\pi_k$ plays $\pi_k(x,h)=\arg\max_a Q^k_h(x,a)$.
--
--   A **run** of LSVI-UCB for $K$ episodes is a family of random states $x^k_h$ and actions $a^k_h$ on a probability space with a filtration, indexed by the flattened time $t(k,h)=(k-1)(H+1)+(h-1)$, such that
--
--   1. $x^k_h$ is measurable with respect to the information at time $t(k,h)$ (the initial state $x^k_1$ is otherwise arbitrary: an adversary may choose it from the past);
--   2. $a^k_h=\arg\max_a Q^k_h(x^k_h,a)$, computed by Algorithm 1 from the data of the earlier episodes;
--   3. given the information at time $t(k,h)$, the next state $x^k_{h+1}$ has law $\mathbb P_h(\cdot\mid x^k_h,a^k_h)$.
--
--   The **regret** after $K$ episodes is
--   $$
--   \mathrm{Regret}(K)=\sum_{k=1}^K\big[V^\star_1(x^k_1)-V^{\pi_k}_1(x^k_1)\big],
--   $$
--   where $V^{\pi_k}_1$ is the value, in the model, of the fixed greedy policy of episode $k$. Finally $\iota=\log(2dT/p)$ with $T=KH$.
--
--   **Formalization Note.** Ties in the argmax are broken by the least maximizer in a fixed linear order on the finite action set; every finite set admits one, so this is a choice of tie-break, not a restriction. $\beta$ is a sequence so that the same definition serves the constant $\beta$ of Theorem 3.1 and the episode-dependent $\beta_k$ of Theorem 3.2. $Q^k_h$, $V^k_h$ and $w^k_h$ are $0$ outside $1\le h\le H$. The transition requirement is stated as an almost-sure identity of conditional expectations of indicators; the filtration is any one for which the three conditions hold (the natural filtration of the observations is one).
-- source:
--   Jin, Yang, Wang, Jordan, arXiv:1907.05388v2, Algorithm 1, p. 6; interaction protocol §2, pp. 4–5; Regret(K), p. 5; ι and T = KH, Theorem 3.1, p. 7; Notation of App. B, p. 16

import Mathlib
import Definitions.Def_LinearMDPRL_Linear_Model

namespace LinearMDPRL.Linear

open MeasureTheory ProbabilityTheory Matrix

section Algorithm

variable {S A : Type*} {d : ℕ}

/-- The Gram matrix of Algorithm 1, line 4 (p. 6): in episode `k`, at step `h`,
`Λ^k_h = Σ_{τ=1}^{k-1} φ(x^τ_h, a^τ_h) φ(x^τ_h, a^τ_h)^⊤ + λ I`, built from the observed states
`xs τ h = x^τ_h` and actions `as τ h = a^τ_h` of the earlier episodes. -/
noncomputable def gram (φ : S → A → EuclideanSpace ℝ (Fin d)) (lam : ℝ) (xs : ℕ → ℕ → S)
    (as : ℕ → ℕ → A) (k h : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  ∑ τ ∈ Finset.Ico 1 k,
      vecMulVec (WithLp.ofLp (φ (xs τ h) (as τ h))) (WithLp.ofLp (φ (xs τ h) (as τ h)))
    + lam • (1 : Matrix (Fin d) (Fin d) ℝ)

/-- The ridge-regression weight of Algorithm 1, line 5 (p. 6), for a given next-step value
function `Vnext` (which is `x ↦ max_a Q_{h+1}(x, a)` in the algorithm):
`w = Λ_h^{-1} Σ_{τ=1}^{k-1} φ(x^τ_h, a^τ_h) [r_h(x^τ_h, a^τ_h) + Vnext(x^τ_{h+1})]`. -/
noncomputable def ridgeW (φ : S → A → EuclideanSpace ℝ (Fin d)) (r : ℕ → S → A → ℝ) (lam : ℝ)
    (xs : ℕ → ℕ → S) (as : ℕ → ℕ → A) (k h : ℕ) (Vnext : S → ℝ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 ((gram φ lam xs as k h)⁻¹ *ᵥ
    ∑ τ ∈ Finset.Ico 1 k,
      (r h (xs τ h) (as τ h) + Vnext (xs τ (h + 1))) • WithLp.ofLp (φ (xs τ h) (as τ h)))

variable [Fintype A] [Nonempty A]

/-- The backward pass of Algorithm 1 (lines 3–6, p. 6) by recursion on the number `n` of
remaining steps: `lsviQRem … k n = Q_{H+1-n}` in episode `k`, with `Q_{H+1} ≡ 0` and
`Q_h(x, a) = min{ w_h^⊤ φ(x, a) + β_k [φ(x, a)^⊤ Λ_h^{-1} φ(x, a)]^{1/2}, H }`. -/
noncomputable def lsviQRem (φ : S → A → EuclideanSpace ℝ (Fin d)) (r : ℕ → S → A → ℝ) (lam : ℝ)
    (β : ℕ → ℝ) (H : ℕ) (xs : ℕ → ℕ → S) (as : ℕ → ℕ → A) (k : ℕ) : ℕ → S → A → ℝ
  | 0 => fun _ _ => 0
  | n + 1 => fun x a =>
      min (inner ℝ (φ x a)
            (ridgeW φ r lam xs as k (H - n)
              (fun y => Finset.univ.sup' Finset.univ_nonempty
                (fun b => lsviQRem φ r lam β H xs as k n y b)))
          + β k * Real.sqrt (WithLp.ofLp (φ x a) ⬝ᵥ
              ((gram φ lam xs as k (H - n))⁻¹ *ᵥ WithLp.ofLp (φ x a))))
        (H : ℝ)

/-- The action-value estimate `Q^k_h(x, a)` of Algorithm 1 (line 6, p. 6) in episode `k` at step
`h ∈ [H]`; it is `0` outside `1 ≤ h ≤ H` (in particular `Q^k_{H+1} ≡ 0`). -/
noncomputable def lsviQ (φ : S → A → EuclideanSpace ℝ (Fin d)) (r : ℕ → S → A → ℝ) (lam : ℝ)
    (β : ℕ → ℝ) (H : ℕ) (xs : ℕ → ℕ → S) (as : ℕ → ℕ → A) (k h : ℕ) (x : S) (a : A) : ℝ :=
  if 1 ≤ h ∧ h ≤ H then lsviQRem φ r lam β H xs as k (H + 1 - h) x a else 0

/-- The value estimate `V^k_h(x) = max_a Q^k_h(x, a)` (App. B, *Notation*, p. 16). -/
noncomputable def lsviV (φ : S → A → EuclideanSpace ℝ (Fin d)) (r : ℕ → S → A → ℝ) (lam : ℝ)
    (β : ℕ → ℝ) (H : ℕ) (xs : ℕ → ℕ → S) (as : ℕ → ℕ → A) (k h : ℕ) (x : S) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun a => lsviQ φ r lam β H xs as k h x a)

/-- The weight `w^k_h` of Algorithm 1 (line 5, p. 6) in episode `k` at step `h ∈ [H]`; it is `0`
outside `1 ≤ h ≤ H`. -/
noncomputable def lsviW (φ : S → A → EuclideanSpace ℝ (Fin d)) (r : ℕ → S → A → ℝ) (lam : ℝ)
    (β : ℕ → ℝ) (H : ℕ) (xs : ℕ → ℕ → S) (as : ℕ → ℕ → A) (k h : ℕ) :
    EuclideanSpace ℝ (Fin d) :=
  if 1 ≤ h ∧ h ≤ H then ridgeW φ r lam xs as k h (lsviV φ r lam β H xs as k (h + 1)) else 0

open Classical in
/-- `argmax_{a ∈ A} q(a)` with ties broken by the least maximizer in the linear order of `A`
(Algorithm 1, line 8, p. 6). -/
noncomputable def greedy [LinearOrder A] (q : A → ℝ) : A :=
  (Finset.univ.filter (fun a => ∀ b, q b ≤ q a)).min'
    (by
      obtain ⟨a, -, ha⟩ := Finset.exists_max_image Finset.univ q Finset.univ_nonempty
      exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, fun b => ha b (Finset.mem_univ b)⟩⟩)

/-- The greedy policy `π_k` of episode `k`: `π_k(x, h) = argmax_a Q^k_h(x, a)`
(App. B, *Notation*, p. 16). -/
noncomputable def greedyPolicy [LinearOrder A] (φ : S → A → EuclideanSpace ℝ (Fin d))
    (r : ℕ → S → A → ℝ) (lam : ℝ) (β : ℕ → ℝ) (H : ℕ) (xs : ℕ → ℕ → S) (as : ℕ → ℕ → A)
    (k : ℕ) : Policy S A :=
  fun x h => greedy (lsviQ φ r lam β H xs as k h x)

end Algorithm

section Interaction

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] [Fintype A] [Nonempty A]
  [LinearOrder A] {d : ℕ}

/-- The flattened time index of step `h ∈ {1, …, H+1}` of episode `k ≥ 1`:
`t(k, h) = (k - 1)(H + 1) + (h - 1)`. -/
def tIdx (H k h : ℕ) : ℕ := (k - 1) * (H + 1) + (h - 1)

/-- A run of LSVI-UCB (Algorithm 1) with parameters `λ = lam`, `β = (β_k)_k` for `K` episodes on
the MDP `M`, on a probability space `(Ω, μ)` with filtration `𝓕` (pp. 4–6). The random state of
episode `k` at step `h` is `x k h` and the action is `a k h`.

1. `adapted`: `x^k_h` is `𝓕_{t(k,h)}`-measurable, for `k ∈ [K]`, `h ∈ [H+1]`; nothing else is
   required of the initial state `x^k_1`, which an adversary may choose from the past;
2. `actions`: `a^k_h = argmax_a Q^k_h(x^k_h, a)`, with `Q^k_h` computed by Algorithm 1 from the
   data of the episodes `τ < k`;
3. `transition`: given `𝓕_{t(k,h)}`, the next state `x^k_{h+1}` has law `P_h(· | x^k_h, a^k_h)`. -/
structure IsLSVIUCBRun {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (𝓕 : Filtration ℕ ‹MeasurableSpace Ω›) (M : EpisodicMDP S A)
    (φ : S → A → EuclideanSpace ℝ (Fin d)) (lam : ℝ) (β : ℕ → ℝ) (H K : ℕ)
    (x : ℕ → ℕ → Ω → S) (a : ℕ → ℕ → Ω → A) : Prop where
  adapted : ∀ k ∈ Finset.Icc 1 K, ∀ h ∈ Finset.Icc 1 (H + 1),
    Measurable[𝓕 (tIdx H k h)] (x k h)
  actions : ∀ ω, ∀ k ∈ Finset.Icc 1 K, ∀ h ∈ Finset.Icc 1 H,
    a k h ω = greedy (lsviQ φ M.r lam β H (fun τ i => x τ i ω) (fun τ i => a τ i ω) k h (x k h ω))
  transition : ∀ k ∈ Finset.Icc 1 K, ∀ h ∈ Finset.Icc 1 H, ∀ B : Set S, MeasurableSet B →
    μ[(x k (h + 1) ⁻¹' B).indicator (fun _ => (1 : ℝ)) | 𝓕 (tIdx H k h)]
      =ᵐ[μ] fun ω => (M.P h (x k h ω, a k h ω) B).toReal

/-- The regret of the first `K` episodes of LSVI-UCB along observed data `xs`, `as` (p. 5):
`Regret(K) = Σ_{k=1}^K [V⋆_1(x^k_1) − V^{π_k}_1(x^k_1)]`, where `π_k` is the greedy policy of
episode `k` and `V^{π_k}` is its value in the model. -/
noncomputable def regret (M : EpisodicMDP S A) (φ : S → A → EuclideanSpace ℝ (Fin d)) (lam : ℝ)
    (β : ℕ → ℝ) (H K : ℕ) (xs : ℕ → ℕ → S) (as : ℕ → ℕ → A) : ℝ :=
  ∑ k ∈ Finset.Icc 1 K,
    (Vstar M H 1 (xs k 1) - V M H (greedyPolicy φ M.r lam β H xs as k) 1 (xs k 1))

end Interaction

/-- The logarithmic factor `ι = log(2dT/p)` with `T = KH` (Theorem 3.1, p. 7). -/
noncomputable def iota (d K H : ℕ) (p : ℝ) : ℝ :=
  Real.log (2 * d * ((K : ℝ) * H) / p)

end LinearMDPRL.Linear


