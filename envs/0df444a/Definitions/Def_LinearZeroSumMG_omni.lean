-- Prove2me | Definitions.Def_LinearZeroSumMG_omni
-- name    : LinearZeroSumMG_omni
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:52:50.630572+00:00
-- url     : https://prove2.me/theorems/80f19915-0dc1-4311-95cd-3b3ea84cb3dc
-- title:
--   Algorithm 1 (Optimistic Minimax Value Iteration, offline)
-- statement:
--   **Algorithm 1** (input $\beta>0$, a CCE rule and a rounding rule). In episode $k$, using the data $(x^\tau_h,a^\tau_h,b^\tau_h)$ of the episodes $\tau<k$ and $\phi^\tau_h=\phi(x^\tau_h,a^\tau_h,b^\tau_h)$, set $\overline V^k_{H+1}=\underline V^k_{H+1}\equiv0$ and for $h=H,\dots,1$:
--   1. $\Lambda^k_h=\sum_{\tau=1}^{k-1}\phi^\tau_h(\phi^\tau_h)^\top+I$;
--   2. $\overline w^k_h=(\Lambda^k_h)^{-1}\sum_{\tau=1}^{k-1}\phi^\tau_h\big[r_h(x^\tau_h,a^\tau_h,b^\tau_h)+\overline V^k_{h+1}(x^\tau_{h+1})\big]$, and $\underline w^k_h$ likewise with $\underline V^k_{h+1}$;
--   3. $\overline Q^k_h=\Pi_H\{(\overline w^k_h)^\top\phi+\beta\|\phi\|_{(\Lambda^k_h)^{-1}}\}$ and $\underline Q^k_h=\Pi_H\{(\underline w^k_h)^\top\phi-\beta\|\phi\|_{(\Lambda^k_h)^{-1}}\}$;
--   4. $\sigma^k_h(x)=\texttt{FIND\_CCE}(\overline Q^k_h,\underline Q^k_h,x)$ for each $x$;
--   5. $\overline V^k_h(x)=\mathbb E_{(a,b)\sim\sigma^k_h(x)}\overline Q^k_h(x,a,b)$ and $\underline V^k_h(x)=\mathbb E_{(a,b)\sim\sigma^k_h(x)}\underline Q^k_h(x,a,b)$.
--
--   Then, for $h=1,\dots,H$, the players sample $(a^k_h,b^k_h)\sim\sigma^k_h(x^k_h)$ and observe $x^k_{h+1}$ (see the run). The **marginal policies** whose duality gap is measured are $\pi^k_h(x)=\mathcal P_1\sigma^k_h(x)$ and $\nu^k_h(x)=\mathcal P_2\sigma^k_h(x)$.
--
--   The upper and lower estimates are optimistic and pessimistic bounds on the best-response values (Lemma 5); the CCE couples the two players' choices so that both bounds remain valid.
--
--   **Formalization Note** Line 6 uses the current episode's $\overline V^k_{h+1}$ at the past next-states. FIND_CCE receives the parameters of $\overline Q^k_h$, $\underline Q^k_h$, and one rounded pair serves all states. The record also exposes $(\Lambda^k_h)^{-1}$, the weights, the estimates, the picked pair and $\sigma^k_h$; $\overline V^k_h,\underline V^k_h$ are set to $0$ outside $h\in[1,H]$.
-- source:
--   Xie, Chen, Wang & Yang, Learning Zero-Sum Simultaneous-Move Markov Games Using Function Approximation and Correlated Equilibrium, arXiv:2002.07066v3, Algorithm 1, p.10; §3.3, p.12

import Mathlib
import Definitions.Def_LinearZeroSumMG_MarkovGame
import Definitions.Def_LinearZeroSumMG_findCCE
import Definitions.Def_LinearZeroSumMG_IsApproxCCE

namespace LinearZeroSumMG

open Matrix

/-- The inputs of Algorithm 1 besides the data: the feature map `φ`, the bonus parameter `β`, the
CCE rule `cce` of line 3 of Algorithm 2, and the rounding rule `round` of its line 2. -/
structure OmniParams (S A : Type*) (d : ℕ) where
  /-- The known feature map `φ : 𝒮 × 𝒜 × 𝒜 → ℝ^d`. -/
  φ : S → A → A → Fin d → ℝ
  /-- The bonus parameter `β > 0`. -/
  β : ℝ
  /-- The CCE rule: payoff matrices for P1 and P2 ↦ a joint distribution on `A × A`. -/
  cce : (A → A → ℝ) → (A → A → ℝ) → (A × A → ℝ)
  /-- The rounding rule of `FIND_CCE`. -/
  round : RoundRule S A d

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] [Fintype A] {d : ℕ}

/-- The feature vector `φ^τ_h = φ(x^τ_h, a^τ_h, b^τ_h)` of step `h` of episode `τ`, from the observed
states `xs τ h = x^τ_h` and actions `as τ h = a^τ_h` (P1), `bs τ h = b^τ_h` (P2). -/
def feat (φ : S → A → A → Fin d → ℝ) (xs : ℕ → ℕ → S) (as bs : ℕ → ℕ → A) (τ h : ℕ) :
    Fin d → ℝ :=
  φ (xs τ h) (as τ h) (bs τ h)

/-- Line 5 of Algorithm 1: `Λ^k_h = ∑_{τ=1}^{k−1} φ^τ_h (φ^τ_h)ᵀ + I`. -/
noncomputable def gram (φ : S → A → A → Fin d → ℝ) (xs : ℕ → ℕ → S) (as bs : ℕ → ℕ → A)
    (k h : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  ∑ τ ∈ Finset.Ico 1 k, vecMulVec (feat φ xs as bs τ h) (feat φ xs as bs τ h) + 1

/-- Lines 6–7 of Algorithm 1, for a given next-step value estimate `Vnext`:
`(Λ^k_h)⁻¹ ∑_{τ=1}^{k−1} φ^τ_h [r_h(x^τ_h, a^τ_h, b^τ_h) + Vnext(x^τ_{h+1})]`. -/
noncomputable def ridge (G : MarkovGame S A) (φ : S → A → A → Fin d → ℝ) (xs : ℕ → ℕ → S)
    (as bs : ℕ → ℕ → A) (k h : ℕ) (Vnext : S → ℝ) : Fin d → ℝ :=
  (gram φ xs as bs k h)⁻¹ *ᵥ ∑ τ ∈ Finset.Ico 1 k,
    (G.r h (xs τ h) (as τ h) (bs τ h) + Vnext (xs τ (h + 1))) • feat φ xs as bs τ h

/-- The quantities computed at one step `h` of the backward pass of Algorithm 1 in episode `k`. -/
structure OmniStep (S A : Type*) (d : ℕ) where
  /-- `(Λ^k_h)⁻¹` -/
  gramInv : Matrix (Fin d) (Fin d) ℝ
  /-- `w̄^k_h` (line 6) -/
  wUp : Fin d → ℝ
  /-- `w̲^k_h` (line 7) -/
  wLo : Fin d → ℝ
  /-- `Q̄^k_h` (line 8) -/
  QUp : S → A → A → ℝ
  /-- `Q̲^k_h` (line 9) -/
  QLo : S → A → A → ℝ
  /-- the pair `(Q̃, Q̰)` picked by `FIND_CCE` (Algorithm 2, line 2) -/
  pick : (S → A → A → ℝ) × (S → A → A → ℝ)
  /-- `σ^k_h(x)` (line 10) -/
  sigma : S → A × A → ℝ
  /-- `V̄^k_h` (line 11) -/
  VUp : S → ℝ
  /-- `V̲^k_h` (line 12) -/
  VLo : S → ℝ

/-- Lines 5–12 of Algorithm 1 at step `h` of episode `k`, given the next-step estimates
`next = (V̄^k_{h+1}, V̲^k_{h+1})`. -/
noncomputable def omniStep (G : MarkovGame S A) (P : OmniParams S A d) (xs : ℕ → ℕ → S)
    (as bs : ℕ → ℕ → A) (k h : ℕ) (next : (S → ℝ) × (S → ℝ)) : OmniStep S A d :=
  let Mi : Matrix (Fin d) (Fin d) ℝ := (gram P.φ xs as bs k h)⁻¹
  let wU := ridge G P.φ xs as bs k h next.1
  let wL := ridge G P.φ xs as bs k h next.2
  let QU := qFun P.φ G.H P.β 1 wU (fun i j => Mi i j)
  let QL := qFun P.φ G.H P.β (-1) wL (fun i j => Mi i j)
  let σ : S → A × A → ℝ :=
    fun x => findCCE P.cce P.round k h (wU, fun i j => Mi i j) (wL, fun i j => Mi i j) x
  { gramInv := Mi, wUp := wU, wLo := wL, QUp := QU, QLo := QL,
    pick := P.round k h (wU, fun i j => Mi i j) (wL, fun i j => Mi i j),
    sigma := σ,
    VUp := fun x => ∑ ab : A × A, σ x ab * QU x ab.1 ab.2,
    VLo := fun x => ∑ ab : A × A, σ x ab * QL x ab.1 ab.2 }

/-- The backward pass (lines 4–13) by recursion on the number `n` of remaining steps:
`omniPass … k n = (V̄^k_{H+1−n}, V̲^k_{H+1−n})`, with `V̄^k_{H+1} = V̲^k_{H+1} ≡ 0`. -/
noncomputable def omniPass (G : MarkovGame S A) (P : OmniParams S A d) (xs : ℕ → ℕ → S)
    (as bs : ℕ → ℕ → A) (k : ℕ) : ℕ → (S → ℝ) × (S → ℝ)
  | 0 => (fun _ => 0, fun _ => 0)
  | n + 1 =>
      let s := omniStep G P xs as bs k (G.H - n) (omniPass G P xs as bs k n)
      (s.VUp, s.VLo)

/-- **Algorithm 1 (Optimistic Minimax Value Iteration, simultaneous move, offline).**
Xie, Chen, Wang & Yang, *Learning Zero-Sum Simultaneous-Move Markov Games Using Function
Approximation and Correlated Equilibrium*, arXiv:2002.07066v3, Algorithm 1, p.10:
"1: Input: bonus parameter `β > 0`. 2: for episode `k = 1, 2, …, K` do 3: Receive initial state
`x^k_1` 4: for step `h = H, H − 1, …, 2, 1` do
5: `Λ^k_h ← ∑_{τ=1}^{k−1} φ(x^τ_h, a^τ_h, b^τ_h)φ(x^τ_h, a^τ_h, b^τ_h)ᵀ + I`.
6: `w̄^k_h ← (Λ^k_h)⁻¹ ∑_{τ=1}^{k−1} φ(x^τ_h, a^τ_h, b^τ_h)[r_h(x^τ_h, a^τ_h, b^τ_h) + V̄^k_{h+1}(x^τ_{h+1})]`.
7: `w̲^k_h ← (Λ^k_h)⁻¹ ∑_{τ=1}^{k−1} φ(x^τ_h, a^τ_h, b^τ_h)[r_h(x^τ_h, a^τ_h, b^τ_h) + V̲^k_{h+1}(x^τ_{h+1})]`.
8: `Q̄^k_h(·, ·, ·) ← Π_H{(w̄^k_h)ᵀφ(·, ·, ·) + β√(φ(·, ·, ·)ᵀ(Λ^k_h)⁻¹φ(·, ·, ·))}`.
9: `Q̲^k_h(·, ·, ·) ← Π_H{(w̲^k_h)ᵀφ(·, ·, ·) − β√(φ(·, ·, ·)ᵀ(Λ^k_h)⁻¹φ(·, ·, ·))}`.
10: For each `x`, let `σ^k_h(x) ← FIND_CCE(Q̄^k_h, Q̲^k_h, x)`.
11: `V̄^k_h(x) ← 𝔼_{(a,b)∼σ^k_h(x)} Q̄^k_h(x, a, b)` for each `x`.
12: `V̲^k_h(x) ← 𝔼_{(a,b)∼σ^k_h(x)} Q̲^k_h(x, a, b)` for each `x`. 13: end for
14: for step `h = 1, 2, …, H` do 15: Sample `(a^k_h, b^k_h) ∼ σ^k_h(x^k_h)`. 16: P1 takes action `a^k_h`;
P2 takes action `b^k_h`. 17: Observe next state `x^k_{h+1}`. 18: end for 19: end for"

`omni G P xs as bs k h` is the record of lines 5–12 at step `h ∈ [1, H]` of episode `k`, computed
from the observed data `xs`, `as`, `bs` of the episodes `τ ∈ [1, k − 1]` (only those entries are read).

**Formalization Note**
- Steps `h ∈ [1, H]` and episodes `k ≥ 1` are 1-based; `V̄^k_{H+1} = V̲^k_{H+1} ≡ 0`.
- Line 6 uses the current episode's `V̄^k_{h+1}`, evaluated at the past next-states `x^τ_{h+1}`.
- The rewards `r_h(x^τ_h, a^τ_h, b^τ_h)` of past steps are observed; they are read from the game.
- Line 10 calls `FIND_CCE` with the parameters `(w̄^k_h, (Λ^k_h)⁻¹)` and `(w̲^k_h, (Λ^k_h)⁻¹)` of
  `Q̄^k_h` and `Q̲^k_h`, so one rounded pair serves all states `x`.
- Lines 14–18 (sampling and observing) are the run of the algorithm, `IsOmniRun`.
- Matrix inversion is Mathlib's `Matrix.inv`; `Λ^k_h` is positive definite, hence invertible. -/
noncomputable def omni (G : MarkovGame S A) (P : OmniParams S A d) (xs : ℕ → ℕ → S)
    (as bs : ℕ → ℕ → A) (k h : ℕ) : OmniStep S A d :=
  omniStep G P xs as bs k h (omniPass G P xs as bs k (G.H - h))

/-- The upper value estimate `V̄^k_h` of Algorithm 1 (line 11), with `V̄^k_h ≡ 0` for `h ∉ [1, H]`
(in particular `V̄^k_{H+1} ≡ 0`). -/
noncomputable def VUp (G : MarkovGame S A) (P : OmniParams S A d) (xs : ℕ → ℕ → S)
    (as bs : ℕ → ℕ → A) (k h : ℕ) : S → ℝ :=
  if 1 ≤ h ∧ h ≤ G.H then (omni G P xs as bs k h).VUp else fun _ => 0

/-- The lower value estimate `V̲^k_h` of Algorithm 1 (line 12), with `V̲^k_h ≡ 0` for `h ∉ [1, H]`. -/
noncomputable def VLo (G : MarkovGame S A) (P : OmniParams S A d) (xs : ℕ → ℕ → S)
    (as bs : ℕ → ℕ → A) (k h : ℕ) : S → ℝ :=
  if 1 ≤ h ∧ h ≤ G.H then (omni G P xs as bs k h).VLo else fun _ => 0

/-- The marginal policy of P1 in episode `k`: `π^k_h(x) := 𝒫₁σ^k_h(x)` (arXiv:2002.07066v3, §3.3,
p.12: "we marginalize `σ^k_h` into a pair of independent policies `π^k_h(x) := 𝒫₁σ^k_h(x)` and
`ν^k_h(x) := 𝒫₂σ^k_h(x)` for each player"). -/
noncomputable def piK (G : MarkovGame S A) (P : OmniParams S A d) (xs : ℕ → ℕ → S)
    (as bs : ℕ → ℕ → A) (k : ℕ) : ℕ → S → A → ℝ :=
  fun h x => marg1 ((omni G P xs as bs k h).sigma x)

/-- The marginal policy of P2 in episode `k`: `ν^k_h(x) := 𝒫₂σ^k_h(x)` (arXiv:2002.07066v3, §3.3,
p.12). -/
noncomputable def nuK (G : MarkovGame S A) (P : OmniParams S A d) (xs : ℕ → ℕ → S)
    (as bs : ℕ → ℕ → A) (k : ℕ) : ℕ → S → A → ℝ :=
  fun h x => marg2 ((omni G P xs as bs k h).sigma x)

end LinearZeroSumMG


