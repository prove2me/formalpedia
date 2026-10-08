-- Prove2me | Definitions.Def_ProbMFG_Nash_Model
-- name    : ProbMFG_Nash_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T19:02:50.836674+00:00
-- url     : https://prove2.me/theorems/072fcb83-0dd8-4759-930e-4c3ea8b08cdf
-- title:
--   §2.1–§3.1, pp. 2707–2713 — mean-field game data, M_p, W₂, the Hamiltonian H, its minimizer α̂, assumptions (A.1)–(A.7)
-- statement:
--   This module fixes the data of the mean-field game of Carmona and Delarue and the standing assumptions (A.1)–(A.7).
--
--   **Data.** Dimensions $d$ (state), $m$ (noise), $k$ (control), a horizon $T \ge 0$, an initial state $x_0\in\mathbb R^d$, a constant volatility matrix $\sigma\in\mathbb R^{d\times m}$, the affine drift (2.11)
--   $$b(t,x,\mu,\alpha) = b_0(t,\mu) + b_1(t)x + b_2(t)\alpha,$$
--   with $b_0(t,\mu)\in\mathbb R^d$, $b_1(t)\in\mathbb R^{d\times d}$, $b_2(t)\in\mathbb R^{d\times k}$, a running cost $f(t,x,\mu,\alpha)\in\mathbb R$ and a terminal cost $g(x,\mu)\in\mathbb R$, for $t\in[0,T]$, $x\in\mathbb R^d$, $\alpha\in\mathbb R^k$ and $\mu$ a probability measure on $\mathbb R^d$.
--
--   **Derived objects.**
--   1. The moment (2.7) $M_p(\mu) = \big(\int |x|^p\,d\mu(x)\big)^{1/p}\in[0,\infty]$; $\mathcal P_2(\mathbb R^d)$ is the set of probability measures with $M_2(\mu)<\infty$.
--   2. The 2-Wasserstein distance $W_2(\mu,\mu') = \inf\{[\int|x-y|^2\pi(dx,dy)]^{1/2} : \pi \text{ with marginals } \mu, \mu'\}$.
--   3. The gradients $\partial_x f$, $\partial_\alpha f$, $\partial_x g$.
--   4. The Hamiltonian (2.5) $H(t,x,\mu,y,\alpha) = \langle b(t,x,\mu,\alpha), y\rangle + f(t,x,\mu,\alpha)$, its minimizer $\hat\alpha(t,x,\mu,y)$ in $\alpha$ (Lemma 2.1), and $\partial_x H(t,x,\mu,y,\alpha) = b_1(t)^\dagger y + \partial_x f(t,x,\mu,\alpha)$.
--
--   **Assumptions**, with two positive constants $\lambda$, $c_L$ and "bounded subsets" meaning bounded $|x|$, $|\alpha|$ and $M_2(\mu)$:
--   - (A.1) $t\mapsto b_2(t)$ is measurable and bounded; $(t,x,\mu)\mapsto b_0(t,\mu)+b_1(t)x$ is measurable and bounded on bounded subsets of $[0,T]\times\mathbb R^d\times\mathcal P_2(\mathbb R^d)$.
--   - (A.2) For $t\in[0,T]$, $\mu\in\mathcal P_2$, $(x,\alpha)\mapsto f(t,x,\mu,\alpha)$ is $C^1$ with $c_L$-Lipschitz gradient, satisfies the convexity (2.8)
--   $$f(t,x',\mu,\alpha') - f(t,x,\mu,\alpha) - \langle (x'-x,\alpha'-\alpha), \partial_{(x,\alpha)} f(t,x,\mu,\alpha)\rangle \ge \lambda|\alpha'-\alpha|^2,$$
--   and $f$, $\partial_x f$, $\partial_\alpha f$ are locally bounded.
--   - (A.3) $b_0$ and $b_1$ are bounded on bounded subsets of their domains.
--   - (A.4) $g$ is locally bounded; for $\mu\in\mathcal P_2$, $x\mapsto g(x,\mu)$ is $C^1$, convex, with $c_L$-Lipschitz gradient.
--   - (A.5) $f(t,0,\delta_0,0)$, $\partial_x f(t,0,\delta_0,0)$, $\partial_\alpha f(t,0,\delta_0,0)$ are bounded by $c_L$;
--   $$|f(t,x',\mu',\alpha') - f(t,x,\mu,\alpha)| \le c_L\big[1 + |(x',\alpha')| + |(x,\alpha)| + M_2(\mu) + M_2(\mu')\big]\big[|(x',\alpha')-(x,\alpha)| + W_2(\mu',\mu)\big],$$
--   the same for $g$ without $t$ and $\alpha$; $b_0$, $b_1$, $b_2$ are bounded by $c_L$ and $|b_0(t,\mu')-b_0(t,\mu)|\le c_L W_2(\mu,\mu')$.
--   - (A.6) $|\partial_\alpha f(t,x,\mu,0)|\le c_L$.
--   - (A.7) $\langle x, \partial_x f(t,0,\delta_x,0)\rangle \ge -c_L(1+|x|)$ and $\langle x,\partial_x g(0,\delta_x)\rangle\ge -c_L(1+|x|)$.
--
--   These are the hypotheses of every result of §3 and §4 of the paper: under them the McKean–Vlasov FBSDE (3.1) is solvable (Theorem 3.2) and its decoupling field yields approximate Nash equilibria of the $N$-player game (Theorem 4.2).
--
--   **Formalization Note** All spaces are `EuclideanSpace ℝ (Fin n)`, so every norm is Euclidean; $|(x,\alpha)| = (|x|^2+|\alpha|^2)^{1/2}$. Matrix norms of $b_1$, $b_2$ are operator norms (the page does not name a norm). Measurability of $b_2$ is entrywise. Measures carry Mathlib's σ-algebra on `Measure`, which on probability measures on $\mathbb R^d$ is the Borel σ-field of weak convergence used by the paper. Every assumption quantifies over $\mu\in\mathcal P_2$ only; $M_2$ and $W_2$ take values in $[0,\infty]$ and are converted to reals only where they are finite. The joint display of (A.5) for $(f,g)$ is read as one inequality for $f$ and one for $g$. $\hat\alpha$ is chosen when a minimizer exists and is $0$ otherwise (Lemma 2.1 excludes the latter for $t\in[0,T]$, $\mu\in\mathcal P_2$). `Assumptions` also contains a standing convention not written on the page: $f$ and $g$ are Borel measurable on $[0,T]\times\mathbb R^d\times\mathcal P_2\times\mathbb R^k$ and $\mathbb R^d\times\mathcal P_2$, so that expected costs are expectations of measurable integrands. This module repeats, in the sub-namespace `ProbMFG.Nash`, the model of the series' first mission (drafts cannot import drafts).
-- source:
--   Carmona and Delarue, Probabilistic analysis of mean-field games, SIAM J. Control Optim. 51 (2013), pp. 2707–2713, §2.1–§2.3, §3.1, (2.5)–(2.11), (A.1)–(A.7)

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance

open MeasureTheory
open scoped NNReal ENNReal RealInnerProductSpace

namespace ProbMFG.Nash

/-- The data of the mean-field game of §2.1–§2.3 and (2.11), pp. 2707–2710: dimensions `d` (state),
`m` (noise), `k` (control), horizon `T`, initial state `x₀ ∈ ℝ^d`, constant volatility
`σ ∈ ℝ^{d×m}` (a linear map `ℝ^m → ℝ^d`), the affine drift
`b(t, x, μ, α) = b₀(t, μ) + b₁(t) x + b₂(t) α`, the running cost `f(t, x, μ, α)` and the terminal
cost `g(x, μ)`. All spaces are Euclidean (`EuclideanSpace ℝ (Fin n)`); measure arguments are
measures on `ℝ^d`. -/
structure Model (d m k : ℕ) where
  T : ℝ≥0
  x₀ : EuclideanSpace ℝ (Fin d)
  σ : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin d)
  b₀ : ℝ≥0 → Measure (EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d)
  b₁ : ℝ≥0 → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)
  b₂ : ℝ≥0 → EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin d)
  f : ℝ≥0 → EuclideanSpace ℝ (Fin d) → Measure (EuclideanSpace ℝ (Fin d)) →
    EuclideanSpace ℝ (Fin k) → ℝ
  g : EuclideanSpace ℝ (Fin d) → Measure (EuclideanSpace ℝ (Fin d)) → ℝ

/-- The moment `M_p(μ) = (∫ |x|^p dμ(x))^{1/p}` of (2.7), Euclidean norm, valued in `[0, ∞]`. -/
noncomputable def moment {d : ℕ} (p : ℝ) (μ : Measure (EuclideanSpace ℝ (Fin d))) : ℝ≥0∞ :=
  (∫⁻ x, ‖x‖ₑ ^ p ∂μ) ^ (1 / p)

/-- The 2-Wasserstein distance `W₂(μ, ν)` on `ℝ^d` (Euclidean norm), valued in `[0, ∞]`. -/
noncomputable def W2 {d : ℕ} (μ ν : Measure (EuclideanSpace ℝ (Fin d))) : ℝ≥0∞ :=
  WassersteinDRO.Duality.wassersteinDistance 2 μ ν

/-- `μ ∈ 𝒫₂(ℝ^d)`: a probability measure with finite second moment. -/
def IsP2 {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) : Prop :=
  IsProbabilityMeasure μ ∧ moment 2 μ < ⊤

/-- The Euclidean norm `|(x, α)| = (|x|² + |α|²)^{1/2}` of a pair. -/
noncomputable def pairNorm {d k : ℕ} (x : EuclideanSpace ℝ (Fin d))
    (α : EuclideanSpace ℝ (Fin k)) : ℝ :=
  Real.sqrt (‖x‖ ^ 2 + ‖α‖ ^ 2)

namespace Model

variable {d m k : ℕ} (M : Model d m k)

/-- The drift (2.11): `b(t, x, μ, α) = b₀(t, μ) + b₁(t) x + b₂(t) α`. -/
def b (t : ℝ≥0) (x : EuclideanSpace ℝ (Fin d)) (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (α : EuclideanSpace ℝ (Fin k)) : EuclideanSpace ℝ (Fin d) :=
  M.b₀ t μ + M.b₁ t x + M.b₂ t α

/-- `∂ₓf(t, x, μ, α)`, the gradient of `x ↦ f(t, x, μ, α)`. -/
noncomputable def dfx (t : ℝ≥0) (x : EuclideanSpace ℝ (Fin d))
    (μ : Measure (EuclideanSpace ℝ (Fin d))) (α : EuclideanSpace ℝ (Fin k)) :
    EuclideanSpace ℝ (Fin d) :=
  gradient (fun x' => M.f t x' μ α) x

/-- `∂_αf(t, x, μ, α)`, the gradient of `α ↦ f(t, x, μ, α)`. -/
noncomputable def dfa (t : ℝ≥0) (x : EuclideanSpace ℝ (Fin d))
    (μ : Measure (EuclideanSpace ℝ (Fin d))) (α : EuclideanSpace ℝ (Fin k)) :
    EuclideanSpace ℝ (Fin k) :=
  gradient (fun a => M.f t x μ a) α

/-- `∂ₓg(x, μ)`, the gradient of `x ↦ g(x, μ)`. -/
noncomputable def dgx (x : EuclideanSpace ℝ (Fin d)) (μ : Measure (EuclideanSpace ℝ (Fin d))) :
    EuclideanSpace ℝ (Fin d) :=
  gradient (fun x' => M.g x' μ) x

/-- The Hamiltonian (2.5): `H(t, x, μ, y, α) = ⟨b(t, x, μ, α), y⟩ + f(t, x, μ, α)`. -/
noncomputable def H (t : ℝ≥0) (x : EuclideanSpace ℝ (Fin d))
    (μ : Measure (EuclideanSpace ℝ (Fin d))) (y : EuclideanSpace ℝ (Fin d))
    (α : EuclideanSpace ℝ (Fin k)) : ℝ :=
  ⟪M.b t x μ α, y⟫ + M.f t x μ α

/-- `α̂(t, x, μ, y)`, a minimizer of `α ↦ H(t, x, μ, y, α)` over `ℝ^k` (Lemma 2.1), chosen when one
exists; the default `0` is used only when there is no minimizer, which Lemma 2.1 rules out under
(A.1)–(A.2) for `t ∈ [0, T]` and `μ ∈ 𝒫₂(ℝ^d)`. -/
noncomputable def alphaHat (t : ℝ≥0) (x : EuclideanSpace ℝ (Fin d))
    (μ : Measure (EuclideanSpace ℝ (Fin d))) (y : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin k) := by
  classical
  exact if h : ∃ a, ∀ a', M.H t x μ y a ≤ M.H t x μ y a' then h.choose else 0

/-- `∂ₓH(t, x, μ, y, α) = b₁(t)^† y + ∂ₓf(t, x, μ, α)` (p. 2715). -/
noncomputable def dxH (t : ℝ≥0) (x : EuclideanSpace ℝ (Fin d))
    (μ : Measure (EuclideanSpace ℝ (Fin d))) (y : EuclideanSpace ℝ (Fin d))
    (α : EuclideanSpace ℝ (Fin k)) : EuclideanSpace ℝ (Fin d) :=
  ContinuousLinearMap.adjoint (M.b₁ t) y + M.dfx t x μ α

/-- (A.1) in the affine form (2.11): `t ↦ b₂(t)` is measurable (entrywise) and bounded on
`[0, T]`; `(t, x, μ) ↦ b₀(t, μ) + b₁(t) x` is measurable on `[0, T] × ℝ^d × 𝒫₂(ℝ^d)` and bounded on
its bounded subsets (bounded `|x|` and `M₂(μ)`). -/
def A1 : Prop :=
  (∀ a, Measurable (fun t : {t : ℝ≥0 // t ≤ M.T} => M.b₂ t a)) ∧
  (∃ C : ℝ, ∀ t ≤ M.T, ‖M.b₂ t‖ ≤ C) ∧
  Measurable (fun q : {q : ℝ≥0 × EuclideanSpace ℝ (Fin d) × Measure (EuclideanSpace ℝ (Fin d)) //
      q.1 ≤ M.T ∧ IsP2 q.2.2} => M.b₀ q.1.1 q.1.2.2 + M.b₁ q.1.1 q.1.2.1) ∧
  ∀ R : ℝ, ∃ C : ℝ, ∀ t ≤ M.T, ∀ x μ, IsP2 μ → ‖x‖ ≤ R → moment 2 μ ≤ ENNReal.ofReal R →
    ‖M.b₀ t μ + M.b₁ t x‖ ≤ C

/-- (A.2) with constants `λ`, `c_L`: for `t ∈ [0, T]` and `μ ∈ 𝒫₂(ℝ^d)`, `(x, α) ↦ f(t, x, μ, α)` is
`C¹` with `c_L`-Lipschitz joint gradient (Euclidean norms on `ℝ^d × ℝ^k`), it satisfies the
convexity (2.8), and `f`, `∂ₓf`, `∂_αf` are bounded on bounded subsets of
`[0, T] × ℝ^d × 𝒫₂(ℝ^d) × ℝ^k`. -/
def A2 (lam cL : ℝ) : Prop :=
  (∀ t ≤ M.T, ∀ μ, IsP2 μ →
    ContDiff ℝ 1 (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin k) => M.f t p.1 μ p.2) ∧
    (∀ x x' α α', pairNorm (M.dfx t x' μ α' - M.dfx t x μ α) (M.dfa t x' μ α' - M.dfa t x μ α)
        ≤ cL * pairNorm (x' - x) (α' - α)) ∧
    (∀ x x' α α', M.f t x' μ α' - M.f t x μ α
        - (⟪x' - x, M.dfx t x μ α⟫ + ⟪α' - α, M.dfa t x μ α⟫) ≥ lam * ‖α' - α‖ ^ 2)) ∧
  ∀ R : ℝ, ∃ C : ℝ, ∀ t ≤ M.T, ∀ x μ α, IsP2 μ → ‖x‖ ≤ R → ‖α‖ ≤ R →
    moment 2 μ ≤ ENNReal.ofReal R →
    |M.f t x μ α| ≤ C ∧ ‖M.dfx t x μ α‖ ≤ C ∧ ‖M.dfa t x μ α‖ ≤ C

/-- (A.3): `b₀` is bounded on bounded subsets of `[0, T] × 𝒫₂(ℝ^d)` and `b₁` is bounded on
`[0, T]` (operator norm). -/
def A3 : Prop :=
  (∀ R : ℝ, ∃ C : ℝ, ∀ t ≤ M.T, ∀ μ, IsP2 μ → moment 2 μ ≤ ENNReal.ofReal R → ‖M.b₀ t μ‖ ≤ C) ∧
  ∃ C : ℝ, ∀ t ≤ M.T, ‖M.b₁ t‖ ≤ C

/-- (A.4): `g` is bounded on bounded subsets of `ℝ^d × 𝒫₂(ℝ^d)`; for `μ ∈ 𝒫₂(ℝ^d)`, `x ↦ g(x, μ)` is
`C¹`, convex, with `c_L`-Lipschitz gradient. -/
def A4 (cL : ℝ) : Prop :=
  (∀ R : ℝ, ∃ C : ℝ, ∀ x μ, IsP2 μ → ‖x‖ ≤ R → moment 2 μ ≤ ENNReal.ofReal R → |M.g x μ| ≤ C) ∧
  ∀ μ, IsP2 μ → ContDiff ℝ 1 (fun x => M.g x μ) ∧ ConvexOn ℝ Set.univ (fun x => M.g x μ) ∧
    ∀ x x', ‖M.dgx x' μ - M.dgx x μ‖ ≤ cL * ‖x' - x‖

/-- (A.5), read as one inequality for `f` and one for `g`: `f(t, 0, δ₀, 0)`, `∂ₓf(t, 0, δ₀, 0)`,
`∂_αf(t, 0, δ₀, 0)` are bounded by `c_L`; `f` and `g` are locally Lipschitz with the displayed
quadratic modulus (Euclidean norms, `M₂`, `W₂`); `b₀`, `b₁`, `b₂` are bounded by `c_L` and
`b₀(t, ·)` is `c_L`-Lipschitz for `W₂`. -/
def A5 (cL : ℝ) : Prop :=
  (∀ t ≤ M.T, |M.f t 0 (Measure.dirac 0) 0| ≤ cL ∧ ‖M.dfx t 0 (Measure.dirac 0) 0‖ ≤ cL ∧
      ‖M.dfa t 0 (Measure.dirac 0) 0‖ ≤ cL) ∧
  (∀ t ≤ M.T, ∀ x x' α α' μ μ', IsP2 μ → IsP2 μ' →
      |M.f t x' μ' α' - M.f t x μ α| ≤
        cL * (1 + pairNorm x' α' + pairNorm x α + (moment 2 μ).toReal + (moment 2 μ').toReal) *
          (pairNorm (x' - x) (α' - α) + (W2 μ' μ).toReal)) ∧
  (∀ x x' μ μ', IsP2 μ → IsP2 μ' →
      |M.g x' μ' - M.g x μ| ≤
        cL * (1 + ‖x'‖ + ‖x‖ + (moment 2 μ).toReal + (moment 2 μ').toReal) *
          (‖x' - x‖ + (W2 μ' μ).toReal)) ∧
  (∀ t ≤ M.T, (∀ μ, IsP2 μ → ‖M.b₀ t μ‖ ≤ cL) ∧ ‖M.b₁ t‖ ≤ cL ∧ ‖M.b₂ t‖ ≤ cL) ∧
  ∀ t ≤ M.T, ∀ μ μ', IsP2 μ → IsP2 μ' → ‖M.b₀ t μ' - M.b₀ t μ‖ ≤ cL * (W2 μ μ').toReal

/-- (A.6): `|∂_αf(t, x, μ, 0)| ≤ c_L` for `t ∈ [0, T]`, `x ∈ ℝ^d`, `μ ∈ 𝒫₂(ℝ^d)`. -/
def A6 (cL : ℝ) : Prop :=
  ∀ t ≤ M.T, ∀ x μ, IsP2 μ → ‖M.dfa t x μ 0‖ ≤ cL

/-- (A.7): `⟨x, ∂ₓf(t, 0, δ_x, 0)⟩ ≥ −c_L(1 + |x|)` and `⟨x, ∂ₓg(0, δ_x)⟩ ≥ −c_L(1 + |x|)`. -/
def A7 (cL : ℝ) : Prop :=
  ∀ t ≤ M.T, ∀ x : EuclideanSpace ℝ (Fin d),
    ⟪x, M.dfx t 0 (Measure.dirac x) 0⟫ ≥ -cL * (1 + ‖x‖) ∧
    ⟪x, M.dgx 0 (Measure.dirac x)⟫ ≥ -cL * (1 + ‖x‖)

/-- Standing measurability convention (not written on the page): the costs are Borel measurable on
`[0, T] × ℝ^d × 𝒫₂(ℝ^d) × ℝ^k` and `ℝ^d × 𝒫₂(ℝ^d)` (`𝒫(ℝ^d)` with Mathlib's σ-algebra on measures),
so that the expected costs (2.12), (4.1), (4.6) are expectations of measurable integrands. -/
def CostMeasurable : Prop :=
  Measurable (fun q : {q : ℝ≥0 × EuclideanSpace ℝ (Fin d) × Measure (EuclideanSpace ℝ (Fin d)) ×
      EuclideanSpace ℝ (Fin k) // q.1 ≤ M.T ∧ IsP2 q.2.2.1} =>
      M.f q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2) ∧
  Measurable (fun q : {q : EuclideanSpace ℝ (Fin d) × Measure (EuclideanSpace ℝ (Fin d)) //
      IsP2 q.2} => M.g q.1.1 q.1.2)

end Model

/-- Assumptions (A.1)–(A.7) with the two positive constants `λ` and `c_L`, together with the
standing measurability convention for the costs. -/
structure Assumptions {d m k : ℕ} (M : Model d m k) (lam cL : ℝ) : Prop where
  lam_pos : 0 < lam
  cL_pos : 0 < cL
  A1 : M.A1
  A2 : M.A2 lam cL
  A3 : M.A3
  A4 : M.A4 cL
  A5 : M.A5 cL
  A6 : M.A6 cL
  A7 : M.A7 cL
  meas : M.CostMeasurable

end ProbMFG.Nash


