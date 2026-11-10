-- Prove2me | Definitions.Def_MultAddExt_Multiplicative_Sources
-- name    : MultAddExt_Multiplicative_Sources
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T01:47:50.830564+00:00
-- url     : https://prove2.me/theorems/9c98c3be-8b74-4b86-a89f-e38693dfed94
-- title:
--   Sources sampled with nondeterministic postselection; multiplicative extractors, errorless condensers and robust errorless block condensers (Definitions 4.14, 4.15, 4.26, 4.27, 4.32)
-- statement:
--   **Postselected sources** (Definitions 4.26, 4.27). Let $\mathrm{Samp}:\{0,1\}^r\to\{0,1\}^n$ be a deterministic circuit and $\mathrm{Post}$ a nondeterministic circuit with $r$ ordinary inputs, with $\Pr_R[\mathrm{Post}(R)=1]>0$ for $R$ uniform on $\{0,1\}^r$. The source $X=(\mathrm{Samp}(R)\mid \mathrm{Post}(R)=1)$ has
--   $$\Pr[X=x]=\frac{\#\{\rho:\mathrm{Post}(\rho)=1,\ \mathrm{Samp}(\rho)=x\}}{\#\{\rho:\mathrm{Post}(\rho)=1\}}.$$
--   $X$ is in the class with size bound $s$ if **each** of $\mathrm{Samp}$ and $\mathrm{Post}$ has size at most $s$ (as Theorems 4.41–4.43 require). A joint distribution of $(Y,X)$ on $\{0,1\}^{n_1}\times\{0,1\}^{n_2}$ is in the joint class when $\mathrm{Samp}$ outputs the $n_1+n_2$ bits of $(Y,X)$.
--
--   **Multiplicative extractor** (Definition 4.14). $\mathrm{Ext}:\{0,1\}^n\to\{0,1\}^m$ is a $(k,\varepsilon)$-multiplicative extractor for a class $\mathcal C$ if for every $X\in\mathcal C$ with $H_\infty(X)\ge k$ and every $\sigma\in\{0,1\}^m$,
--   $$\Pr[\mathrm{Ext}(X)=\sigma]\le e^{\varepsilon}\cdot 2^{-m}.$$
--
--   **Errorless condenser** (Definition 4.15). $\mathrm{Cond}$ is an errorless $(k,k_{\mathrm{Cond}})$-condenser for $\mathcal C$ if $H_\infty(X)\ge k\implies H_\infty(\mathrm{Cond}(X))\ge k_{\mathrm{Cond}}$ for every $X\in\mathcal C$.
--
--   **Robust errorless block condenser** (Definition 4.32). Fix $0<\lambda\le 1$. $\mathrm{rbCond}:\{0,1\}^{n_y}\times\{0,1\}^{n_x}\to\{0,1\}^m$ is a $(\lambda,k_y,k_y^{\ge},k_x,k_{\mathrm{out}})$-robust errorless block condenser for a class of joint distributions if for every $(Y,X)$ in the class and every decomposition $(Y,X)=\lambda'(Y_{\mathrm{good}},X_{\mathrm{good}})+(1-\lambda')(Y_{\mathrm{rest}},X_{\mathrm{rest}})$ into joint distributions with $\lambda\le\lambda'\le 1$ such that $H_\infty(Y_{\mathrm{good}})\ge k_y$, $\Pr[Y_{\mathrm{good}}=y]\ge 2^{-k_y^{\ge}}$ for every $y\in\mathrm{Supp}(Y_{\mathrm{good}})$, and $H_\infty(X)\ge k_x$ (the second marginal of the whole pair), one has $H_\infty(\mathrm{rbCond}(Y_{\mathrm{good}},X_{\mathrm{good}}))\ge k_{\mathrm{out}}$.
--
--   These are the objects of the goal (Theorem 4.41) and of its two main ingredients (Theorems 4.42, 4.43).
--
--   **Formalization Note** The class predicates require $\Pr[\mathrm{Post}(R)=1]>0$, so the division above is never by zero. The parameters $k,\varepsilon,\lambda,k_y,\dots$ are reals and $e^\varepsilon$ is the natural exponential.
-- source:
--   Ball, Chattopadhyay, Gurumukhani, Shaltiel, Zhao, Multiplicative and Additive Extractors for Low Entropy Samplable Sources Under Reduced Assumptions, STOC 2027 submission (manuscript sha256 5ac077d7…), §4.3, pp. 20–24 (PDF 24–28), Definitions 4.14, 4.15, 4.26, 4.27, 4.32

import Mathlib
import Definitions.Def_MultAddExt_Multiplicative_FinDist
import Definitions.Def_MultAddExt_Multiplicative_NondetCircuit

set_option autoImplicit false

namespace MultAddExt.Multiplicative

/-! # Sources sampled with nondeterministic postselection; multiplicative extractors, errorless
condensers, robust errorless block condensers (Definitions 4.14, 4.15, 4.26, 4.27, 4.32)

Ball, Chattopadhyay, Gurumukhani, Shaltiel, Zhao, *Multiplicative and Additive Extractors for Low
Entropy Samplable Sources Under Reduced Assumptions*, STOC 2027 submission (manuscript sha256
5ac077d7…), §4.3, pp. 20–24 (PDF 24–28). -/

/-- The law of `X = (Samp(R) | Post(R) = 1)`, `R ← U_r` (Definition 4.27):
`Pr[X = x] = #{ρ : Post(ρ) = 1, Samp(ρ) = x} / #{ρ : Post(ρ) = 1}`. -/
noncomputable def postselDist {r n : ℕ} (Samp : Circ r n) (Post : NondetCirc r) :
    (Fin n → Bool) → ℝ :=
  open Classical in fun x =>
    ((Finset.univ.filter (fun ρ => Post.accepts ρ ∧ Samp.eval ρ = x)).card : ℝ) /
      ((Finset.univ.filter (fun ρ => Post.accepts ρ)).card : ℝ)

/-- `X` on `{0,1}ⁿ` is sampled by a deterministic circuit `Samp : {0,1}^r → {0,1}ⁿ` with
postselection by a nondeterministic circuit `Post` on the same `r` bits, **each** of size at most
`s`, with `Pr[Post(R) = 1] > 0` (Definitions 4.26, 4.27, with the per-circuit bound of
Theorems 4.41–4.43). -/
def IsPostselSamplable (n : ℕ) (s : ℝ) (X : (Fin n → Bool) → ℝ) : Prop :=
  ∃ (r : ℕ) (Samp : Circ r n) (Post : NondetCirc r),
    (Samp.size : ℝ) ≤ s ∧ (Post.size : ℝ) ≤ s ∧ (∃ ρ, Post.accepts ρ) ∧ X = postselDist Samp Post

/-- Split `z ∈ {0,1}^{n₁+n₂}` into its first `n₁` and its last `n₂` bits. -/
def splitBits {n₁ n₂ : ℕ} (z : Fin (n₁ + n₂) → Bool) : (Fin n₁ → Bool) × (Fin n₂ → Bool) :=
  (fun i => z (Fin.castAdd n₂ i), fun j => z (Fin.natAdd n₁ j))

/-- A joint distribution `P` of `(Y, X)` on `{0,1}^{n₁} × {0,1}^{n₂}` sampled with nondeterministic
postselection, each circuit of size at most `s`: `Samp` outputs the `n₁ + n₂` bits of `(Y, X)`. -/
def IsJointPostselSamplable (n₁ n₂ : ℕ) (s : ℝ)
    (P : (Fin n₁ → Bool) × (Fin n₂ → Bool) → ℝ) : Prop :=
  ∃ (r : ℕ) (Samp : Circ r (n₁ + n₂)) (Post : NondetCirc r),
    (Samp.size : ℝ) ≤ s ∧ (Post.size : ℝ) ≤ s ∧ (∃ ρ, Post.accepts ρ) ∧
      P = pushforward splitBits (postselDist Samp Post)

/-- **Multiplicative extractor** (Definition 4.14): `Ext` is a `(k, ε)`-multiplicative extractor
for the class `cls` if `Pr[Ext(X) = σ] ≤ e^ε · 2^{−m}` for every `X ∈ cls` with `H∞(X) ≥ k` and
every `σ ∈ {0,1}^m`. -/
def IsMultExtractor {n m : ℕ} (Ext : (Fin n → Bool) → (Fin m → Bool))
    (cls : ((Fin n → Bool) → ℝ) → Prop) (k ε : ℝ) : Prop :=
  ∀ X, cls X → k ≤ minEntropy X → ∀ σ : Fin m → Bool,
    pushforward Ext X σ ≤ Real.exp ε * (2 : ℝ) ^ (-(m : ℝ))

/-- **Errorless condenser** (Definition 4.15): for every `X ∈ cls`,
`H∞(X) ≥ k ⟹ H∞(Cond(X)) ≥ k_Cond`. -/
def IsErrorlessCondenser {n m : ℕ} (Cond : (Fin n → Bool) → (Fin m → Bool))
    (cls : ((Fin n → Bool) → ℝ) → Prop) (k kCond : ℝ) : Prop :=
  ∀ X, cls X → k ≤ minEntropy X → kCond ≤ minEntropy (pushforward Cond X)

/-- **Robust errorless block condenser** (Definition 4.32), with parameters
`(λ, k_y, k_y^≥, k_x, k_out)`: for every `(Y, X) ∈ cls` and every decomposition
`(Y, X) = λ'(Y_good, X_good) + (1 − λ')(Y_rest, X_rest)` into joint distributions with `λ' ≥ λ`,
`H∞(Y_good) ≥ k_y`, `Pr[Y_good = y] ≥ 2^{−k_y^≥}` on `Supp(Y_good)`, and `H∞(X) ≥ k_x`, one has
`H∞(rbCond(Y_good, X_good)) ≥ k_out`. -/
def IsRobustBlockCondenser {ny nx m : ℕ}
    (rbCond : (Fin ny → Bool) → (Fin nx → Bool) → (Fin m → Bool))
    (cls : ((Fin ny → Bool) × (Fin nx → Bool) → ℝ) → Prop)
    (lam ky kyGe kx kout : ℝ) : Prop :=
  ∀ P, cls P → ∀ (lam' : ℝ) (Pgood Prest : (Fin ny → Bool) × (Fin nx → Bool) → ℝ),
    lam ≤ lam' → lam' ≤ 1 → IsDist Pgood → IsDist Prest →
    (∀ z, P z = lam' * Pgood z + (1 - lam') * Prest z) →
    ky ≤ minEntropy (pushforward Prod.fst Pgood) →
    (∀ y ∈ support (pushforward Prod.fst Pgood),
      (2 : ℝ) ^ (-kyGe) ≤ pushforward Prod.fst Pgood y) →
    kx ≤ minEntropy (pushforward Prod.snd P) →
    kout ≤ minEntropy (pushforward (fun z => rbCond z.1 z.2) Pgood)

end MultAddExt.Multiplicative


