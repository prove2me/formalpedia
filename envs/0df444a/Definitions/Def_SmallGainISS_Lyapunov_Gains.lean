-- Prove2me | Definitions.Def_SmallGainISS_Lyapunov_Gains
-- name    : SmallGainISS_Lyapunov_Gains
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:08:58.976287+00:00
-- url     : https://prove2.me/theorems/ca9ac826-97b0-4b01-b2d2-fb68bc5c89bb
-- title:
--   Comparison functions, MAFs, gain operators $\Gamma_\mu$, $\overline\Gamma_\mu$, compatibility and Ω-paths (§2, §4, Definitions 2.4, 5.1)
-- statement:
--   Write $\mathbb R_+ = [0,\infty)$ and $\mathbb R^n_+$ for the nonnegative orthant. For $v, w \in \mathbb R^n_+$, $v \ge w$ means $v_i \ge w_i$ for every $i$, and the **strict order** $v > w$ means $v_i > w_i$ for **every** $i$ (p. 5).
--
--   **Comparison functions** (p. 5). $\mathcal K$ is the class of continuous, strictly increasing $\gamma:\mathbb R_+\to\mathbb R_+$ with $\gamma(0)=0$; $\mathcal K_\infty$ is the class of unbounded $\gamma\in\mathcal K$. $\mathcal K\cup\{0\}$ and $\mathcal K_\infty\cup\{0\}$ also admit the zero function. A function $\alpha:\mathbb R_+\to\mathbb R_+$ is **positive definite** if it is continuous and $\alpha(r)=0 \iff r=0$.
--
--   **Monotone aggregation functions** (Definition 2.4, p. 7). A continuous $\mu:\mathbb R^m_+\to\mathbb R_+$ is a MAF, $\mu\in\mathrm{MAF}_m$, if
--   1. (M1) $\mu(s)>0$ whenever $s\ge 0$, $s\ne 0$;
--   2. (M2) $x<y$ (strictly in every component) implies $\mu(x)<\mu(y)$;
--   3. (M3) $\mu(x)\to\infty$ as $\|x\|\to\infty$.
--
--   **Gain matrix and gain operators** ((2.8), (2.9), p. 8). A gain matrix is $\Gamma=(\gamma_{ij})_{i,j=1}^n$ of functions $\mathbb R_+\to\mathbb R_+$; external gains $\gamma_{iu}$ form the last column of $\overline\Gamma$. For $\mu=(\mu_1,\dots,\mu_n)$ with $\mu_i\in\mathrm{MAF}_{n+1}$,
--   $$\overline\Gamma_\mu(s,r)_i=\mu_i\big(\gamma_{i1}(s_1),\dots,\gamma_{in}(s_n),\gamma_{iu}(r)\big),\qquad \Gamma_\mu(s):=\overline\Gamma_\mu(s,0).$$
--   The diagonal convention is $\gamma_{ii}\equiv 0$. **Compatibility** (Remark 2.6, (2.10)): for every $i$ whose index set $I_i=\{j:\gamma_{ij}\not\equiv0\}$ is nonempty, $\mu_i$ restricted to the coordinates in $I_i$ (all other coordinates set to $0$) satisfies (M2); and $s\mapsto\mu_i(s,0)$ satisfies (M2) on $\mathbb R^n_+$.
--
--   **Ω-paths** (p. 13, Definition 5.1). For $T:\mathbb R^n_+\to\mathbb R^n_+$, $\Omega(T)=\{s: T(s)<s\}$. A continuous $\sigma:\mathbb R_+\to\mathbb R^n_+$ with every $\sigma_i\in\mathcal K_\infty$ is an **Ω-path with respect to $T$** if, with $\sigma_i^{-1}$ the inverse of $\sigma_i$,
--   1. each $\sigma_i^{-1}$ is locally Lipschitz on $(0,\infty)$;
--   2. for every compact $K\subset(0,\infty)$ there are constants $0<c<C$ with $c\le(\sigma_i^{-1})'(r)\le C$ for all $i$ and all $r\in K$ at which $\sigma_i^{-1}$ is differentiable (5.1);
--   3. $T(\sigma(r))<\sigma(r)$ for all $r>0$ (5.2).
--
--   These objects carry both main results of the paper: Theorem 5.2 asserts that an Ω-path exists under a small-gain condition, and Theorem 5.3 uses an Ω-path, together with the small-gain condition (5.3) written with $\overline\Gamma_\mu$, to build an ISS Lyapunov function for the interconnected system.
--
--   **Formalization Note** Indices are `Fin n` (0-based). $\mathbb R_+$ is `ℝ≥0`. The strict order is the named predicate `SLt`, not Lean's Pi `<` (which is the paper's $\gneq$). The external slot of a vector in $\mathbb R^{n+1}_+$ is the last coordinate. The inverses $\sigma_i^{-1}$ are an explicit argument `τ` with $\tau_i\circ\sigma_i=\mathrm{id}=\sigma_i\circ\tau_i$; derivatives of $\tau_i$ are taken of the real function $r\mapsto\tau_i(\max(r,0))$ and are guarded by differentiability. In (2.10) the restriction $\mu_i(x|_{I_i})$ is read as $\mu_i$ evaluated at the vector that agrees with $x$ on $I_i$ and is $0$ elsewhere (external slot included). A row of $\Gamma$ with $I_i=\emptyset$ imposes no condition in (2.10), since (M2) cannot hold for a function of no coordinates. $\Gamma_\mu(s)=\overline\Gamma_\mu(s,0)$ evaluates $\gamma_{iu}(0)$, which is $0$ for $\gamma_{iu}\in\mathcal K\cup\{0\}$; that class membership is a hypothesis of the theorems, not part of these definitions. (M4) subadditivity is not part of the MAF definition (p. 7).
-- source:
--   Dashkovskiy, Rüffer, Wirth, Small Gain Theorems for Large Scale Systems and Construction of ISS Lyapunov Functions, arXiv:0901.1842v2, pp. 5, 7, 8, 13, §2.1, Definition 2.4, (2.8), (2.9), Remark 2.6 (2.10), Definition 5.1

import Mathlib

open scoped NNReal
open Filter Topology

namespace SmallGainISS.Lyapunov

/-! Dashkovskiy, Rüffer, Wirth, *Small Gain Theorems for Large Scale Systems and Construction of
ISS Lyapunov Functions*, arXiv:0901.1842v2: comparison functions (§2.1, p. 5), monotone
aggregation functions (Definition 2.4, p. 7), gain matrices and gain operators ((2.8), (2.9),
Remark 2.6, p. 8), the set `Ω` (p. 13) and Ω-paths (Definition 5.1, p. 13).

Conventions: the paper's subsystems `1, …, n` are `Fin n` (0-based); `ℝ₊` is `ℝ≥0` and `ℝⁿ₊`
is `Fin n → ℝ≥0`; the external-input slot of a vector MAF in `MAF_{n+1}` is the last
coordinate `Fin.last n`. -/

variable {n : ℕ}

/-- The paper's strict order on `ℝⁿ₊` (p. 5): `v < w` iff `vᵢ < wᵢ` for **every** `i`.
(This is not Lean's Pi `<`, which is the paper's `≩`.) -/
def SLt {m : ℕ} (v w : Fin m → ℝ≥0) : Prop := ∀ i, v i < w i

/-- Class `𝒦` (p. 5): continuous, strictly increasing, `γ(0) = 0`. -/
def IsK (γ : ℝ≥0 → ℝ≥0) : Prop := Continuous γ ∧ StrictMono γ ∧ γ 0 = 0

/-- Class `𝒦∞` (p. 5): class `𝒦` and unbounded. -/
def IsKInf (γ : ℝ≥0 → ℝ≥0) : Prop := IsK γ ∧ ¬ BddAbove (Set.range γ)

/-- `γ ∈ 𝒦 ∪ {0}`. -/
def IsKOrZero (γ : ℝ≥0 → ℝ≥0) : Prop := IsK γ ∨ γ = 0

/-- `γ ∈ 𝒦∞ ∪ {0}`. -/
def IsKInfOrZero (γ : ℝ≥0 → ℝ≥0) : Prop := IsKInf γ ∨ γ = 0

/-- A positive definite function `α : ℝ₊ → ℝ₊` (p. 5): continuous, and `α(r) = 0 ⟺ r = 0`. -/
def IsPosDef (α : ℝ≥0 → ℝ≥0) : Prop := Continuous α ∧ ∀ r, α r = 0 ↔ r = 0

/-- `g` is a two-sided inverse of `γ` on `ℝ₊`: `g ∘ γ = id` and `γ ∘ g = id`. Used for
`σᵢ⁻¹` and `φ⁻¹`, which the paper writes for `𝒦∞` functions (bijections of `ℝ₊`). -/
def IsInverse (g γ : ℝ≥0 → ℝ≥0) : Prop :=
  Function.LeftInverse g γ ∧ Function.RightInverse g γ

/-- Monotone aggregation function, Definition 2.4 (p. 7): `μ : ℝᵐ₊ → ℝ₊` continuous with
(M1) `μ(s) > 0` if `s ≩ 0` (`μ(s) ≥ 0` is automatic on `ℝ≥0`);
(M2) `x < y` (strict in every component) implies `μ(x) < μ(y)`;
(M3) `‖x‖ → ∞` implies `μ(x) → ∞`.
(M4) subadditivity is not part of the definition (p. 7). -/
def IsMAF {m : ℕ} (μ : (Fin m → ℝ≥0) → ℝ≥0) : Prop :=
  Continuous μ ∧
  (∀ s : Fin m → ℝ≥0, s ≠ 0 → 0 < μ s) ∧
  (∀ x y : Fin m → ℝ≥0, SLt x y → μ x < μ y) ∧
  Tendsto μ (Bornology.cobounded (Fin m → ℝ≥0)) atTop

/-- A gain matrix `Γ = (γᵢⱼ)` (2.8): `Γ i j` is the gain `γᵢⱼ : ℝ₊ → ℝ₊`. The external gains
`γᵢᵤ` (the last column of `Γ̄`) are carried separately as `γu : Fin n → ℝ≥0 → ℝ≥0`. -/
abbrev GainMatrix (n : ℕ) := Fin n → Fin n → ℝ≥0 → ℝ≥0

/-- The vector `(s₁, …, sₙ, r) ∈ ℝⁿ⁺¹₊`. -/
def appendLast (s : Fin n → ℝ≥0) (r : ℝ≥0) : Fin (n + 1) → ℝ≥0 :=
  Fin.snoc (α := fun _ => ℝ≥0) s r

/-- The gain operator `Γ̄_μ : ℝⁿ⁺¹₊ → ℝⁿ₊` of (2.9), p. 8:
`Γ̄_μ(s, r)ᵢ = μᵢ(γᵢ₁(s₁), …, γᵢₙ(sₙ), γᵢᵤ(r))`. -/
def gainOpBar (Γ : GainMatrix n) (γu : Fin n → ℝ≥0 → ℝ≥0)
    (μ : Fin n → (Fin (n + 1) → ℝ≥0) → ℝ≥0) (s : Fin n → ℝ≥0) (r : ℝ≥0) : Fin n → ℝ≥0 :=
  fun i => μ i (appendLast (fun j => Γ i j (s j)) (γu i r))

/-- The gain operator `Γ_μ(s) := Γ̄_μ(s, 0)` (p. 8). -/
def gainOp (Γ : GainMatrix n) (γu : Fin n → ℝ≥0 → ℝ≥0)
    (μ : Fin n → (Fin (n + 1) → ℝ≥0) → ℝ≥0) (s : Fin n → ℝ≥0) : Fin n → ℝ≥0 :=
  gainOpBar Γ γu μ s 0

/-- The convention `γᵢᵢ ≡ 0` (p. 8). -/
def ZeroDiagonal (Γ : GainMatrix n) : Prop := ∀ i, Γ i i = 0

/-- Remark 2.6 (general assumption, p. 8), for `μ ∈ MAFⁿ_{n+1}`.
(a) (2.10): for each `i` whose row `Iᵢ = {j : γᵢⱼ ≢ 0}` is nonempty, the restriction of `μᵢ`
to the coordinates in `Iᵢ` (all other coordinates, including the external slot, set to `0`)
satisfies (M2): if `xⱼ < yⱼ` for all `j ∈ Iᵢ` then `μᵢ(x|Iᵢ) < μᵢ(y|Iᵢ)`. A row with
`Iᵢ = ∅` imposes nothing (a restriction to no coordinates is constant, so (M2) cannot hold).
(b) "In particular" `s ↦ μᵢ(s₁, …, sₙ, 0)` satisfies (M2) on `ℝⁿ₊`. -/
def Compatible (Γ : GainMatrix n) (μ : Fin n → (Fin (n + 1) → ℝ≥0) → ℝ≥0) : Prop :=
  (∀ i, (∃ j, Γ i j ≠ 0) → ∀ x y : Fin n → ℝ≥0,
    (∀ j, Γ i j = 0 → x j = 0) → (∀ j, Γ i j = 0 → y j = 0) →
    (∀ j, Γ i j ≠ 0 → x j < y j) → μ i (appendLast x 0) < μ i (appendLast y 0)) ∧
  (∀ i, ∀ x y : Fin n → ℝ≥0, SLt x y → μ i (appendLast x 0) < μ i (appendLast y 0))

/-- `Ω(T) = {s ∈ ℝⁿ₊ : T(s) < s}` (p. 13), strict in every component. -/
def Omega (T : (Fin n → ℝ≥0) → (Fin n → ℝ≥0)) : Set (Fin n → ℝ≥0) := {s | SLt (T s) s}

/-- A function `ℝ₊ → ℝ₊` read as a real function of a real variable, `r ↦ f(max r 0)`, so that
at a point `r > 0` its derivative is the ordinary derivative of `f` there. -/
noncomputable def liftR (f : ℝ≥0 → ℝ≥0) : ℝ → ℝ := fun r => (f r.toNNReal : ℝ)

/-- Definition 5.1 (p. 13). A continuous path `σ : ℝ₊ → ℝⁿ₊` with every component `σᵢ ∈ 𝒦∞` is
an Ω-path with respect to `T`, with `τᵢ = σᵢ⁻¹` the inverse of `σᵢ` on `ℝ₊`, if
(i) each `τᵢ` is locally Lipschitz continuous on `(0, ∞)`;
(ii) for every compact `K ⊂ (0, ∞)` there are constants `0 < c < C` such that for all `i` and all
`r ∈ K` at which `τᵢ` is differentiable, `c ≤ τᵢ'(r) ≤ C` (5.1) — `c, C` depend on `K` only;
(iii) `σ(r) ∈ Ω(T)` for all `r > 0`, i.e. `T(σ(r)) < σ(r)` (5.2), strict in every component.
The inverses `τ` are an explicit argument; since each `σᵢ` is a bijection of `ℝ₊`, `τ` is
determined by `σ`. -/
def IsOmegaPath (T : (Fin n → ℝ≥0) → (Fin n → ℝ≥0)) (σ : ℝ≥0 → Fin n → ℝ≥0)
    (τ : Fin n → ℝ≥0 → ℝ≥0) : Prop :=
  Continuous σ ∧ (∀ i, IsKInf (fun r => σ r i)) ∧
  (∀ i, IsInverse (τ i) (fun r => σ r i)) ∧
  (∀ i, LocallyLipschitzOn (Set.Ioi (0 : ℝ≥0)) (τ i)) ∧
  (∀ K : Set ℝ, IsCompact K → K ⊆ Set.Ioi 0 →
    ∃ c C : ℝ, 0 < c ∧ c < C ∧ ∀ i, ∀ r ∈ K, DifferentiableAt ℝ (liftR (τ i)) r →
      c ≤ deriv (liftR (τ i)) r ∧ deriv (liftR (τ i)) r ≤ C) ∧
  ∀ r : ℝ≥0, 0 < r → σ r ∈ Omega T

end SmallGainISS.Lyapunov


