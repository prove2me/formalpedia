-- Prove2me | Definitions.Def_BanKeskin_UnknownSparsity_Model
-- name    : BanKeskin_UnknownSparsity_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T16:55:07.026219+00:00
-- url     : https://prove2.me/theorems/5d20e7f3-d7ed-4d3c-915b-4557389b93a0
-- title:
--   pp. 5552–5557 — the personalized pricing model (1) with link g, sparsity s, schedule (7) and the lasso quasi-likelihood objective (17)
-- statement:
--   **Setting** (Ban and Keskin 2021, §2.1). A seller sells to customers arriving in periods $t = 1, 2, \dots$. Before pricing, the seller sees the customer's raw feature vector $z_t \in \mathbb R^d$ ($d \ge 1$) and forms the augmented vector $x_t = [1; z_t] \in \mathbb R^{d+1}$. The seller then charges a price $p_t \in [\ell, u]$, $0 < \ell < u$, and observes the demand
--
--   $$D_t = g\big(\alpha\cdot x_t + (\beta\cdot x_t)\,p_t\big) + \varepsilon_t, \qquad (1)$$
--
--   with unknown $\theta = (\alpha,\beta) \in \Theta \subset \mathbb R^{2(d+1)}$. Writing $u(p,x) = [1;p]\otimes x \in \mathbb R^{2(d+1)}$, the argument of $g$ is $\theta\cdot u(p,x)$.
--
--   This definition fixes the static data of the model:
--
--   1. the price bounds $0 < \ell < u$ and the parameter set $\Theta = [\mathrm{lo}, \mathrm{hi}]$, a compact rectangle in $\mathbb R^{2(d+1)}$; the projection $\mathcal P_\Theta$ onto $\Theta$, which for a rectangle is coordinatewise clamping;
--   2. the feature support $\mathcal Z \subset \mathbb R^d$, compact and contained in the Euclidean ball of radius $z_{\max} > 0$; $\mathcal X = \{1\}\times\mathcal Z$;
--   3. two distinct experimental prices $m_1 \ne m_2$ in $[\ell, u]$;
--   4. the link $g:\mathbb R\to\mathbb R$, differentiable and increasing, and constants $0 < \tilde\ell \le \tilde u$ with $\tilde\ell \le g'(\xi) \le \tilde u$ for every $\xi = \theta\cdot u(p,x)$ with $\theta\in\Theta$, $x\in\mathcal X$, $p\in[\ell,u]$ (endnote 2);
--   5. the revenue $r(p,\theta,x) = p\,g(\theta\cdot u(p,x))$ (2), and a clairvoyant price $\varphi(\theta,x)$ that maximizes $r(\cdot,\theta,x)$ over all of $\mathbb R$ and lies in the open interval $(\ell,u)$ for every $\theta\in\Theta$, $x\in\mathcal X$; the map $(v,z)\mapsto\varphi(\mathcal P_\Theta v,[1;z])$ is measurable, so the induced pricing policy is admissible; $r^*(\theta,x) = r(\varphi(\theta,x),\theta,x)$;
--   6. the sparsity $s(\theta) = |\mathcal S|$, $\mathcal S = \{i : \alpha_i \ne 0\}\cup\{i : \beta_i\ne 0\}$;
--   7. the experimentation schedule (7): $M_1 = \{L^2 : L \ge 1\}$, $M_2 = \{L^2+1 : L\ge 1\}$, $\chi_t = \mathbb I\{t \in M_1\cup M_2\}$;
--   8. the regularization schedule $\lambda_{n+1} = \tilde c\, n^{1/4}\sqrt{\log d + \log n}$;
--   9. the lasso-regularized quasi-likelihood objective of a history $(x_k,p_k,D_k)_{k=1}^n$, $u_k = u(p_k,x_k)$:
--
--   $$\bar Q_n(\tilde\theta,\tilde\lambda) = \sum_{k=1}^n \chi_k\Big(D_k\,(\tilde\theta\cdot u_k) - \int_0^{\tilde\theta\cdot u_k} g(b)\,db\Big) - \tilde\lambda\,\|\tilde\theta\|_1 .$$
--
--   The substitution $y = g(b)$ in the paper's (17), $\int_{D_k}^{g(\tilde\theta\cdot u_k)}\frac{D_k-y}{\nu(y)}\,dy$ with $\nu(y) = g'(g^{-1}(y))$, gives $D_k(\tilde\theta\cdot u_k) - \int_0^{\tilde\theta\cdot u_k} g$ minus a quantity that does not depend on $\tilde\theta$; so $\bar Q_n$ and (17) have the same maximizers in $\tilde\theta$.
--
--   These objects are shared by Lemma 3 and Theorem 3 of the paper.
--
--   **Formalization Note.** Coordinates: the paper's index $1$ (the intercept) is Lean index `0`, its index $i+1$ is Lean `i.succ`; $\theta(0,i) = \alpha_i$, $\theta(1,i) = \beta_i$. Periods are 1-based, and history entry `k : Fin n` is period $k+1$. The derivative bounds of endnote 2 are a hypothesis: the paper's claim that they follow from "differentiable and increasing" is false ($g(\xi)=\xi^3$). The integrated objective avoids requiring a global inverse of $g$. The objective is the integrated form above, which needs neither $g^{-1}$ nor $\nu$ and is finite for every $\tilde\theta$. $\varphi$ is a field constrained by its maximizing property, not a formula. The support $\mathcal Z$ is any compact set containing every realized feature vector; the paper's phrase "positive measure in the interior of their domains and zero on the boundary" is not formalized. $d \ge 1$ is assumed.
-- source:
--   Ban and Keskin, Personalized Dynamic Pricing with Machine Learning, Management Science 67(9) (2021), pp. 5552–5553, (1)–(2) and §2.1; p. 5555, (7); p. 5557, (17); p. 5558, Lemma 3 and Theorem 3 (λ_{t+1}); p. 5568, endnotes 1–2

import Mathlib
import Definitions.Def_BanKeskin_KnownSparsity_Model

namespace BanKeskin.UnknownSparsity

open Real

/-- Augmented feature vectors `x = [1; z] ∈ ℝ^{d+1}`. The paper's index `1` (the intercept) is
Lean index `0`, and the paper's index `i + 1` is Lean index `i.succ`. -/
abbrev Feat (d : ℕ) := Fin (d + 1) → ℝ

/-- Parameter vectors `θ = (α, β) ∈ ℝ^{2(d+1)}`, with `θ (0, i) = α_i` and `θ (1, i) = β_i`. -/
abbrev Param (d : ℕ) := Fin 2 × Fin (d + 1) → ℝ

/-- The augmented feature vector `[1; z] ∈ ℝ^{d+1}` of a raw feature vector `z ∈ ℝ^d`. -/
def featX {d : ℕ} (z : Fin d → ℝ) : Feat d := Fin.cons 1 z

/-- The regressor `u(p, x) = [1; p] ⊗ x ∈ ℝ^{2(d+1)}`, so that
`θ ⬝ᵥ regr p x = α · x + (β · x) p`. -/
def regr {d : ℕ} (p : ℝ) (x : Feat d) : Param d :=
  fun ji => (if ji.1 = 0 then 1 else p) * x ji.2

/-- Expected single-period revenue (2): `r(p, θ, x) = p · g(α · x + (β · x) p)`. -/
def revenue {d : ℕ} (g : ℝ → ℝ) (p : ℝ) (θ : Param d) (x : Feat d) : ℝ :=
  p * g (θ ⬝ᵥ regr p x)

/-- The projection of `ℝ^{2(d+1)}` onto the rectangle `Θ = [lo, hi]`; for a rectangle the
Euclidean projection is coordinatewise clamping. -/
def clamp {d : ℕ} (lo hi : Param d) (v : Param d) : Param d :=
  fun j => max (lo j) (min (v j) (hi j))

/-- The sparsity `s = |𝒮|`, where `𝒮 = 𝒮_α ∪ 𝒮_β = {i : α_i ≠ 0} ∪ {i : β_i ≠ 0}`. -/
noncomputable def supportCard {d : ℕ} (θ : Param d) : ℕ :=
  (Finset.univ.filter fun i : Fin (d + 1) => θ (0, i) ≠ 0 ∨ θ (1, i) ≠ 0).card

/-- The squared Euclidean norm `‖v‖² = Σ_j v_j²` of a parameter vector. -/
def sqNorm {d : ℕ} (v : Param d) : ℝ := ∑ j, v j ^ 2

/-- The `ℓ₁` norm `‖v‖₁ = Σ_j |v_j|` of a parameter vector. -/
def l1Norm {d : ℕ} (v : Param d) : ℝ := ∑ j, |v j|

open Classical in

/-- The regularization schedule `λ_{n+1} = c̃ n^{1/4} √(log d + log n)`; `lam c d n` is the
paper's `λ_{n+1}`. -/
noncomputable def lam (c : ℝ) (d n : ℕ) : ℝ :=
  c * (n : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt (Real.log d + Real.log n)

/-- The lasso-regularized quasi-likelihood objective (17) in integrated form. The history
`h : Fin n → Feat d × ℝ × ℝ` lists `(x_k, p_k, D_k)` for the periods `k = 1, …, n`
(entry `k` of `Fin n` is period `k + 1`). For `θ̃` and `λ̃`,
`Qbar = Σ_k χ_k (D_k · (θ̃ · u_k) - ∫₀^{θ̃ · u_k} g) - λ̃ ‖θ̃‖₁`,
which differs from (17) by a term independent of `θ̃` (substitute `y = g(b)` in (17)). -/
noncomputable def Qbar {d : ℕ} (g : ℝ → ℝ) (n : ℕ) (h : Fin n → Feat d × ℝ × ℝ)
    (θ : Param d) (lamt : ℝ) : ℝ :=
  (∑ k : Fin n, BanKeskin.KnownSparsity.chi (k.val + 1) *
      ((h k).2.2 * (θ ⬝ᵥ regr (h k).2.1 (h k).1) -
        ∫ b in (0 : ℝ)..(θ ⬝ᵥ regr (h k).2.1 (h k).1), g b)) -
    lamt * l1Norm θ

/-- The standing model data of §2.1 (pp. 5552–5553) and endnote 2 (p. 5568): price bounds
`0 < ℓ < u`, the compact parameter rectangle `Θ = [lo, hi]`, the compact feature support
`𝒵 ⊆ B₀(z_max)`, two distinct experimental prices `m₁, m₂ ∈ [ℓ, u]`, the link `g`
(differentiable, increasing, with `ℓ̃ ≤ g' ≤ ũ` on the relevant domain) and the
clairvoyant price `φ(θ, x)`, an unconstrained maximizer of `r(·, θ, x)` that lies in `(ℓ, u)`.
The map `(v,z) ↦ φ(clamp(v), [1;z])` is measurable, making the induced pricing rule admissible. -/
structure Model (d : ℕ) where
  one_le_d : 1 ≤ d
  ℓ : ℝ
  u : ℝ
  ℓ_pos : 0 < ℓ
  ℓ_lt_u : ℓ < u
  lo : Param d
  hi : Param d
  lo_le_hi : lo ≤ hi
  Zset : Set (Fin d → ℝ)
  Zset_compact : IsCompact Zset
  zmax : ℝ
  zmax_pos : 0 < zmax
  Zset_ball : ∀ z ∈ Zset, ∑ i, z i ^ 2 ≤ zmax ^ 2
  m1 : ℝ
  m2 : ℝ
  m1_mem : m1 ∈ Set.Icc ℓ u
  m2_mem : m2 ∈ Set.Icc ℓ u
  m1_ne_m2 : m1 ≠ m2
  g : ℝ → ℝ
  g_diff : Differentiable ℝ g
  g_mono : Monotone g
  gl : ℝ
  gu : ℝ
  gl_pos : 0 < gl
  gl_le_gu : gl ≤ gu
  deriv_bounds : ∀ θ ∈ Set.Icc lo hi, ∀ z ∈ Zset, ∀ p ∈ Set.Icc ℓ u,
    gl ≤ deriv g (θ ⬝ᵥ regr p (featX z)) ∧ deriv g (θ ⬝ᵥ regr p (featX z)) ≤ gu
  φ : Param d → Feat d → ℝ
  φ_meas : Measurable (fun a : Param d × (Fin d → ℝ) => φ (clamp lo hi a.1) (featX a.2))
  φ_interior : ∀ θ ∈ Set.Icc lo hi, ∀ z ∈ Zset, φ θ (featX z) ∈ Set.Ioo ℓ u
  φ_max : ∀ θ ∈ Set.Icc lo hi, ∀ z ∈ Zset, ∀ p : ℝ,
    revenue g p θ (featX z) ≤ revenue g (φ θ (featX z)) θ (featX z)

/-- The parameter rectangle `Θ = [lo, hi] ⊂ ℝ^{2(d+1)}`. -/
def Model.Theta {d : ℕ} (M : Model d) : Set (Param d) := Set.Icc M.lo M.hi

/-- The maximal single-period revenue `r*(θ, x) = r(φ(θ, x), θ, x)`. -/
def Model.rstar {d : ℕ} (M : Model d) (θ : Param d) (x : Feat d) : ℝ :=
  revenue M.g (M.φ θ x) θ x

end BanKeskin.UnknownSparsity


