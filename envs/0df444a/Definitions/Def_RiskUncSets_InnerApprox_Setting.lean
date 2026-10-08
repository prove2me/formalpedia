-- Prove2me | Definitions.Def_RiskUncSets_InnerApprox_Setting
-- name    : RiskUncSets_InnerApprox_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T12:48:15.494101+00:00
-- url     : https://prove2.me/theorems/f9b0fc37-2979-46e0-a19e-2d8ea2565d0f
-- title:
--   Defs. 4.6, 4.7, 4.9, (9), (12), (14), (15) — restricted simplices, q-permutohull, the gauge ‖·‖_{q,𝒜}, mixtures with e_N, the polytope 𝒰 and the constraints of LP (15)
-- statement:
--   Fix a number $N \ge 1$ of observations and data points $\mathcal A = \{a_1,\dots,a_N\}$ with $a_i \in \mathbb R^n$, written as the columns of $A$. Write $e_N$ for the vector in $\mathbb R^N$ with $1/N$ at each entry, so that the **sample mean** is $\hat a = A e_N = \frac1N\sum_{i=1}^N a_i$.
--
--   1. The **restricted simplex** is $\hat\Delta^N = \{q \in \Delta^N : q_1 \ge \dots \ge q_N\}$, where $\Delta^N$ is the probability simplex of $\mathbb R^N$ (Definition 4.6).
--   2. For $q \in \mathbb R^N$, the **$q$-permutohull** of $\mathcal A$ is
--   $$\Pi_q(\mathcal A) = \operatorname{conv}\Big\{\sum_{i=1}^N q_{\sigma(i)}\, a_i : \sigma \in S_N\Big\}$$
--   (Definition 4.7; the page states it for $q \in \Delta^N$, here it is defined for every real vector $q$, as the linear program (15) needs).
--   3. The **symmetric restricted simplex** $\hat\Delta^N_{\mathrm{sym}}$ is the set of $q \in \hat\Delta^N$ with $q = 2e_N - q_\sigma$ for some permutation $\sigma$, where $(q_\sigma)_i = q_{\sigma(i)}$ (Definition 4.9 with condition (9)).
--   4. $\tilde\pi_q(\mathcal A) = \Pi_q(\mathcal A) - \hat a$ is the permutohull shifted by $-\hat a$, and
--   $$\|w\|_{q,\mathcal A} = \inf\{\alpha > 0 : w/\alpha \in \tilde\pi_q(\mathcal A)\}$$
--   is its Minkowski functional (gauge); evaluated at $w = a - \hat a$ it is (12).
--   5. For $q \in \mathbb R^N$ and $\lambda \in \mathbb R$, the **mixture** with the generator $e_N$ is $\lambda q + (1-\lambda) e_N$.
--   6. For $u_1,\dots,u_m \in \mathbb R^n$ and $v \in \mathbb R^m$, the polyhedron (14) is $\mathcal U = \{a \in \mathbb R^n : u_k' a \ge v_k,\ k = 1,\dots,m\}$.
--   7. Given $\hat q \in \mathbb R^N$, the value $\lambda$ is **feasible for (15)** if there are $q \in \mathbb R^N$ and $s_k, t_k \in \mathbb R^N$ ($k = 1,\dots,m$) with
--   $$q = \lambda \hat q + (1-\lambda) e/N,\qquad e'(s_k + t_k) \ge v_k\ \ \forall k,\qquad s_{k,i} + t_{k,j} \le (u_k' a_j)\, q_i\ \ \forall (i,j),\ \forall k.$$
--
--   These are the objects of §4.5 of the paper: Theorem 4.5 maximizes $\lambda$ over the feasible set of (15) to find the largest centrally symmetric distortion inner approximation of $\mathcal U$.
--
--   **Formalization Note** Indices run over `Fin N`, i.e. from $0$ to $N-1$; the ordering $q_1 \ge \dots \ge q_N$ is `Antitone q`. The gauge is Mathlib's `gauge`, $\inf\{r > 0 : w \in r\cdot \tilde\pi_q(\mathcal A)\}$, which equals (12) because $w \in r\cdot S \iff w/r \in S$ for $r > 0$; Mathlib's `gauge` takes the value $0$ (not $+\infty$) when no positive multiple of the set contains $w$, which is why the theorems that use it carry the hypotheses stated with them. The polyhedron (14) is not assumed bounded. The variable $q$ of (15) is kept as printed, tied to $\lambda$ by its equality constraint. These definitions duplicate the restricted simplex, symmetric restricted simplex, permutohull and sample mean of missions 1 and 2 of this series (drafts cannot import drafts).
-- source:
--   Bertsimas & Brown, Constructing uncertainty sets for robust linear optimization, Oper. Res. 57(6) (2009), pp. 1489–1493, Definitions 4.6, 4.7, 4.9, (9), (12), (14), (15)

import Mathlib
noncomputable section

namespace RiskUncSets.InnerApprox

/-- Definition 4.6: the restricted simplex `Δ̂ᴺ`, probability vectors with
`q₁ ≥ ⋯ ≥ q_N` (indices are 0-based in Lean). -/
def restrictedSimplex (N : ℕ) : Set (Fin N → ℝ) :=
  {q | q ∈ stdSimplex ℝ (Fin N) ∧ Antitone q}

/-- Definition 4.7: the `q`-permutohull `Π_q(𝒜) = conv {∑ᵢ q_{σ(i)} aᵢ : σ ∈ S_N}`.
Defined for every real vector `q`. -/
def permutohull {N n : ℕ} (q : Fin N → ℝ) (a : Fin N → Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin N) => ∑ i, q (σ i) • a i)

/-- The sample mean `â = A e_N = (1/N) ∑ᵢ aᵢ`. -/
def sampleMean {N n : ℕ} (a : Fin N → Fin n → ℝ) : Fin n → ℝ :=
  ∑ i, (1 / (N : ℝ)) • a i

/-- Definition 4.9 with equation (9): the symmetric restricted simplex `Δ̂ᴺ_sym`,
the `q ∈ Δ̂ᴺ` with `q = 2 e_N − q_σ` for some permutation `σ`, `(q_σ)ᵢ = q_{σ(i)}`. -/
def symRestrictedSimplex (N : ℕ) : Set (Fin N → ℝ) :=
  {q | q ∈ restrictedSimplex N ∧
    ∃ σ : Equiv.Perm (Fin N), q = fun i => 2 / (N : ℝ) - q (σ i)}

/-- `π̃_q(𝒜)`: the permutohull `Π_q(𝒜)` shifted by `−â`. -/
def piTilde {N n : ℕ} (q : Fin N → ℝ) (a : Fin N → Fin n → ℝ) : Set (Fin n → ℝ) :=
  (fun w => w - sampleMean a) '' permutohull q a

/-- Equation (12): `‖w‖_{q,𝒜} = inf {α > 0 | w / α ∈ π̃_q(𝒜)}`, the Minkowski functional
(`gauge`) of `π̃_q(𝒜)` evaluated at `w = a − â`. Mathlib's `gauge` is `0`, not `+∞`,
when no positive multiple of the set contains `w`. -/
def normQ {N n : ℕ} (q : Fin N → ℝ) (a : Fin N → Fin n → ℝ) (w : Fin n → ℝ) : ℝ :=
  gauge (piTilde q a) w

/-- The mixture `λ q + (1 − λ) e_N`, with `e_N` the vector with `1/N` at each entry. -/
def mix {N : ℕ} (q : Fin N → ℝ) (lam : ℝ) : Fin N → ℝ :=
  fun i => lam * q i + (1 - lam) * (1 / (N : ℝ))

/-- Equation (14): the polyhedron `𝒰 = {a ∈ ℝⁿ : u_k′ a ≥ v_k, k = 1, …, m}`. -/
def polytope {n m : ℕ} (u : Fin m → Fin n → ℝ) (v : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {a | ∀ k, v k ≤ u k ⬝ᵥ a}

/-- The constraints of the linear program (15) at the value `lam` of `λ`: there are
`q ∈ ℝᴺ` and `s_k, t_k ∈ ℝᴺ` (`k = 1, …, m`) with `q = λ q̂ + (1 − λ) e/N`,
`e′(s_k + t_k) ≥ v_k` and `s_{k,i} + t_{k,j} ≤ (u_k′ a_j) q_i` for all `i, j, k`. -/
def LP15Feasible {N n m : ℕ} (qh : Fin N → ℝ) (a : Fin N → Fin n → ℝ)
    (u : Fin m → Fin n → ℝ) (v : Fin m → ℝ) (lam : ℝ) : Prop :=
  ∃ (q : Fin N → ℝ) (s t : Fin m → Fin N → ℝ), q = mix qh lam ∧
    (∀ k, v k ≤ ∑ i, (s k i + t k i)) ∧
    ∀ k i j, s k i + t k j ≤ (u k ⬝ᵥ a j) * q i

end RiskUncSets.InnerApprox


