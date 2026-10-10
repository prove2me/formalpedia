-- Prove2me | Definitions.Def_SmoothCCP_PenaltyModel_Setting
-- name    : SmoothCCP_PenaltyModel_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T13:45:53.866879+00:00
-- url     : https://prove2.me/theorems/d79aee4b-7e70-494f-8145-d7dd289c77de
-- title:
--   pp. 6–17 — Γ_ε (2.2), quartic γ_ε (2.6), smoothed quantile Q_ε (2.3), C^N, C̃^N, Q̃_ε, penalty φ_π (5.3), model m (5.6)
-- statement:
--   This module fixes the objects of the exact-penalty approach to a sample-based smoothed chance constraint.
--
--   Fix $\varepsilon>0$ and a function $\gamma_\varepsilon$ on $[-\varepsilon,\varepsilon]$. The **smoothed indicator** is
--   $$
--   \Gamma_\varepsilon(y)=\begin{cases}1, & y\le-\varepsilon,\\ \gamma_\varepsilon(y), & -\varepsilon<y<\varepsilon,\\ 0, & y\ge\varepsilon,\end{cases}
--   $$
--   which is (2.2). The concrete choice used from §4 on is the **quartic kernel** (2.6),
--   $$
--   \gamma_\varepsilon(y)=\frac{15}{16}\Big(-\frac15\big(\tfrac{y}{\varepsilon}\big)^5+\frac23\big(\tfrac{y}{\varepsilon}\big)^3-\frac{y}{\varepsilon}+\frac{8}{15}\Big).
--   $$
--
--   For a risk level $\alpha$ and a vector $z\in\mathbb R^N$, the **smoothed $(1-\alpha)$-quantile** $Q_\varepsilon(z)$ is the root $q$ of equation (2.3),
--   $$
--   \sum_{i=1}^N\Gamma_\varepsilon(z_i-q)=(1-\alpha)N .
--   $$
--   It is defined here as the least $q$ with $\sum_i\Gamma_\varepsilon(z_i-q)\ge(1-\alpha)N$; under the hypotheses of Lemma 2.1 this is the unique root of (2.3).
--
--   Let $c_1,\dots,c_m:\mathbb R^n\times\Xi\to\mathbb R$ be the constraint functions and $\xi_1,\dots,\xi_N$ a fixed sample. Then
--   1. $[C^N(x)]_i=\max_j c_j(x,\xi_i)$ is the vector of sampled constraint values;
--   2. $[\widetilde C^N]_i(x;d)=\max_j\{c_j(x,\xi_i)+\nabla_x c_j(x,\xi_i)^{\mathsf T}d\}$ is the vector of maxima of the linearizations;
--   3. $\widetilde Q_\varepsilon(z;p)=Q_\varepsilon(z)+\nabla Q_\varepsilon(z)^{\mathsf T}p$ is the linearization of the quantile.
--
--   For an objective $f:\mathbb R^n\to\mathbb R$, deterministic constraints $g=(g_1,\dots,g_p):\mathbb R^n\to\mathbb R^p$ and a penalty parameter $\pi$, the **exact penalty function** (5.3) and the **piecewise quadratic model** (5.6) are
--   $$
--   \varphi_\pi(x)=f(x)+\pi\Big(\big\|[g(x)]^+\big\|_1+\big[Q_\varepsilon(C^N(x))\big]^+\Big),
--   $$
--   $$
--   m(x,H;d)=f(x)+\nabla f(x)^{\mathsf T}d+\tfrac12 d^{\mathsf T}Hd+\pi\Big(\big\|[g(x)+\nabla g(x)^{\mathsf T}d]^+\big\|_1+\big[\widetilde Q_\varepsilon\big(C^N(x);\widetilde C^N(x;d)-C^N(x)\big)\big]^+\Big),
--   $$
--   where $[y]^+=\max\{0,y\}$ componentwise.
--
--   These are the objects of the trust-region method of §5: $\varphi_\pi$ is the function minimized, and $m$ is the model whose minimization over a trust region produces each step.
--
--   **Formalization Note** Points of $\mathbb R^n$ live in `EuclideanSpace ℝ (Fin n)`, so gradients and $d^{\mathsf T}Hd=\langle d,Hd\rangle$ are inner products; $H$ is a continuous linear operator. $Q_\varepsilon$ is a function on `Fin N → ℝ`, and $\nabla Q_\varepsilon(z)^{\mathsf T}p$ is its Fréchet derivative applied to $p$. The maximum over $j$ uses `Finset.sup'`, which needs $m\ge1$ (the paper's §5 has $m>1$). The quantile is a least root through `sInf`; the set is nonempty and bounded below whenever $\gamma_\varepsilon$ is as in Lemma 2.1, $0<\alpha<1$ and $N\ge1$, so no junk value enters the statements that use it.
-- source:
--   Peña-Ordieres, Luedtke, Wächter, Solving chance-constrained problems via a smooth sample-based nonlinear approximation, arXiv:1905.07377v2, (2.2) pp. 6–7, (2.3) p. 7, (2.6) p. 8, §5 p. 16, (5.3) p. 17, Proposition 5.3 (5.6) p. 17

import Mathlib
import Definitions.Def_SmoothCCP_Feasibility_Setting

namespace SmoothCCP.PenaltyModel

/-- (2.6), p. 8: the quartic-kernel choice
γ_ε(y) = (15/16)(−(1/5)(y/ε)⁵ + (2/3)(y/ε)³ − (y/ε) + 8/15). -/
noncomputable def quarticGamma (ε y : ℝ) : ℝ :=
  15 / 16 * (-(1 / 5) * (y / ε) ^ 5 + 2 / 3 * (y / ε) ^ 3 - y / ε + 8 / 15)

/-- (2.3), p. 7: the smoothed (1 − α)-quantile Q^{1−α}_ε(z) of `z ∈ ℝᴺ`, taken as the least root
`q` of `Σᵢ Γ_ε(zᵢ − q) = (1 − α)N`. Since `q ↦ Σᵢ Γ_ε(zᵢ − q)` is nondecreasing and continuous for an
admissible γ_ε, the set below is the up-set `[Q, ∞)` of the least root; under the hypotheses of
Lemma 2.1 that root is the unique solution of (2.3). -/
noncomputable def smoothQuantile (ε : ℝ) (γ : ℝ → ℝ) (α : ℝ) {N : ℕ} (z : Fin N → ℝ) : ℝ :=
  sInf {q : ℝ | (1 - α) * N ≤ ∑ i, SmoothCCP.Feasibility.Gam ε γ (z i - q)}

/-- p. 4 and p. 16: [C^N(x)]ᵢ = C(x, ξᵢ) = maxⱼ cⱼ(x, ξᵢ), on sample values `ξs`
(`c j x s` is cⱼ(x, s); `1 ≤ m` makes the maximum over `j` well defined). -/
noncomputable def CN {n m N : ℕ} {Ξ : Type} (hm : 1 ≤ m)
    (c : Fin m → EuclideanSpace ℝ (Fin n) → Ξ → ℝ) (ξs : Fin N → Ξ)
    (x : EuclideanSpace ℝ (Fin n)) : Fin N → ℝ :=
  fun i => Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩) (fun j => c j x (ξs i))

/-- Proposition 5.3, p. 17: [C̃^N]ᵢ(x; d) = maxⱼ {cⱼ(x, ξᵢ) + ∇cⱼ(x, ξᵢ)ᵀd}. -/
noncomputable def Ctil {n m N : ℕ} {Ξ : Type} (hm : 1 ≤ m)
    (c : Fin m → EuclideanSpace ℝ (Fin n) → Ξ → ℝ) (ξs : Fin N → Ξ)
    (x d : EuclideanSpace ℝ (Fin n)) : Fin N → ℝ :=
  fun i => Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩)
    (fun j => c j x (ξs i) + inner ℝ (gradient (fun y => c j y (ξs i)) x) d)

/-- Proposition 5.3, p. 17: Q̃_ε(z; p) = Q_ε(z) + ∇Q_ε(z)ᵀp. -/
noncomputable def Qtil {N : ℕ} (Q : (Fin N → ℝ) → ℝ) (z p : Fin N → ℝ) : ℝ :=
  Q z + fderiv ℝ Q z p

/-- (5.3), p. 17: the ℓ₁ exact penalty
φ_π(x) = f(x) + π(‖[g(x)]⁺‖₁ + [Q_ε(C^N(x))]⁺), with `g k` the components of g : ℝⁿ → ℝᵖ. -/
noncomputable def penalty {n m p N : ℕ} {Ξ : Type} (hm : 1 ≤ m)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : Fin p → EuclideanSpace ℝ (Fin n) → ℝ)
    (c : Fin m → EuclideanSpace ℝ (Fin n) → Ξ → ℝ) (ξs : Fin N → Ξ)
    (ε : ℝ) (γ : ℝ → ℝ) (α π : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  f x + π * ((∑ k, max 0 (g k x)) + max 0 (smoothQuantile ε γ α (CN hm c ξs x)))

/-- (5.6), p. 17: the piecewise quadratic model
m(x, H; d) = f(x) + ∇f(x)ᵀd + ½dᵀHd + π(‖[g(x) + ∇g(x)ᵀd]⁺‖₁ + [Q̃_{ε,C}(x; d)]⁺), where
Q̃_{ε,C}(x; d) = Q̃_ε(C^N(x); C̃^N(x; d) − C^N(x)). -/
noncomputable def model {n m p N : ℕ} {Ξ : Type} (hm : 1 ≤ m)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : Fin p → EuclideanSpace ℝ (Fin n) → ℝ)
    (c : Fin m → EuclideanSpace ℝ (Fin n) → Ξ → ℝ) (ξs : Fin N → Ξ)
    (ε : ℝ) (γ : ℝ → ℝ) (α π : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (d : EuclideanSpace ℝ (Fin n)) : ℝ :=
  f x + inner ℝ (gradient f x) d + 1 / 2 * inner ℝ d (H d)
    + π * ((∑ k, max 0 (g k x + inner ℝ (gradient (g k) x) d))
      + max 0 (Qtil (smoothQuantile ε γ α) (CN hm c ξs x) (Ctil hm c ξs x d - CN hm c ξs x)))

end SmoothCCP.PenaltyModel


