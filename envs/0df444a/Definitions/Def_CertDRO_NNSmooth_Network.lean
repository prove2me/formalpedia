-- Prove2me | Definitions.Def_CertDRO_NNSmooth_Network
-- name    : CertDRO_NNSmooth_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T17:31:55.592143+00:00
-- url     : https://prove2.me/theorems/09c223fb-e7fc-4e8d-93d6-171927d0167d
-- title:
--   Layered network F_l(θ; x), the constants α_l(θ), β_l(θ) of (21), Assumption E, and the tail Jacobian products of (34)
-- statement:
--   This file fixes the deep-network model of §4 of Sinha, Namkoong, Volpi and Duchi.
--
--   **Network.** A layered network consists of widths $d_{l,O}$ (output of layer $l$, with $d_{0,O}=p$ the input dimension) and $d_{l,I}$ (pre-activation of layer $l$), weight matrices $\theta_l:\mathbb R^{d_{l-1,O}}\to\mathbb R^{d_{l,I}}$, and nonlinear operations $\sigma_l:\mathbb R^{d_{l,I}}\to\mathbb R^{d_{l,O}}$ (activations, pooling, …), for $l=1,2,\dots$. Every space carries the Euclidean norm $\|\cdot\|_2$, and $\|\theta_l\|_{\mathrm{op}}$ is the $\ell_2$-operator (spectral) norm. The output of the first $l$ layers is defined by (20),
--   $$F_0(\theta;x)=x,\qquad F_l(\theta;x)=\sigma_l\big(\theta_l\cdot F_{l-1}(\theta;x)\big),$$
--   so that $F_l(\theta;x)=\sigma_l(\theta_l\cdot\sigma_{l-1}(\theta_{l-1}\cdots\sigma_1(\theta_1\cdot x)\cdots))$.
--
--   **Constants (21).** Given layer constants $L^0_l$ and $L^1_l$,
--   $$\alpha_l(\theta)=\prod_{j=1}^{l}L^0_j\|\theta_j\|_{\mathrm{op}},\qquad \beta_l(\theta)=\alpha_l(\theta)\sum_{j=1}^{l}\frac{L^1_j}{(L^0_j)^2}\,\alpha_j(\theta).$$
--   In particular $\alpha_0(\theta)=1$ and $\beta_0(\theta)=0$.
--
--   **Assumption E** (for a network of depth $L$). For all $l=1,\dots,L$: $\sigma_l$ is differentiable; $\sigma_l$ is $L^0_l$-Lipschitz for $\|\cdot\|_2$; its Jacobian $J\sigma_l$ is $L^1_l$-Lipschitz from $(\mathbb R^{d_{l,I}},\|\cdot\|_2)$ to the linear maps with $\|\cdot\|_{\mathrm{op}}$, i.e. $\|J\sigma_l(u)-J\sigma_l(v)\|_{\mathrm{op}}\le L^1_l\|u-v\|_2$; $L^0_l>0$; and $L^1_l\ge0$.
--
--   **Tail products.** For inputs $x'$ and layers $j\le l$, the linear map
--   $$\prod_{k=j+1}^{l}\nabla\sigma_k\big(\theta_k\cdot F_{k-1}(\theta;x')\big)\cdot\theta_k:\ \mathbb R^{d_{j,O}}\to\mathbb R^{d_{l,O}}$$
--   is the composition of the factors in network order ($A_l\cdots A_{j+1}$), and the identity when $j=l$ (empty product). It is term (a) of the telescoping representation (34).
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Layers are indexed from $0$: Lean layer `l` is the paper's layer $l+1$, so `θ l` is $\theta_{l+1}$, `σ l` is $\sigma_{l+1}$, `L0 l` is $L^0_{l+1}$ and `L1 l` is $L^1_{l+1}$; `F l`, `α L0 l`, `β L0 L1 l` carry the paper's index $l$ (number of layers applied). Widths `dO l` $=d_{l,O}$ and `dI l` $=d_{l,I}$ vary with the layer. Weights are continuous linear maps between Euclidean spaces, so their norm is the spectral norm. Jacobians are Fréchet derivatives (`fderiv`) with the operator norm. The network carries layers for every natural number; a depth-$L$ network uses only the first $L$, and Assumption E constrains only those. Differentiability of $\sigma_l$ is implicit in the paper's Assumption E (it speaks of the Jacobian) and is stated explicitly; $L^1_l\ge0$ is the usual reading of "Lipschitz constant". The tail product is defined by recursion on its last layer; for $j=l$ a type cast identifies $\mathbb R^{d_{j,O}}$ with $\mathbb R^{d_{l,O}}$, and for $j>l$ it is the zero map (never used).
-- source:
--   Sinha, Namkoong, Volpi, Duchi, Certifying Some Distributional Robustness with Principled Adversarial Training, arXiv:1710.10571v5, p. 12, (20) and Assumption E; p. 13, (21); p. 45, (34) term (a) and the convention F_0(θ; x) = x

import Mathlib

namespace CertDRO.NNSmooth

/-- The Euclidean space `ℝ^n` with the ℓ²-norm. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A layered network (§4, p. 12, (20)), with **0-based layer indices**: Lean layer `l` is the paper's
layer `l + 1`.

* `dO l` is the paper's output width `d_{l,O}` of layer `l`; `dO 0 = p` is the input dimension.
* `dI l` is the paper's pre-activation width `d_{l,I}` of layer `l` (used for `l ≥ 1`).
* `θ l : ℝ^{d_{l,O}} → ℝ^{d_{l+1,I}}` is the weight matrix `θ_{l+1}` of the paper, as a continuous
  linear map; its norm `‖θ l‖` is the ℓ²-operator (spectral) norm `‖θ_{l+1}‖_op`.
* `σ l : ℝ^{d_{l+1,I}} → ℝ^{d_{l+1,O}}` is the nonlinear operation `σ_{l+1}` applied after the
  `(l+1)`-st linear layer.

The layers are indexed by all of `ℕ`; a network of depth `L` uses only the layers `l < L`. -/
structure Network where
  dO : ℕ → ℕ
  dI : ℕ → ℕ
  θ : (l : ℕ) → E (dO l) →L[ℝ] E (dI (l + 1))
  σ : (l : ℕ) → E (dI (l + 1)) → E (dO (l + 1))

namespace Network

variable (N : Network)

/-- The output `F_l(θ; x)` of the first `l` layers, (20): `F_0(θ; x) = x` (p. 45) and
`F_{l+1}(θ; x) = σ_{l+1}(θ_{l+1} · F_l(θ; x))`. -/
noncomputable def F : (l : ℕ) → E (N.dO 0) → E (N.dO l)
  | 0, x => x
  | l + 1, x => N.σ l (N.θ l (F l x))

/-- `α_l(θ) = ∏_{j=1}^{l} L⁰_j ‖θ_j‖_op`, (21). In 0-based indices: `α l = ∏_{j<l} L0 j * ‖θ j‖`,
where `L0 j` is the constant `L⁰_{j+1}` of the paper's layer `j + 1`. In particular `α 0 = 1`. -/
noncomputable def α (L0 : ℕ → ℝ) (l : ℕ) : ℝ :=
  ∏ j ∈ Finset.range l, L0 j * ‖N.θ j‖

/-- `β_l(θ) = α_l(θ) ∑_{j=1}^{l} (L¹_j / (L⁰_j)²) α_j(θ)`, (21). In 0-based indices:
`β l = α l * ∑_{j<l} (L1 j / (L0 j)^2) * α (j+1)`. In particular `β 0 = 0` (empty sum). -/
noncomputable def β (L0 L1 : ℕ → ℝ) (l : ℕ) : ℝ :=
  N.α L0 l * ∑ j ∈ Finset.range l, (L1 j / (L0 j) ^ 2) * N.α L0 (j + 1)

/-- Assumption E (p. 12) for the first `L` layers, with constants `L0 l = L⁰_{l+1}` and
`L1 l = L¹_{l+1}`: for every `l < L`, the map `σ l` is differentiable, `L0 l`-Lipschitz for the
ℓ²-norm, its Jacobian (Fréchet derivative, a continuous linear map with the operator norm) is
`L1 l`-Lipschitz from `(ℝ^{d_I}, ‖·‖₂)` to `(linear maps, ‖·‖_op)`, `L0 l > 0`, and `L1 l ≥ 0`. -/
structure AssumptionE (L : ℕ) (L0 L1 : ℕ → ℝ) : Prop where
  differentiable : ∀ l < L, Differentiable ℝ (N.σ l)
  lipschitz : ∀ l < L, ∀ u v, ‖N.σ l u - N.σ l v‖ ≤ L0 l * ‖u - v‖
  jacobian_lipschitz : ∀ l < L, ∀ u v,
    ‖fderiv ℝ (N.σ l) u - fderiv ℝ (N.σ l) v‖ ≤ L1 l * ‖u - v‖
  L0_pos : ∀ l < L, 0 < L0 l
  L1_nonneg : ∀ l < L, 0 ≤ L1 l

/-- The tail product of Jacobians at the input `x'` that appears as term (a) of (34), p. 45:
for `j ≤ l`, `tailJac x' j l : ℝ^{d_{j,O}} → ℝ^{d_{l,O}}` is the composition, over the (0-based)
layers `k = j, …, l - 1`, of `u ↦ Jσ_k(θ_k · F_k(θ; x')) · θ_k · u`, applied in the order of the
network (the paper's `∏_{k=j+1}^{l} ∇σ_k(θ_k · F_{k-1}(θ; x')) · θ_k` in 1-based indices, with
`A_l ⋯ A_{j+1}` ordering). For `j = l` it is the identity (the empty product); the cast only
identifies `ℝ^{d_{j,O}}` with `ℝ^{d_{l,O}}` when `j = l`. For `j > l` it is `0` (never used). -/
noncomputable def tailJac (x' : E (N.dO 0)) (j : ℕ) : (l : ℕ) → E (N.dO j) →L[ℝ] E (N.dO l)
  | 0 =>
    if h : j = 0 then
      cast (congrArg (fun i => E (N.dO j) →L[ℝ] E (N.dO i)) h) (ContinuousLinearMap.id ℝ _)
    else 0
  | l + 1 =>
    if h : j = l + 1 then
      cast (congrArg (fun i => E (N.dO j) →L[ℝ] E (N.dO i)) h) (ContinuousLinearMap.id ℝ _)
    else
      (fderiv ℝ (N.σ l) (N.θ l (N.F l x'))).comp ((N.θ l).comp (tailJac x' j l))

end Network

end CertDRO.NNSmooth


