-- Prove2me | Definitions.Def_PINNConvergence_Basic
-- name    : PINNConvergence_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-23T20:03:50.076312+00:00
-- url     : https://prove2.me/theorems/aa7ec20f-a2b2-4c71-825f-b937427b5469
-- title:
--   Hölder spaces, neural networks, PINN losses and the elliptic Dirichlet problem (Shin–Darbon–Karniadakis)
-- statement:
--   Objects of Sections 2 and 3 and Appendices B and D of Shin, Darbon and Karniadakis (2020).
--
--   1. **Hölder quantities (Section 2.1, eq. 2.6, Definition 2.1).** For $S\subseteq\mathbb{R}^d$ (Euclidean norm), $[u]_{\alpha;S}=\sup_{x\ne y\in S}\|u(x)-u(y)\|/\|x-y\|^\alpha\in[0,\infty]$, also for vector-valued $u$ such as $D^ku$. $u\in C^{k,\alpha}(S)$ means: $u\in C^k(S)$, every derivative of order $\le k$ is bounded on $S$, and $[D^ku]_{\alpha;S}<\infty$. $u\in C^k(\overline U)$ means $u\in C^k(U)$ with derivatives of order $\le k$ extending continuously to $\overline U$. $h_n\to u$ in $C^k$ means that every derivative of order $\le k$ converges uniformly on $U$. $\|u\|_{C^0(S)}=\sup_S|u|\in[0,\infty]$.
--   2. **Domains (Definition 2.2).** A bounded domain is a bounded, open, connected set. It is of class $C^{0,1}$ if at each $x_0\in\partial U$ there are a ball $B$ about $x_0$ and a bi-Lipschitz map $\psi$ on $B$ with $\psi(B\cap U)\subseteq\{y_i>0\}$ and $\psi(B\cap\partial U)\subseteq\{y_i=0\}$.
--   3. **Data distributions (Assumption 3.1, $d\ge2$).** $U$ is a bounded $C^{0,1}$ domain and $\Gamma\subseteq\partial U$ is closed. $\mu_r$ is a probability measure with a density $\rho_r$ with respect to Lebesgue measure on $U$, $\inf_U\rho_r>0$. $\mu_b$ is a probability measure with a density $\rho_b$ with respect to $(d-1)$-dimensional Hausdorff measure on $\Gamma$, $\inf_\Gamma\rho_b>0$. For every $\varepsilon>0$ with $c_r\varepsilon^d\le1$ there is a finite measurable partition $\{U_j\}$ of $U$ with points $z_j\in U_j$ such that $U_j$ lies in the closed axis-parallel cube $H_\varepsilon(z_j)$ of side $\varepsilon$ and $\mu_r(U_j)\ge c_r\varepsilon^d$. The same holds for $\Gamma$, $\mu_b$ and $c_b\varepsilon^{d-1}$. Moreover $\mu_r(B_\varepsilon(x)\cap U)\le C_r\varepsilon^d$ for $x\in U$ and $\mu_b(B_\varepsilon(x)\cap\Gamma)\le C_b\varepsilon^{d-1}$ for $x\in\Gamma$, for all $\varepsilon>0$ (closed balls). The constants satisfy $c_r,C_r,c_b,C_b>0$.
--   4. **Networks (Section 2.2, eq. 2.8).** For an activation $\sigma$, an architecture $(n_0=d,n_1,\dots,n_L=1)$ with $L\ge1$ and positive widths, and parameters $\theta=\{W^\ell,b^\ell\}$: $h^1(x)=W^1x+b^1$ and $h^\ell(x)=W^\ell\sigma(h^{\ell-1}(x))+b^\ell$. The network is $h^L$. $\mathcal H^{NN}_{\vec n}$ is the class of all such networks of a fixed architecture.
--   5. **Losses (eqs. 2.2-2.5, 3.1-3.3).** For operators $\mathcal L,\mathcal B$, data $f,g$, weights $\lambda_r,\lambda_b$ and samples $x_r^1,\dots,x_r^{m_r}$, $x_b^1,\dots,x_b^{m_b}$: $\mathrm{Loss}^{PINN}_m(h)=\frac{\lambda_r}{m_r}\sum_i(\mathcal L[h](x_r^i)-f(x_r^i))^2+\frac{\lambda_b}{m_b}\sum_i(\mathcal B[h](x_b^i)-g(x_b^i))^2$ and $\mathrm{Loss}^{PINN}(h)=\lambda_r\|\mathcal L[h]-f\|^2_{L^2(\mu_r)}+\lambda_b\|\mathcal B[h]-g\|^2_{L^2(\mu_b)}\in[0,\infty]$. The regularized loss is $\mathrm{Loss}_m(h;\lambda,\lambda^R)=\mathrm{Loss}^{PINN}_m(h)+\lambda_r^RR_r(h)+\lambda_b^RR_b(h)$. The Hölder regularized loss (3.3) is the case $R_r(h)=[\mathcal L[h]]^2_{\alpha;U}$, $R_b(h)=[\mathcal B[h]]^2_{\alpha;\Gamma}$, valued in $[0,\infty]$. The constants of (3.1) are $C_m=3\max\{\kappa_r\sqrt d^{\,d}m_r^{1/2},\kappa_b\sqrt d^{\,d-1}m_b^{1/2}\}$ with $\kappa=C/c$, $\hat\lambda^R_{r,m}=3\lambda_r\sqrt d^{\,2\alpha}c_r^{-2\alpha/d}m_r^{-\alpha/d}/C_m$ and $\hat\lambda^R_{b,m}=3\lambda_b\sqrt d^{\,2\alpha}c_b^{-2\alpha/(d-1)}m_b^{-\alpha/(d-1)}/C_m$. Condition (3.2) along $m_r=m$, $m_b=m_b(m)$ is: $\lambda^R_m\ge\hat\lambda^R_m$ entrywise and $\|\lambda^R_m\|_\infty\le K\|\hat\lambda^R_m\|_\infty$ for some $K$.
--   6. **Sampling and network classes (Assumption 3.2).** For each $m\ge1$ the $m$ residual and $m_b(m)$ boundary samples are iid from $\mu_r$ and $\mu_b$, the two sets independent. The class $\mathcal H_m$, which may depend on the samples, consists of networks in $C^{k,\alpha}(U)\cap C^{0,\alpha}(\overline U)$ with $\mathcal L[h]\in C^{0,\alpha}(U)$ and $\mathcal B[h]\in C^{0,\alpha}(\Gamma)$. It contains some $u^*_m$ with zero empirical PINN loss, and $\sup_m[\mathcal L[u^*_m]]_{\alpha;U}$ and $\sup_m[\mathcal B[u^*_m]]_{\alpha;\Gamma}$ are finite. Also $0<\alpha\le1$, $f\in C^{0,\alpha}(U)$ and $g\in C^{0,\alpha}(\Gamma)$.
--   7. **Elliptic problem (eq. 3.6, Assumption 3.3).** $\mathcal L[u]=\sum_iD_i\big(\sum_ja^{ij}D_ju+b^iu\big)+\sum_ic^iD_iu+e\,u$, where $e$ is the paper's coefficient $d(x)$. The auxiliary coefficients are $\tilde b^i=\sum_jD_ja^{ij}+b^i+c^i$ and $\tilde c=\sum_iD_ib^i+e$. A classical solution is $u\in C^2(U)\cap C^0(\overline U)$ with $\mathcal L[u]=f$ in $U$ and $u=g$ on $\partial U$. Assumption 3.3 consists of:
--      - $\alpha\in(0,1)$;
--      - $a^{ij}=a^{ji}$ and $\sum_{ij}a^{ij}\xi_i\xi_j\ge\lambda_0|\xi|^2$ with $\lambda_0>0$;
--      - $c^i,e\in C^\alpha(U)$, $a^{ij},b^i\in C^{1,\alpha}(U)$, $f\in C^{0,\alpha}(U)$ and $g\in C^{0,\alpha}(\partial U)$;
--      - an exterior sphere at every boundary point;
--      - $\sum|a^{ij}|^2\le\Lambda$ and $\lambda_0^{-2}(|b|^2+|c|^2)+\lambda_0^{-1}|e|\le v^2$.
--   8. **$H^1$ distance.** $\|u-w\|^2_{H^1(U)}=\int_U\big(|\nabla(u-w)|^2+|u-w|^2\big)\,dx\in[0,\infty]$ for functions that are $C^1$ on $U$.
--
--   **Formalization Note** The paper requires the cube partitions for every $\varepsilon>0$. No probability measure satisfies this once $c\varepsilon^s>1$, so it is required for $c\varepsilon^s\le1$, the only range the proofs use. Partition pieces are assumed measurable. Networks have scalar output. The output of the last layer, which has width $1$, is written as a sum over its single coordinate. Real quantities that may be infinite (Hölder constants, sup norms, the expected loss, the Hölder regularized loss) take values in $[0,\infty]$.
-- source:
--   Shin, Darbon and Karniadakis, On the convergence of physics informed neural networks for linear second-order elliptic and parabolic type PDEs, arXiv:2004.01806v2 (2020), Section 2 (eqs. (2.2)-(2.6), (2.8), Definitions 2.1-2.2), Section 3 (Assumptions 3.1-3.3, eqs. (3.1)-(3.3), (3.6)), Appendices B and D

import Mathlib

/-!
Shin, Darbon and Karniadakis, *On the convergence of physics informed neural networks for linear
second-order elliptic and parabolic type PDEs*, arXiv:2004.01806v2 (2020): the Hölder constants
and spaces of Section 2.1, the feed-forward networks of Section 2.2 (eq. (2.8)), the PINN losses
(2.2)–(2.5), Assumptions 3.1–3.3, the weights (3.1)–(3.2), the Hölder regularized loss (3.3), and
the linear elliptic Dirichlet problem (3.6) of Section 3.
-/

open MeasureTheory

noncomputable section

namespace PINNConvergence

/-- Section 2: the space `ℝ^d` of the paper, with the Euclidean norm. -/
abbrev Rd (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

/-- Eq. (2.6), Section 2.1: the Hölder constant `[u]_{α;S} = sup_{x,y ∈ S, x ≠ y} ‖u x - u y‖ / ‖x - y‖^α`,
valued in `[0, ∞]`. For a vector-valued `u` (such as `D^k u`) it is the quantity used in `[u]_{k,α;S}`. -/
def holderConst {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] (α : ℝ) (S : Set E)
    (u : E → F) : ENNReal :=
  ⨆ x ∈ S, ⨆ y ∈ S, ⨆ (_ : x ≠ y), ENNReal.ofReal (‖u x - u y‖ / ‖x - y‖ ^ α)

/-- Section 2.1: the sup norm `sup_{x ∈ S} ‖u x‖` (the `C^0(S)` norm, and `[u]_{j,0;S}` for `u = D^j v`),
valued in `[0, ∞]`. -/
def supNorm {E F : Type*} [NormedAddCommGroup F] (S : Set E) (u : E → F) : ENNReal :=
  ⨆ x ∈ S, ‖u x‖ₑ

/-- Definition 2.1: `u ∈ C^{k,α}(S)`: `u` is `k` times continuously differentiable on `S`, its
derivatives of order `≤ k` are bounded on `S`, and `[D^k u]_{α;S} < ∞`. For `k = 0` this is
`C^{0,α}(S)`: `u` is continuous and bounded on `S` with finite Hölder constant. -/
def IsHolderCk {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ) (α : ℝ) (S : Set E)
    (u : E → ℝ) : Prop :=
  ContDiffOn ℝ k u S ∧ (∀ j ≤ k, supNorm S (iteratedFDerivWithin ℝ j u S) < ⊤) ∧
    holderConst α S (iteratedFDerivWithin ℝ k u S) < ⊤

/-- Section 2.1: `u ∈ C^k(closure U)`: `u ∈ C^k(U)` and each derivative of order `≤ k` has a
continuous extension to the closure of `U`. -/
def IsCkClosure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ) (U : Set E)
    (u : E → ℝ) : Prop :=
  ContDiffOn ℝ k u U ∧ ∀ j ≤ k, ∃ F : E → ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℝ,
    ContinuousOn F (closure U) ∧ ∀ x ∈ U, F x = iteratedFDerivWithin ℝ j u U x

/-- Section 2.1: convergence `h_n → u` in the norm `‖·‖_{C^k} = ∑_{j ≤ k} [·]_{j,0;U}`, i.e. every
derivative of order `j ≤ k` converges uniformly on `U`. -/
def TendstoCk {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ) (U : Set E)
    (h : ℕ → E → ℝ) (u : E → ℝ) : Prop :=
  ∀ j ≤ k, TendstoUniformlyOn (fun n => iteratedFDerivWithin ℝ j (h n) U)
    (iteratedFDerivWithin ℝ j u U) Filter.atTop U

/-- Section 2: a bounded domain, i.e. a bounded, open and connected subset of `ℝ^d`. -/
def IsBoundedDomain {d : ℕ} (U : Set (Rd d)) : Prop :=
  Bornology.IsBounded U ∧ IsOpen U ∧ IsConnected U

/-- Definition 2.2 with `(k, α) = (0, 1)`: a bounded domain of class `C^{0,1}`. At each `x₀ ∈ ∂U`
there are a ball `B = B(x₀, r)` and a map `ψ` that is bi-Lipschitz on `B` (so `ψ ∈ C^{0,1}(B)` is
one-to-one and `ψ⁻¹ ∈ C^{0,1}(ψ(B))`) with `ψ(B ∩ U)` in the half-space `{y_i > 0}` and
`ψ(B ∩ ∂U)` in its boundary `{y_i = 0}`. -/
def IsDomainC01 {d : ℕ} (U : Set (Rd d)) : Prop :=
  IsBoundedDomain U ∧
    ∀ x₀ ∈ frontier U, ∃ r > 0, ∃ ψ : Rd d → Rd d, ∃ K > 0, ∃ i : Fin d,
      (∀ x ∈ Metric.ball x₀ r, ∀ y ∈ Metric.ball x₀ r,
        dist (ψ x) (ψ y) ≤ K * dist x y ∧ dist x y ≤ K * dist (ψ x) (ψ y)) ∧
      (∀ x ∈ Metric.ball x₀ r ∩ U, 0 < ψ x i) ∧
      (∀ x ∈ Metric.ball x₀ r ∩ frontier U, ψ x i = 0)

/-- Assumption 3.1 (2): the closed axis-parallel cube `H_ε(z)` of side length `ε` centred at `z`. -/
def cube {d : ℕ} (z : Rd d) (ε : ℝ) : Set (Rd d) :=
  {y | ∀ i, |y i - z i| ≤ ε / 2}

/-- Assumption 3.1 (2)–(3) and Lemma B.2: for every `ε > 0` with `c ε^s ≤ 1` there is a finite
partition of `S` into measurable pieces `S_j`, each containing a point `z_j` with `S_j ⊆ H_ε(z_j)`
and `μ(S_j) ≥ c ε^s`. (The paper asks this for every `ε > 0`, which no probability measure
satisfies once `c ε^s > 1`; see the Formalization Note.) -/
def HasCubePartitions {d : ℕ} (S : Set (Rd d)) (μ : Measure (Rd d)) (c : ℝ) (s : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → c * ε ^ s ≤ 1 →
    ∃ (K : ℕ) (P : Fin K → Set (Rd d)) (z : Fin K → Rd d),
      (∀ j, MeasurableSet (P j)) ∧ Pairwise (fun i j => Disjoint (P i) (P j)) ∧
      (⋃ j, P j) = S ∧ ∀ j, z j ∈ P j ∧ P j ⊆ cube (z j) ε ∧ ENNReal.ofReal (c * ε ^ s) ≤ μ (P j)

/-- Assumption 3.1 (items 1–3, the case `d ≥ 2`): `U` is a bounded domain of class `C^{0,1}`,
`Γ ⊆ ∂U` is closed, `μ_r` is a probability measure with density `ρ_r` with respect to Lebesgue
measure on `U`, `inf_U ρ_r > 0`, `μ_b` is a probability measure with density `ρ_b` with respect to
the `(d-1)`-dimensional Hausdorff measure on `Γ`, `inf_Γ ρ_b > 0`, the cube partitions exist with
constants `c_r, c_b > 0`, and `μ_r(B_ε(x) ∩ U) ≤ C_r ε^d`, `μ_b(B_ε(x) ∩ Γ) ≤ C_b ε^{d-1}` for
closed balls. -/
def DataDistAssumption {d : ℕ} (U Gam : Set (Rd d)) (μr μb : Measure (Rd d))
    (cr Cr cb Cb : ℝ) : Prop :=
  IsDomainC01 U ∧ IsClosed Gam ∧ Gam ⊆ frontier U ∧
    IsProbabilityMeasure μr ∧ IsProbabilityMeasure μb ∧
    (∃ ρ : Rd d → ENNReal, Measurable ρ ∧ μr = (volume.restrict U).withDensity ρ ∧
      ∃ ρ₀ : ENNReal, 0 < ρ₀ ∧ ∀ x ∈ U, ρ₀ ≤ ρ x) ∧
    (∃ ρ : Rd d → ENNReal, Measurable ρ ∧
      μb = ((Measure.hausdorffMeasure ((d : ℝ) - 1)).restrict Gam).withDensity ρ ∧
      ∃ ρ₀ : ENNReal, 0 < ρ₀ ∧ ∀ x ∈ Gam, ρ₀ ≤ ρ x) ∧
    0 < cr ∧ 0 < Cr ∧ 0 < cb ∧ 0 < Cb ∧
    HasCubePartitions U μr cr d ∧ HasCubePartitions Gam μb cb (d - 1) ∧
    (∀ ε : ℝ, 0 < ε → ∀ x ∈ U, μr (Metric.closedBall x ε ∩ U) ≤ ENNReal.ofReal (Cr * ε ^ d)) ∧
    (∀ ε : ℝ, 0 < ε → ∀ x ∈ Gam,
      μb (Metric.closedBall x ε ∩ Gam) ≤ ENNReal.ofReal (Cb * ε ^ (d - 1)))

/-- Section 2.2: the number of inputs of layer `l` (0-indexed): `d` for the first layer and the
width `n l` of the previous layer otherwise. -/
def inWidth (d : ℕ) (n : ℕ → ℕ) : ℕ → ℕ
  | 0 => d
  | l + 1 => n l

/-- Section 2.2: the output of layer `l + 1` of a feed-forward network (layers are 0-indexed here):
`h¹(x) = W¹ x + b¹` and `h^{ℓ}(x) = W^{ℓ} σ(h^{ℓ-1}(x)) + b^{ℓ}`, `σ` applied entrywise. -/
def layerOut (σ : ℝ → ℝ) (d : ℕ) (n : ℕ → ℕ)
    (W : ∀ l, Matrix (Fin (n l)) (Fin (inWidth d n l)) ℝ) (b : ∀ l, Fin (n l) → ℝ)
    (x : Fin d → ℝ) : ∀ l : ℕ, Fin (n l) → ℝ
  | 0 => (W 0).mulVec x + b 0
  | l + 1 => (W (l + 1)).mulVec (fun i => σ (layerOut σ d n W b x l i)) + b (l + 1)

/-- Section 2.2: the architecture `(n₀ = d, n₁, …, n_L)` of a scalar network with `L ≥ 1` layers,
all widths positive and output width `n_L = 1` (`n l` here is the paper's `n_{l+1}`). -/
def IsArch (L : ℕ) (n : ℕ → ℕ) : Prop :=
  1 ≤ L ∧ (∀ l < L, 1 ≤ n l) ∧ n (L - 1) = 1

/-- Section 2.2: the scalar network `h^L(x; θ_L)` with parameters `θ_L = {W^j, b^j}`. For an
architecture with `n_L = 1` the sum has the single term `h^L(x)`. -/
def nnEval (σ : ℝ → ℝ) (d L : ℕ) (n : ℕ → ℕ)
    (W : ∀ l, Matrix (Fin (n l)) (Fin (inWidth d n l)) ℝ) (b : ∀ l, Fin (n l) → ℝ)
    (x : Rd d) : ℝ :=
  ∑ i, layerOut σ d n W b (WithLp.ofLp x) (L - 1) i

/-- Eq. (2.8): the class `H^{NN}_{n}` of networks with activation `σ` and fixed architecture. -/
def nnClass (σ : ℝ → ℝ) (d L : ℕ) (n : ℕ → ℕ) : Set (Rd d → ℝ) :=
  {h | ∃ W b, h = nnEval σ d L n W b}

/-- Section 2.2: `h` is a feed-forward network with activation `σ` (of some architecture). -/
def IsNeuralNet (σ : ℝ → ℝ) (d : ℕ) (h : Rd d → ℝ) : Prop :=
  ∃ (L : ℕ) (n : ℕ → ℕ), IsArch L n ∧ h ∈ nnClass σ d L n

/-- Lemma 2.1: all weights and biases of the `L` layers are bounded in absolute value by `M`. -/
def ParamsBounded {d : ℕ} {n : ℕ → ℕ} (L : ℕ)
    (W : ∀ l, Matrix (Fin (n l)) (Fin (inWidth d n l)) ℝ) (b : ∀ l, Fin (n l) → ℝ) (M : ℝ) :
    Prop :=
  ∀ l < L, (∀ i j, |W l i j| ≤ M) ∧ ∀ i, |b l i| ≤ M

/-- Eq. (2.5): the empirical PINN loss
`(λ_r/m_r) ∑_i (L[h](x_r^i) - f(x_r^i))² + (λ_b/m_b) ∑_i (B[h](x_b^i) - g(x_b^i))²`. -/
def pinnLossEmp {E : Type*} (Lop Bop : (E → ℝ) → E → ℝ) (f g : E → ℝ) (lr lb : ℝ)
    {mr mb : ℕ} (xr : Fin mr → E) (xb : Fin mb → E) (h : E → ℝ) : ℝ :=
  lr / mr * ∑ i, (Lop h (xr i) - f (xr i)) ^ 2 + lb / mb * ∑ j, (Bop h (xb j) - g (xb j)) ^ 2

/-- Eq. (2.5): the expected PINN loss `λ_r ‖L[h] - f‖²_{L²(μ_r)} + λ_b ‖B[h] - g‖²_{L²(μ_b)}`,
valued in `[0, ∞]`. -/
def pinnLossExp {E : Type*} [MeasurableSpace E] (Lop Bop : (E → ℝ) → E → ℝ) (f g : E → ℝ)
    (lr lb : ℝ) (μr μb : Measure E) (h : E → ℝ) : ENNReal :=
  ENNReal.ofReal lr * ∫⁻ x, ENNReal.ofReal ((Lop h x - f x) ^ 2) ∂μr +
    ENNReal.ofReal lb * ∫⁻ x, ENNReal.ofReal ((Bop h x - g x) ^ 2) ∂μb

/-- Eqs. (2.2)–(2.3): the regularized empirical loss
`Loss_m(h; λ, λ^R) = Loss^{PINN}_m(h; λ) + λ_r^R R_r(h) + λ_b^R R_b(h)`, with the values
`R_r(h)`, `R_b(h)` of the regularization functionals given. -/
def lossEmp {E : Type*} (Lop Bop : (E → ℝ) → E → ℝ) (f g : E → ℝ) (lr lb lrR lbR Rr Rb : ℝ)
    {mr mb : ℕ} (xr : Fin mr → E) (xb : Fin mb → E) (h : E → ℝ) : ℝ :=
  pinnLossEmp Lop Bop f g lr lb xr xb h + lrR * Rr + lbR * Rb

/-- Eq. (3.3), case `d ≥ 2`: the Hölder regularized empirical loss
`Loss^{PINN}_m(h; λ) + λ_r^R [L[h]]²_{α;U} + λ_b^R [B[h]]²_{α;Γ}`, valued in `[0, ∞]`. -/
def holderRegLoss {E : Type*} [NormedAddCommGroup E] (α : ℝ) (U Gam : Set E)
    (Lop Bop : (E → ℝ) → E → ℝ) (f g : E → ℝ) (lr lb lrR lbR : ℝ) {mr mb : ℕ}
    (xr : Fin mr → E) (xb : Fin mb → E) (h : E → ℝ) : ENNReal :=
  ENNReal.ofReal (pinnLossEmp Lop Bop f g lr lb xr xb h) +
    ENNReal.ofReal lrR * holderConst α U (Lop h) ^ 2 + ENNReal.ofReal lbR * holderConst α Gam (Bop h) ^ 2

/-- Theorem 3.1 (`d ≥ 2`): `C_m = 3 max{κ_r √d^d m_r^{1/2}, κ_b √d^{d-1} m_b^{1/2}}` with
`κ_r = C_r / c_r`, `κ_b = C_b / c_b`. -/
def constCm (d : ℕ) (cr Cr cb Cb : ℝ) (mr mb : ℕ) : ℝ :=
  3 * max (Cr / cr * Real.sqrt d ^ d * Real.sqrt mr) (Cb / cb * Real.sqrt d ^ (d - 1) * Real.sqrt mb)

/-- Eq. (3.1): `λ̂^R_{r,m} = 3 λ_r √d^{2α} c_r^{-2α/d} m_r^{-α/d} / C_m`. -/
def lamHatR (d : ℕ) (α lr cr Cr cb Cb : ℝ) (mr mb : ℕ) : ℝ :=
  3 * lr * Real.sqrt d ^ (2 * α) * cr ^ (-(2 * α) / d) / constCm d cr Cr cb Cb mr mb *
    (mr : ℝ) ^ (-α / d)

/-- Eq. (3.1): `λ̂^R_{b,m} = 3 λ_b √d^{2α} c_b^{-2α/(d-1)} m_b^{-α/(d-1)} / C_m`. -/
def lamHatB (d : ℕ) (α lb cr Cr cb Cb : ℝ) (mr mb : ℕ) : ℝ :=
  3 * lb * Real.sqrt d ^ (2 * α) * cb ^ (-(2 * α) / ((d : ℝ) - 1)) / constCm d cr Cr cb Cb mr mb *
    (mb : ℝ) ^ (-α / ((d : ℝ) - 1))

/-- Eq. (3.2), along the sample sizes `m_r = m`, `m_b = mb m` (`m ≥ 1`): `λ^R_m ≥ λ̂^R_m`
entrywise and `‖λ^R_m‖_∞ = O(‖λ̂^R_m‖_∞)`. -/
def RegWeightCondition (d : ℕ) (α lr lb cr Cr cb Cb : ℝ) (mb : ℕ → ℕ) (lrR lbR : ℕ → ℝ) : Prop :=
  (∀ m : ℕ, 1 ≤ m → lamHatR d α lr cr Cr cb Cb m (mb m) ≤ lrR m ∧
      lamHatB d α lb cr Cr cb Cb m (mb m) ≤ lbR m) ∧
    ∃ K : ℝ, ∀ m : ℕ, 1 ≤ m → max (lrR m) (lbR m) ≤
      K * max (lamHatR d α lr cr Cr cb Cb m (mb m)) (lamHatB d α lb cr Cr cb Cb m (mb m))

/-- Section 2: for each `m ≥ 1`, `(XR m, XB m)` are `m` iid samples from `μ_r` and `mb m` iid
samples from `μ_b`, the two sets independent: their joint law is `μ_r^{⊗m} ⊗ μ_b^{⊗ mb m}`. -/
def IsIIDSampling {d : ℕ} {Smp : Type*} [MeasurableSpace Smp] (P : Measure Smp) (μr μb : Measure (Rd d))
    (mb : ℕ → ℕ) (XR : ∀ m : ℕ, Smp → Fin m → Rd d) (XB : ∀ m : ℕ, Smp → Fin (mb m) → Rd d) : Prop :=
  ∀ m : ℕ, 1 ≤ m → AEMeasurable (fun ω => (XR m ω, XB m ω)) P ∧
    P.map (fun ω => (XR m ω, XB m ω)) =
      (Measure.pi fun _ : Fin m => μr).prod (Measure.pi fun _ : Fin (mb m) => μb)

/-- Assumption 3.2, for classes `H m ω` that may depend on the samples `ω`: `0 < α ≤ 1`,
`f ∈ C^{0,α}(U)`, `g ∈ C^{0,α}(Γ)`; (1) every `h ∈ H_m` is a network (activation `σ`) in
`C^{k,α}(U) ∩ C^{0,α}(closure U)` with `L[h] ∈ C^{0,α}(U)`, `B[h] ∈ C^{0,α}(Γ)`; (2) `H_m` contains
`u*_m` with zero empirical PINN loss on the `m`-th samples; (3) `sup_m [L[u*_m]]_{α;U} < ∞` and
`sup_m [B[u*_m]]_{α;Γ} < ∞`. -/
def NetClassAssumption {d : ℕ} {Smp : Type*} (σ : ℝ → ℝ) (k : ℕ) (α : ℝ) (U Gam : Set (Rd d))
    (Lop Bop : (Rd d → ℝ) → Rd d → ℝ) (f g : Rd d → ℝ) (lr lb : ℝ) (mb : ℕ → ℕ)
    (XR : ∀ m : ℕ, Smp → Fin m → Rd d) (XB : ∀ m : ℕ, Smp → Fin (mb m) → Rd d)
    (H : ℕ → Smp → Set (Rd d → ℝ)) : Prop :=
  0 < α ∧ α ≤ 1 ∧ IsHolderCk 0 α U f ∧ IsHolderCk 0 α Gam g ∧
    (∀ m ω, ∀ h ∈ H m ω, IsNeuralNet σ d h ∧ IsHolderCk k α U h ∧
      IsHolderCk 0 α (closure U) h ∧ IsHolderCk 0 α U (Lop h) ∧ IsHolderCk 0 α Gam (Bop h)) ∧
    ∀ ω, ∃ us : ℕ → Rd d → ℝ,
      (∀ m : ℕ, 1 ≤ m → us m ∈ H m ω ∧ pinnLossEmp Lop Bop f g lr lb (XR m ω) (XB m ω) (us m) = 0) ∧
      (⨆ m : ℕ, ⨆ (_ : 1 ≤ m), holderConst α U (Lop (us m))) < ⊤ ∧
      (⨆ m : ℕ, ⨆ (_ : 1 ≤ m), holderConst α Gam (Bop (us m))) < ⊤

/-- Section 3.3: the partial derivative `D_i F(x)`. -/
def pd {d : ℕ} (i : Fin d) (F : Rd d → ℝ) (x : Rd d) : ℝ :=
  fderiv ℝ F x (EuclideanSpace.single i 1)

/-- Eq. (3.6): the divergence-form operator
`L[u] = ∑_i D_i(∑_j a^{ij} D_j u + b^i u) + ∑_i c^i D_i u + e u`
(the paper's zeroth-order coefficient `d(x)` is called `e` here). -/
def ellipticOp {d : ℕ} (a : Fin d → Fin d → Rd d → ℝ) (b c : Fin d → Rd d → ℝ) (e : Rd d → ℝ)
    (u : Rd d → ℝ) : Rd d → ℝ :=
  fun x => ∑ i, pd i (fun y => ∑ j, a i j y * pd j u y + b i y * u y) x +
    ∑ i, c i x * pd i u x + e x * u x

/-- Lemma D.1 and Assumption 3.4: `b̃^i = ∑_j D_j a^{ij} + b^i + c^i`. -/
def btilde {d : ℕ} (a : Fin d → Fin d → Rd d → ℝ) (b c : Fin d → Rd d → ℝ) (i : Fin d)
    (x : Rd d) : ℝ :=
  ∑ j, pd j (a i j) x + b i x + c i x

/-- Theorem 3.3: `c̃ = ∑_i D_i b^i + e`. -/
def ctilde {d : ℕ} (b : Fin d → Rd d → ℝ) (e : Rd d → ℝ) (x : Rd d) : ℝ :=
  ∑ i, pd i (b i) x + e x

/-- Section 2 and eq. (3.6): a classical solution of `L[u] = f` in `U`, `u = g` on `∂U`:
`u ∈ C²(U) ∩ C⁰(closure U)`. -/
def IsClassicalSol {d : ℕ} (U : Set (Rd d)) (a : Fin d → Fin d → Rd d → ℝ) (b c : Fin d → Rd d → ℝ)
    (e f g : Rd d → ℝ) (u : Rd d → ℝ) : Prop :=
  ContDiffOn ℝ 2 u U ∧ ContinuousOn u (closure U) ∧ (∀ x ∈ U, ellipticOp a b c e u x = f x) ∧
    ∀ x ∈ frontier U, u x = g x

/-- Assumption 3.3: `α ∈ (0,1)`; (1) `[a^{ij}]` is symmetric with smallest eigenvalue `≥ λ₀ > 0`
on `U`; (2) `c^i, e ∈ C^α(U)`; (3) `a^{ij}, b^i ∈ C^{1,α}(U)`, `f ∈ C^{0,α}(U)`,
`g ∈ C^{0,α}(∂U)`; (4) exterior sphere condition at every boundary point; (5) `Λ, v ≥ 0` with
`∑ |a^{ij}|² ≤ Λ` and `λ₀^{-2}(‖b‖² + ‖c‖²) + λ₀^{-1}|e| ≤ v²` on `U`. -/
def EllipticAssumption {d : ℕ} (α : ℝ) (U : Set (Rd d)) (a : Fin d → Fin d → Rd d → ℝ)
    (b c : Fin d → Rd d → ℝ) (e f g : Rd d → ℝ) (lam0 Lam v : ℝ) : Prop :=
  0 < α ∧ α < 1 ∧ 0 < lam0 ∧
    (∀ x ∈ U, ∀ ξ : Fin d → ℝ, lam0 * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a i j x * ξ i * ξ j) ∧
    (∀ x ∈ U, ∀ i j, a i j x = a j i x) ∧
    (∀ i, IsHolderCk 0 α U (c i)) ∧ IsHolderCk 0 α U e ∧
    (∀ i j, IsHolderCk 1 α U (a i j)) ∧ (∀ i, IsHolderCk 1 α U (b i)) ∧
    IsHolderCk 0 α U f ∧ IsHolderCk 0 α (frontier U) g ∧
    (∀ x₀ ∈ frontier U, ∃ y : Rd d, ∃ R > 0, Metric.closedBall y R ∩ closure U = {x₀}) ∧
    0 ≤ Lam ∧ 0 ≤ v ∧
    ∀ x ∈ U, ∑ i, ∑ j, a i j x ^ 2 ≤ Lam ∧
      lam0⁻¹ ^ 2 * (∑ i, b i x ^ 2 + ∑ i, c i x ^ 2) + lam0⁻¹ * |e x| ≤ v ^ 2

/-- Theorem 3.4: the squared `H¹(U)` distance `∫_U (|∇(u - w)|² + |u - w|²) dx` of two functions
that are `C¹` on `U` (for which the weak gradient is the classical one), valued in `[0, ∞]`. -/
def h1DistSq {d : ℕ} (U : Set (Rd d)) (u w : Rd d → ℝ) : ENNReal :=
  ∫⁻ x in U, ‖fderiv ℝ (u - w) x‖ₑ ^ 2 + ‖u x - w x‖ₑ ^ 2

end PINNConvergence


