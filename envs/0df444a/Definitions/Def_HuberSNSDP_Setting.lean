-- Prove2me | Definitions.Def_HuberSNSDP_Setting
-- name    : HuberSNSDP_Setting
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:22:43.641294+00:00
-- url     : https://prove2.me/theorems/8c068dcb-2391-4430-a835-82041c540970
-- title:
--   §1–§3 — the SDP pair, KKT system, standing assumption, Huber smoothing $\Phi$, constraint nondegeneracy and SSOSC
-- statement:
--   This module fixes the objects of §1–§3 of the paper.
--
--   1. **The SDP pair** ((1)–(2), p.1). Data $C\in\mathbb S^n$, $b\in\mathbb R^m$, $A_1,\dots,A_m\in\mathbb S^n$; $\mathcal AX=(\langle A_1,X\rangle,\dots,\langle A_m,X\rangle)^T$ and $\mathcal A^*y=\sum_i y_iA_i$, with the trace inner product. The primal problem is $\min\{\langle C,X\rangle:\mathcal AX=b,\ X\in\mathbb S^n_+\}$.
--   2. **Standing assumption** (p.2). (1) has an optimal solution, and some $\tilde X\in\mathbb S^n_{++}$ has $\mathcal A\tilde X=b$ (Slater).
--   3. **KKT system** ((3)–(4), p.2). $(X,y,Z)$ is a KKT point if $\mathcal AX=b$, $\mathcal A^*y+Z=C$, $X,Z\in\mathbb S^n_+$ and $\langle X,Z\rangle=0$; $\mathcal M(\bar X)$ is the set of $(y,Z)$ making $(\bar X,y,Z)$ a KKT point, and the KKT map is
--   $$\mathcal F(X,y,Z)=\big(\mathcal AX-b;\ -\mathcal A^*y-Z+C;\ X-\Pi_{\mathbb S^n_+}(X-Z)\big).\qquad(5)$$
--   4. **Huber function and $\Phi$** ((12)–(13), p.9). For $\epsilon\neq0$, $h(\epsilon,t)=t-|\epsilon|/2$ if $t>|\epsilon|$, $t^2/(2|\epsilon|)$ if $0\le t\le|\epsilon|$, $0$ if $t<0$; $h(0,t)=\max\{0,t\}$. For $W=P\,\mathrm{diag}(d)P^T$, $\Phi(\epsilon,W)=P\,\mathrm{diag}(h(\epsilon,d_1),\dots,h(\epsilon,d_n))P^T$. $\Omega(\epsilon,d)$ has entries $(h(\epsilon,d_i)-h(\epsilon,d_j))/(d_i-d_j)$ for $d_i\neq d_j$ and $h'_2(\epsilon,d_i)$ otherwise, and $\mathcal D(\epsilon,d)=\mathrm{diag}(h'_1(\epsilon,d_i))$.
--   5. **Spectral decomposition** ((7), p.6). $W=PDP^T$, $P$ orthogonal, $d_1\ge\dots\ge d_n$; $\alpha,\beta,\gamma$ index the positive, zero and negative $d_i$.
--   6. **Lemma 4's block form** (p.11). For a pair $(V_{|\beta|},v)$, the matrix $P[\cdots]P^T+\frac{v\tau}{2}\sum_{i\in\alpha}p_ip_i^T$ of Lemma 4, the set of coupled pairs ($V_{|\beta|}\in\partial_B\Phi_{|\beta|}(0,0)$, $v\in\{-1,1\}$, $vV_{|\beta|}(1,0)\succeq0$), and the limit set $\{\lim_k\Omega(\epsilon^k,z^k):(\epsilon^k,z^k)\to(0,0),\ \epsilon^k\neq0,\ z^k_1\ge\dots\ge z^k_{|\beta|}\}$.
--   7. **Constraint nondegeneracy** ((9)–(10), p.8). Primal at $\bar X$: every $(u,V)\in\mathbb R^m\times\mathbb S^n$ equals $(\mathcal AH,H+L)$ with $H\in\mathbb S^n$, $L\in\mathrm{lin}(\mathcal T_{\mathbb S^n_+}(\bar X))$. Dual at $(\bar y,\bar Z)$: every $(V_1,V_2)$ equals $(\mathcal A^*u+H,H+L)$ with $L\in\mathrm{lin}(\mathcal T_{\mathbb S^n_+}(\bar Z))$.
--   8. **SSOSC** (Definition 3, p.8). For every $0\neq H\in\bigcap_{(y,Z)\in\mathcal M(\bar X)}\mathrm{app}(y,Z)$ there is $(y,Z)\in\mathcal M(\bar X)$ with $-\Gamma_{\bar X}(-Z,H)>0$, where $\Gamma_B(S,H)=2\langle S,HB^\dagger H\rangle$ (11) and $\mathrm{app}(y,Z)=\{B:\mathcal AB=0,\ P_\beta^TBP_\gamma=0,\ P_\gamma^TBP_\gamma=0\}$.
--
--   These are the objects on which the global and superlinear convergence theory of the squared smoothing Newton method is stated.
--
--   **Formalization Note** $\mathbb S^n$ is the published `SymMat (Fin n)` (Frobenius = trace inner product), $\Phi$ is the continuous functional calculus `cfc (huber ε)` (independent of the choice of $P$), and $\Phi$ is defined on every finite index type so that $\Phi_{|\beta|}$ is the same definition. $\Pi_{\mathbb S^n_+}$ in (5) is the published metric projector; the tangent cone is the published contingent cone and $\mathrm{lin}$ the published lineality space $\mathrm{span}(T\cap-T)$. In (10) the space of $\bar y$ is read as $\mathbb R^m$ (printed $\mathbb R^n$). In $\mathrm{app}(y,Z)$ the blocks $P_\beta,P_\gamma$ come from a spectral decomposition of $\bar X-Z$; these blocks are independent of the choice of $P$.
-- source:
--   Liang, Sun & Toh, A Squared Smoothing Newton Method for Semidefinite Programming, arXiv:2303.05825v4, (1)–(4), pp.1–2; (5), p.4; (6)–(7), p.6; Definition 2, (9)–(11), Definition 3, pp.7–8; (12)–(13) and Φ, p.9; Lemma 4, p.11

import Mathlib
import Definitions.Def_SunNLSDP_Equiv_Setting
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_RobinsonSR_Reduction_Setting

open scoped RealInnerProductSpace Topology
open Filter

namespace HuberSNSDP

/-! # The SDP pair, its KKT system, the Huber smoothing `Φ`, nondegeneracy and SSOSC

L. Liang, D. Sun and K.-C. Toh, *A Squared Smoothing Newton Method for Semidefinite
Programming*, arXiv:2303.05825v4: problems (1)–(2), the standing assumption, (3)–(4) (pp.1–2),
`F` (5) (p.4), (6)–(7) (p.6), Definition 2, (9)–(11), Definition 3 (pp.7–8), the Huber function
(12), `Φ`, `Ω(ε, d)`, `𝒟(ε, d)` (13) (p.9), Lemma 4's block form (p.11).

**Formalization Note.**
* `Sⁿ` is `SunNLSDP.Equiv.SymMat (Fin n)`: the symmetric matrices as a subspace of
  `EuclideanSpace ℝ (Fin n × Fin n)`, so its inner product is `∑ᵢⱼ AᵢⱼBᵢⱼ = tr(AB)`, the trace
  inner product, and its norm is the Frobenius norm. `Φ` is defined for every finite index type
  `ι` so that `Φ_{|β|}` (Lemma 4) is the same definition on `SymMat β`.
* `ℝᵐ` is `EuclideanSpace ℝ (Fin m)`; products are `WithLp 2` products, so every norm is the
  Euclidean norm of the paper.
* `Φ(ε, W) = P diag(h(ε, d₁), …, h(ε, dₙ)) Pᵀ` is the continuous functional calculus
  `cfc (huber ε) W` (independent of the choice of `P`); `huber ε` is continuous, so this is the
  paper's value. The pair `(ε, W)` is one point of `ℝ × Sⁿ = WithLp 2 (ℝ × SymMat ι)`.
* `Π_{Sⁿ₊}` in `F` (5) is the published metric projector `SunNLSDP.Equiv.metricProj` onto
  `psdCone`; the paper's identity `Φ(0, ·) = Π_{Sⁿ₊}` (p.9) is a fact, not a definition here.
* `T_{Sⁿ₊}(X)` is the published contingent cone `SunNLSDP.Equiv.tangentCone` (the usual tangent
  cone of the closed convex cone `Sⁿ₊`), and `lin(T)` is `RobinsonSR.Reduction.linealitySpace T`
  `= span(T ∩ −T)`, the largest subspace contained in the convex cone `T`. -/

noncomputable section

open SunNLSDP.Equiv

/-! ### The Huber function and the smoothing map `Φ` (p.9) -/

/-- The Huber smoothing function (12), p.9: for `ε ≠ 0`,
`h(ε, t) = t − |ε|/2` if `t > |ε|`, `t²/(2|ε|)` if `0 ≤ t ≤ |ε|`, `0` if `t < 0`;
and `h(0, t) = ρ(t) = max{0, t}`. -/
def huber (ε t : ℝ) : ℝ :=
  if ε = 0 then max t 0
  else if |ε| < t then t - |ε| / 2
  else if 0 ≤ t then t ^ 2 / (2 * |ε|)
  else 0

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `Φ(ε, W) := P diag(h(ε, d₁), …, h(ε, dₙ)) Pᵀ` (p.9), for the spectral decomposition
`W = P diag(d) Pᵀ`; as the continuous functional calculus of the continuous function `h(ε, ·)`. -/
def Phi (ε : ℝ) (W : SymMat ι) : SymMat ι :=
  SymMat.ofMat (cfc (huber ε) W.toMat)

/-- The space `ℝ × S^ι` of pairs `(ε, W)` (or directions `(τ, H)`), with the Euclidean norm
`‖(τ, H)‖² = τ² + ‖H‖_F²`. -/
abbrev RS (ι : Type) [Fintype ι] [DecidableEq ι] : Type :=
  WithLp 2 (ℝ × SymMat ι)

/-- The point `(ε, W) ∈ ℝ × S^ι`. -/
def rsPt (ε : ℝ) (W : SymMat ι) : RS ι := WithLp.toLp 2 (ε, W)

/-- `Φ` as a map on the single space `ℝ × S^ι`, `(ε, W) ↦ Φ(ε, W)`; its B-subdifferential and
Clarke Jacobian are those of `Φ` in the paper. -/
def PhiPair (p : RS ι) : SymMat ι :=
  Phi (WithLp.ofLp p).1 (WithLp.ofLp p).2

/-- The spectral decomposition (7), p.6: `W = P diag(d) Pᵀ` with `P` orthogonal and
`d₁ ≥ ⋯ ≥ dₙ`. -/
def IsSpectralDecomp {n : ℕ} (W : SymMat (Fin n)) (P : Matrix (Fin n) (Fin n) ℝ)
    (d : Fin n → ℝ) : Prop :=
  P ∈ Matrix.orthogonalGroup (Fin n) ℝ ∧ Antitone d ∧
    W.toMat = P * Matrix.diagonal d * P.transpose

/-- `Ω(ε, d)` (13), p.9: `[Ω(ε, d)]ᵢⱼ = (h(ε, dᵢ) − h(ε, dⱼ))/(dᵢ − dⱼ)` if `dᵢ ≠ dⱼ`, and
`h′₂(ε, dᵢ)` (the partial derivative in the second argument) if `dᵢ = dⱼ`. Used for `ε ≠ 0`. -/
def OmegaMat (ε : ℝ) (d : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j =>
    if d i ≠ d j then (huber ε (d i) - huber ε (d j)) / (d i - d j) else deriv (huber ε) (d i)

/-- The diagonal of `𝒟(ε, d) = diag(h′₁(ε, d₁), …, h′₁(ε, d_N))` (13), p.9, `h′₁` the partial
derivative in the first argument. Used for `ε ≠ 0`. -/
def Dvec (ε : ℝ) (d : ι → ℝ) : ι → ℝ :=
  fun i => deriv (fun e => huber e (d i)) ε

/-! ### Lemma 4 (p.11): the block form and the sets of pairs `(V_{|β|}, v)` -/

/-- The right-hand side of Lemma 4, p.11 (with the leading `P` of (16)):
`P [ H̃_αα, H̃_αβ, [Ω₀(d)]_αγ ∘ H̃_αγ ; H̃_αβᵀ, V_{|β|}(τ, H̃_ββ), 0 ; H̃_αγᵀ ∘ [Ω₀(d)]_αγᵀ, 0, 0 ] Pᵀ
 + (vτ/2) ∑_{i∈α} pᵢpᵢᵀ`, with `H̃ = PᵀHP`, `pᵢ` the `i`-th column of `P`, and the block matrix
the published `blockForm21 d H̃ (V_{|β|}(τ, H̃_ββ))` (`Ω₀ = Umat`). -/
def lemma4Block {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ)
    (Vb : RS (betaIdx d) →L[ℝ] SymMat (betaIdx d)) (v : ℝ) (q : RS (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  P * blockForm21 d (P.transpose * (WithLp.ofLp q).2.toMat * P)
      (Vb (rsPt (WithLp.ofLp q).1
        (SymMat.ofMat ((P.transpose * (WithLp.ofLp q).2.toMat * P).submatrix
          (fun i : betaIdx d => (i : Fin n)) (fun i : betaIdx d => (i : Fin n)))))).toMat *
      P.transpose +
    (v * (WithLp.ofLp q).1 / 2) •
      ∑ i ∈ Finset.univ.filter (fun i => 0 < d i),
        Matrix.vecMulVec (fun k => P k i) (fun k => P k i)

/-- The coupled pairs of Lemma 4 (corrected): `V_{|β|} ∈ ∂_BΦ_{|β|}(0, 0)`, `v ∈ {−1, 1}`, and
`v · V_{|β|}(1, 0) ⪰ 0` (the sign of `v` is tied to the sign of the `τ`-part of `V_{|β|}`). -/
def coupledPairs {n : ℕ} (d : Fin n → ℝ) :
    Set ((RS (betaIdx d) →L[ℝ] SymMat (betaIdx d)) × ℝ) :=
  {q | q.1 ∈ NonsmoothNewton.Shared.bJac (PhiPair (ι := betaIdx d)) (rsPt 0 0) ∧
    (q.2 = 1 ∨ q.2 = -1) ∧ q.2 • q.1 (rsPt 1 0) ∈ psdCone (betaIdx d)}

/-- The limit set of Lemma 4, p.11: `{Ω ∈ S^{|β|} : Ω = lim_k Ω(εᵏ, zᵏ), (εᵏ, zᵏ) → (0, 0),
εᵏ ≠ 0, z₁ᵏ ≥ ⋯ ≥ z_{|β|}ᵏ}` (a limit of symmetric matrices is symmetric). -/
def OmegaLimSet {n : ℕ} (d : Fin n → ℝ) : Set (Matrix (betaIdx d) (betaIdx d) ℝ) :=
  {Ω | ∃ (e : ℕ → ℝ) (z : ℕ → betaIdx d → ℝ), Tendsto e atTop (𝓝 0) ∧
    Tendsto z atTop (𝓝 0) ∧ (∀ k, e k ≠ 0) ∧ (∀ k, Antitone (z k)) ∧
    Tendsto (fun k => OmegaMat (e k) (z k)) atTop (𝓝 Ω)}

/-- `lin(T_{Sⁿ₊}(X))`, the lineality space of the tangent cone of `Sⁿ₊` at `X` (p.7). -/
def linT {n : ℕ} (X : SymMat (Fin n)) : Submodule ℝ (SymMat (Fin n)) :=
  RobinsonSR.Reduction.linealitySpace (SunNLSDP.Equiv.tangentCone (psdCone (Fin n)) X)

/-! ### The SDP pair (1)–(2), the KKT system (3)–(4), the standing assumption (pp.1–2) -/

/-- The data `C ∈ Sⁿ`, `b ∈ ℝᵐ`, `A₁, …, Aₘ ∈ Sⁿ` of (1), p.1. -/
structure SDPData (n m : ℕ) where
  /-- the matrices `Aᵢ` defining `𝒜X = (⟨A₁, X⟩, …, ⟨Aₘ, X⟩)ᵀ` -/
  A : Fin m → SymMat (Fin n)
  /-- the right-hand side `b` -/
  b : EuclideanSpace ℝ (Fin m)
  /-- the cost matrix `C` -/
  C : SymMat (Fin n)

namespace SDPData

variable {n m : ℕ} (D : SDPData n m)

/-- `𝒜X := (⟨A₁, X⟩, …, ⟨Aₘ, X⟩)ᵀ` (p.1), trace inner product. -/
def opA (X : SymMat (Fin n)) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun i => ⟪D.A i, X⟫)

/-- The adjoint `𝒜*y := ∑ᵢ yᵢAᵢ` (p.1). -/
def opAadj (y : EuclideanSpace ℝ (Fin m)) : SymMat (Fin n) :=
  ∑ i, y i • D.A i

/-- Feasibility for the primal problem (1): `𝒜X = b`, `X ∈ Sⁿ₊`. -/
def PrimalFeasible (X : SymMat (Fin n)) : Prop :=
  D.opA X = D.b ∧ X ∈ psdCone (Fin n)

/-- `X` is an optimal solution of (1): feasible, and `⟨C, X⟩ ≤ ⟨C, X'⟩` for every feasible `X'`. -/
def PrimalOptimal (X : SymMat (Fin n)) : Prop :=
  D.PrimalFeasible X ∧ ∀ X', D.PrimalFeasible X' → ⟪D.C, X⟫ ≤ ⟪D.C, X'⟫

/-- The standing assumption of the paper (p.2): (1) admits an optimal solution, and Slater's
condition holds, i.e. some `X̃ ∈ Sⁿ₊₊` (positive definite) has `𝒜X̃ = b`. -/
def Standing : Prop :=
  (∃ X, D.PrimalOptimal X) ∧ ∃ Xt : SymMat (Fin n), Xt.toMat.PosDef ∧ D.opA Xt = D.b

/-- The KKT conditions (3), p.2: `𝒜X = b`, `𝒜*y + Z = C`, `X, Z ∈ Sⁿ₊`, `⟨X, Z⟩ = 0`. -/
def KKT (X : SymMat (Fin n)) (y : EuclideanSpace ℝ (Fin m)) (Z : SymMat (Fin n)) : Prop :=
  D.opA X = D.b ∧ D.opAadj y + Z = D.C ∧ X ∈ psdCone (Fin n) ∧ Z ∈ psdCone (Fin n) ∧
    ⟪X, Z⟫ = 0

/-- The multiplier set `M(X̄) := {(y, Z) ∈ ℝᵐ × Sⁿ : (X̄, y, Z) is a KKT point}` (4), p.2. -/
def mult (Xbar : SymMat (Fin n)) : Set (EuclideanSpace ℝ (Fin m) × SymMat (Fin n)) :=
  {p | D.KKT Xbar p.1 p.2}

/-! ### Constraint nondegeneracy (9)–(10) and SSOSC (Definition 3), pp.7–8 -/

/-- Primal constraint nondegeneracy (9), p.8, at `X̄`:
`(𝒜; ℐ) Sⁿ + ({0}; lin(T_{Sⁿ₊}(X̄))) = (ℝᵐ; Sⁿ)`, i.e. every `(u, V) ∈ ℝᵐ × Sⁿ` is
`(𝒜H, H + L)` for some `H ∈ Sⁿ` and `L ∈ lin(T_{Sⁿ₊}(X̄))`. -/
def PrimalNondeg (Xbar : SymMat (Fin n)) : Prop :=
  ∀ (u : EuclideanSpace ℝ (Fin m)) (V : SymMat (Fin n)),
    ∃ H : SymMat (Fin n), ∃ L ∈ linT Xbar, D.opA H = u ∧ H + L = V

/-- Dual constraint nondegeneracy (10), p.8, at `(ȳ, Z̄)`:
`(𝒜*, ℐ; 0, ℐ)(ℝᵐ; Sⁿ) + ({0}; lin(T_{Sⁿ₊}(Z̄))) = (Sⁿ; Sⁿ)`, i.e. every `(V₁, V₂)` is
`(𝒜*u + H, H + L)` for some `u ∈ ℝᵐ`, `H ∈ Sⁿ`, `L ∈ lin(T_{Sⁿ₊}(Z̄))`. The condition involves `Z̄`
only. -/
def DualNondeg (Zbar : SymMat (Fin n)) : Prop :=
  ∀ V₁ V₂ : SymMat (Fin n), ∃ (u : EuclideanSpace ℝ (Fin m)) (H : SymMat (Fin n)),
    ∃ L ∈ linT Zbar, D.opAadj u + H = V₁ ∧ H + L = V₂

/-- `app(y, Z) := {B ∈ Sⁿ : 𝒜B = 0, P_βᵀBP_γ = 0, P_γᵀBP_γ = 0}` (Definition 3, p.8), where
`P = (P_α P_β P_γ)` comes from a spectral decomposition (7) of `X̄ − Z`: the entries `(i, j)` of
`PᵀBP` with `dᵢ ≤ 0` (`i ∈ β ∪ γ`) and `dⱼ < 0` (`j ∈ γ`) vanish. These blocks do not depend on
the choice of `P` (they are `Q_β B Q_γ`, `Q_γ B Q_γ` for the eigenprojections), and every symmetric
matrix has a spectral decomposition. -/
def app (Xbar Z : SymMat (Fin n)) : Set (SymMat (Fin n)) :=
  {B | D.opA B = 0 ∧ ∀ (P : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ),
    IsSpectralDecomp (Xbar - Z) P d →
      ∀ i j, d i ≤ 0 → d j < 0 → (P.transpose * B.toMat * P) i j = 0}

/-- The strong second-order sufficient condition, Definition 3, p.8, at `X̄`:
`sup_{(y,Z)∈M(X̄)} {−Γ_X̄(−Z, H)} > 0` for every `0 ≠ H ∈ ⋂_{(y,Z)∈M(X̄)} app(y, Z)`, with
`Γ_B(S, H) = 2⟨S, HB†H⟩` (11) the published `upsilon B S H`. A supremum of reals exceeds `0`
exactly when some element does. -/
def SSOSC (Xbar : SymMat (Fin n)) : Prop :=
  ∀ H : SymMat (Fin n), H ≠ 0 → (∀ p ∈ D.mult Xbar, H ∈ D.app Xbar p.2) →
    ∃ p ∈ D.mult Xbar, 0 < -upsilon Xbar (-p.2) H

end SDPData

/-! ### The spaces `𝕏 = Sⁿ × ℝᵐ × Sⁿ`, `ℝ × 𝕏`, and the KKT map `F` (5), p.4 -/

/-- `𝕏 := Sⁿ × ℝᵐ × Sⁿ` (p.12), with `‖(X, y, Z)‖² = ‖X‖_F² + ‖y‖² + ‖Z‖_F²`. -/
abbrev XSpace (n m : ℕ) : Type :=
  WithLp 2 (SymMat (Fin n) × WithLp 2 (EuclideanSpace ℝ (Fin m) × SymMat (Fin n)))

/-- `ℝ × 𝕏`, the space of the iterates `(ε, X, y, Z)`, with the Euclidean norm. -/
abbrev ISpace (n m : ℕ) : Type := WithLp 2 (ℝ × XSpace n m)

/-- `ℝᵐ × Sⁿ × Sⁿ`, the codomain of `F` (5) and `ℰ` (18), with the Euclidean norm. -/
abbrev ESpace (n m : ℕ) : Type :=
  WithLp 2 (EuclideanSpace ℝ (Fin m) × WithLp 2 (SymMat (Fin n) × SymMat (Fin n)))

/-- `ℝ × ℝᵐ × Sⁿ × Sⁿ`, the codomain of `ℰ̂` (19), with the Euclidean norm. -/
abbrev EhatSpace (n m : ℕ) : Type := WithLp 2 (ℝ × ESpace n m)

variable {n m : ℕ}

/-- The point `(X, y, Z) ∈ 𝕏`. -/
def xPt (X : SymMat (Fin n)) (y : EuclideanSpace ℝ (Fin m)) (Z : SymMat (Fin n)) : XSpace n m :=
  WithLp.toLp 2 (X, WithLp.toLp 2 (y, Z))

/-- The `X`-component of a point of `𝕏`. -/
def xX (x : XSpace n m) : SymMat (Fin n) := (WithLp.ofLp x).1
/-- The `y`-component of a point of `𝕏`. -/
def xy (x : XSpace n m) : EuclideanSpace ℝ (Fin m) := (WithLp.ofLp (WithLp.ofLp x).2).1
/-- The `Z`-component of a point of `𝕏`. -/
def xZ (x : XSpace n m) : SymMat (Fin n) := (WithLp.ofLp (WithLp.ofLp x).2).2

/-- The point `(ε, X, y, Z) ∈ ℝ × 𝕏`. -/
def wPt (ε : ℝ) (x : XSpace n m) : ISpace n m := WithLp.toLp 2 (ε, x)

/-- The `ε`-component of `w = (ε, X, y, Z)`. -/
def epsOf (w : ISpace n m) : ℝ := (WithLp.ofLp w).1
/-- The `(X, y, Z)`-component of `w = (ε, X, y, Z)`. -/
def xOf (w : ISpace n m) : XSpace n m := (WithLp.ofLp w).2
/-- The `X`-component of `w = (ε, X, y, Z)`. -/
def XOf (w : ISpace n m) : SymMat (Fin n) := xX (xOf w)
/-- The `y`-component of `w = (ε, X, y, Z)`. -/
def yOf (w : ISpace n m) : EuclideanSpace ℝ (Fin m) := xy (xOf w)
/-- The `Z`-component of `w = (ε, X, y, Z)`. -/
def ZOf (w : ISpace n m) : SymMat (Fin n) := xZ (xOf w)

/-- The point `(u, V₁, V₂) ∈ ℝᵐ × Sⁿ × Sⁿ`. -/
def ePt (u : EuclideanSpace ℝ (Fin m)) (V₁ V₂ : SymMat (Fin n)) : ESpace n m :=
  WithLp.toLp 2 (u, WithLp.toLp 2 (V₁, V₂))

namespace SDPData

variable (D : SDPData n m)

/-- The KKT map `F(X, y, Z) := (𝒜X − b; −𝒜*y − Z + C; X − Π_{Sⁿ₊}(X − Z))` (5), p.4. -/
def Fmap (x : XSpace n m) : ESpace n m :=
  ePt (D.opA (xX x) - D.b) (-D.opAadj (xy x) - xZ x + D.C)
    (xX x - metricProj (psdCone (Fin n)) (xX x - xZ x))

/-- The solution set of the KKT system (3) (p.2, Theorem 2), as a subset of `𝕏`. -/
def KKTSet : Set (XSpace n m) :=
  {x | D.KKT (xX x) (xy x) (xZ x)}

end SDPData

end

end HuberSNSDP


