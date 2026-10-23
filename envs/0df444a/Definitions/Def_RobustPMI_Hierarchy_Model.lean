-- Prove2me | Definitions.Def_RobustPMI_Hierarchy_Model
-- name    : RobustPMI_Hierarchy_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:17:28.122893+00:00
-- url     : https://prove2.me/theorems/e8144e1b-5597-4393-ad56-20d45210f7aa
-- title:
--   pp. 1–9, 16–20 — (RPMIO), SOS matrices, SOS-convexity, PSD-SOS-convexity, 𝒬^m_k(G), moment and localizing matrices, 𝓜^m_k(G), the hierarchy (4.4)–(4.5)
-- statement:
--   The objects of Guo and Wang's moment-SOS hierarchy for robust polynomial matrix inequality optimization.
--
--   **The problem (RPMIO).** Let $f\in\mathbb R[y]$ with $y=(y_1,\dots,y_\ell)$, let $\theta_1,\dots,\theta_s\in\mathbb R[y]$, let $G(x)$ be a $q\times q$ symmetric polynomial matrix in $x=(x_1,\dots,x_n)$, and let $P(y,x)$ be an $m\times m$ symmetric polynomial matrix in $(y,x)$. Put
--   $$\mathcal Y=\{y\in\mathbb R^\ell:\theta_1(y)\ge0,\dots,\theta_s(y)\ge0\},\qquad \mathcal X=\{x\in\mathbb R^n: G(x)\succeq0\},$$
--   $$f^\star=\inf_{y\in\mathcal Y} f(y)\quad\text{s.t.}\quad P(y,x)\succeq0\ \ \forall x\in\mathcal X .$$
--   A global minimizer is a feasible $y$ with $f(y)\le f(y')$ for every feasible $y'$.
--
--   **Sums of squares.** For a polynomial matrix $T$, $\deg(T)=\max_{i,j}\deg(T_{ij})$. A polynomial is SOS if it is a finite sum of squares; a symmetric polynomial matrix $\Sigma$ is an SOS matrix if $\Sigma=T^{\intercal}T$ for some $l\times q$ polynomial matrix $T$. A polynomial $h$ is **SOS-convex** if its Hessian $\nabla_{yy}h$ is an SOS matrix (Definition 2.2), and $Q(y)\in\mathbb S[y]^m$ is **PSD-SOS-convex** if for every $v\in\mathbb R^m$ there is a polynomial matrix $F_v$ with $\nabla_{yy}(v^{\intercal}Q(y)v)=F_v(y)^{\intercal}F_v(y)$ (Definition 2.4). For $A\in\mathbb R^{mq\times mq}$ and $B\in\mathbb R^{q\times q}$, $(A,B)_m=\operatorname{tr}_m(A^{\intercal}(I_m\otimes B))$, where $\operatorname{tr}_m(C)$ is the $m\times m$ matrix of traces of the $q\times q$ blocks of $C$. The truncated matrix quadratic module is
--   $$\mathcal Q^m_k(G)=\{\Sigma_0+(\Sigma_1,G)_m:\ \Sigma_0\in\mathbb S[x]^m,\ \Sigma_1\in\mathbb S[x]^{mq}\ \text{SOS matrices},\ \deg(\Sigma_0),\deg((\Sigma_1,G)_m)\le 2k\}.$$
--
--   **Moments.** For a sequence $S=(S_\alpha)$ of $m\times m$ matrices, the Riesz functional is $\mathscr L_S(F)=\sum_{\alpha\in\operatorname{supp}(F)}\operatorname{tr}(F_\alpha S_\alpha)$; the moment matrix $M_d(S)$ has $(\alpha,\beta)$ block $S_{\alpha+\beta}$ and the localizing matrix $M_d(GS)$ has $(\alpha,\beta)$ block $\sum_{\gamma\in\operatorname{supp}(G)}S_{\alpha+\beta+\gamma}\otimes G_\gamma$, for $|\alpha|,|\beta|\le d$ (Definition 2.12). With $d_G=\lceil\deg(G)/2\rceil$,
--   $$\mathcal M^m_k(G)=\{S=(S_\alpha)_{|\alpha|\le 2k}\subseteq\mathbb S^m:\ M_k(S)\succeq0,\ M_{k-d_G}(GS)\succeq0\},\qquad \mathcal M^m(G)=\bigcap_{k\ge d_G}\mathcal M^m_k(G).$$
--   For $m=1$ and $\Theta=\{\theta_1,\dots,\theta_s\}$, $\mathcal Q_k(\Theta)$ and $\mathcal M_k(\Theta)$ are these sets for the diagonal matrix $\operatorname{diag}(\theta_1,\dots,\theta_s)$ (Remark 2.16). A finitely atomic PSD matrix-valued measure on $\mathcal X$ is $\Phi=\sum_{i=1}^r W_i\delta_{x^{(i)}}$ with distinct $x^{(i)}\in\mathcal X$ and $W_i\succeq0$ (Definition 2.7); its moments are $S_\alpha=\sum_i (x^{(i)})^\alpha W_i$ and $\mathscr L_\Phi(P(y,x))=\sum_i\operatorname{tr}(P(y,x^{(i)})W_i)$.
--
--   **The hierarchy.** Write $P(y,x)=\sum_\beta P_\beta(x)y^\beta$, and set $\mathscr L_S(P(y,x))=\sum_\beta\mathscr L_S(P_\beta(x))y^\beta\in\mathbb R[y]$ and $\mathscr H_s(P(y,x))=\sum_\beta P_\beta(x)\,s_\beta\in\mathbb S[x]^m$, where $\mathscr H_s(h)=\sum_{\alpha}h_\alpha s_\alpha$. Let $k_y=\max\{\deg f,\deg\theta_j,\deg_y P_{ij}\}$ and $k_x=\max\{\deg_x P_{ij},\deg G\}$. For $k\ge\lceil k_x/2\rceil$,
--   $$f^{\mathrm{primal}}_k=\sup_{\rho,S}\ \rho\quad\text{s.t.}\quad f(y)-\rho-\mathscr L_S(P(y,x))\in\mathcal Q_{\lceil k_y/2\rceil}(\Theta),\ \rho\in\mathbb R,\ S\in\mathcal M^m_k(G),\tag{4.4}$$
--   $$f^{\mathrm{dual}}_k=\inf_s\ \mathscr H_s(f)\quad\text{s.t.}\quad s\in\mathcal M_{\lceil k_y/2\rceil}(\Theta),\ \mathscr H_s(1)=1,\ \mathscr H_s(P(y,x))\in\mathcal Q^m_k(G).\tag{4.5}$$
--   Finally $s_e=(s_{e_1},\dots,s_{e_\ell})$.
--
--   **Assumptions.** Assumption 1: $f,-\theta_1,\dots,-\theta_s$ are SOS-convex, $-P(y,x)$ is PSD-SOS-convex in $y$ for every $x\in\mathcal X$, and $\mathcal X$ is compact. Assumption 2: there are $r\in\mathbb R$ and an SOS matrix $\Sigma(x)\in\mathbb S[x]^q$ with $r^2-\|x\|^2-\langle\Sigma(x),G(x)\rangle$ SOS, where $\langle N_1,N_2\rangle=\operatorname{tr}(N_1^{\intercal}N_2)$. Assumption 3 (Slater): some $\bar y\in\mathcal Y$ has $\theta_i(\bar y)>0$ for all $i$ and $P(\bar y,x)\succ0$ for all $x\in\mathcal X$.
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** In $P$ the variables `Sum.inl j` are $y_j$ and `Sum.inr i` are $x_i$; $P_\beta(x)$ is read off through `MvPolynomial.sumAlgEquiv`. Moment sequences are total functions on all exponents; each object reads only the entries the paper's truncation has ($|\alpha|\le 2k$ for $\mathcal M^m_k(G)$, $|\alpha|\le 2\lceil k_y/2\rceil$ for (4.5)), so the extra entries are unconstrained and never read, and the optimal values are unchanged. Symmetry of $S_\alpha$ is required for $|\alpha|\le 2k$. $\lceil a/2\rceil$ is written `(a + 1) / 2` in $\mathbb N$, and $k-d_G$ is natural subtraction (the paper only uses $k\ge d_G$). The optimal values $f^{\mathrm{primal}}_k$, $f^{\mathrm{dual}}_k$ are `EReal` suprema and infima, so an infeasible or unbounded relaxation gets $\pm\infty$ rather than a junk $0$; $f^\star$ is a real infimum, attained under the paper's standing assumption that (RPMIO) has an optimizer, which every theorem carries as a hypothesis.
-- source:
--   Guo, Wang, A moment-SOS hierarchy for robust polynomial matrix inequality optimization with SOS-convexity, arXiv:2304.12628v5, pp. 1–2, 5–9, 16–20: (RPMIO), (1.1), (1.2), Assumption 1 (p. 2); §2.1 deg(T), SOS matrix (p. 5); Definitions 2.2, 2.4, (·,·)_m, Assumption 2 (p. 6); 𝒬^m_k(G), Definition 2.7 (p. 7); Riesz functional, Definition 2.12 (p. 8); d_G, 𝓜^m_k(G), 𝓜^m(G), Remark 2.16 (p. 9); 𝓛(P), 𝓗(P), Assumption 3 (pp. 16–17); k_y, k_x, (4.4), (4.5) (p. 19); s_e (p. 20)

import Mathlib

namespace RobustPMI.Hierarchy

open MvPolynomial Matrix

noncomputable section

/-! ## Polynomial matrices and sums of squares (§2.1, pp. 5–7) -/

section SOS

variable {σ ι κ : Type*}

/-- `deg(T) := max_{i,j} deg(T_ij)` for a polynomial matrix `T` (p. 5). -/
def degMat [Fintype ι] [Fintype κ] (T : Matrix ι κ (MvPolynomial σ ℝ)) : ℕ :=
  Finset.univ.sup fun p : ι × κ => (T p.1 p.2).totalDegree

/-- `supp(F)`: the exponents `α` such that `x^α` appears in some entry of the polynomial matrix
`F` (p. 8). -/
def suppMat {R : Type*} [CommSemiring R] [DecidableEq σ] [Fintype ι] [Fintype κ]
    (F : Matrix ι κ (MvPolynomial σ R)) : Finset (σ →₀ ℕ) :=
  Finset.univ.biUnion fun p : ι × κ => (F p.1 p.2).support

/-- The coefficient matrix `F_α` of `x^α` in the polynomial matrix `F` (p. 8). -/
def coeffMat {R : Type*} [CommSemiring R] (F : Matrix ι κ (MvPolynomial σ R)) (α : σ →₀ ℕ) :
    Matrix ι κ R :=
  F.map (coeff α)

/-- An SOS polynomial: `h = ∑_{i=1}^t h_i²` (p. 5). -/
def IsSOSPoly (h : MvPolynomial σ ℝ) : Prop :=
  ∃ (t : ℕ) (g : Fin t → MvPolynomial σ ℝ), h = ∑ i, g i ^ 2

/-- An SOS matrix: `Σ(x) = T(x)ᵀ T(x)` for some `l × q` polynomial matrix `T(x)` (p. 5). -/
def IsSOSMat [Fintype ι] (Sig : Matrix ι ι (MvPolynomial σ ℝ)) : Prop :=
  ∃ (l : ℕ) (T : Matrix (Fin l) ι (MvPolynomial σ ℝ)), Sig = Tᵀ * T

/-- The Hessian `∇_{yy} h` of a polynomial `h` (p. 5). -/
def hessian (h : MvPolynomial σ ℝ) : Matrix σ σ (MvPolynomial σ ℝ) :=
  Matrix.of fun i j => pderiv i (pderiv j h)

/-- Definition 2.2 (p. 6): `h` is SOS-convex if its Hessian is an SOS matrix. -/
def IsSOSConvex [Fintype σ] (h : MvPolynomial σ ℝ) : Prop :=
  IsSOSMat (hessian h)

/-- The polynomial `vᵀ Q(y) v` for a polynomial matrix `Q` and a real vector `v`. -/
def quadForm [Fintype ι] (Q : Matrix ι ι (MvPolynomial σ ℝ)) (v : ι → ℝ) : MvPolynomial σ ℝ :=
  ∑ i, ∑ j, C (v i) * Q i j * C (v j)

/-- Definition 2.4 (p. 6): `Q(y)` is PSD-SOS-convex if for every `v ∈ ℝ^m` there is a polynomial
matrix `F_v(y)` with `∇_{yy}(vᵀ Q(y) v) = F_v(y)ᵀ F_v(y)`. -/
def IsPSDSOSConvex [Fintype σ] [Fintype ι] (Q : Matrix ι ι (MvPolynomial σ ℝ)) : Prop :=
  ∀ v : ι → ℝ, ∃ (l : ℕ) (F : Matrix (Fin l) σ (MvPolynomial σ ℝ)),
    hessian (quadForm Q v) = Fᵀ * F

/-- `tr_m(C)`: the `m × m` matrix of the traces of the `q × q` blocks `C_{jk}` of an
`mq × mq` matrix `C`, rows and columns indexed by (block index, index inside the block) (p. 6). -/
def trBlocks {R : Type*} [AddCommMonoid R] [Fintype κ] (C : Matrix (ι × κ) (ι × κ) R) :
    Matrix ι ι R :=
  Matrix.of fun j k => ∑ a, C (j, a) (k, a)

/-- The bilinear map `(A, B)_m = tr_m(Aᵀ (I_m ⊗ B))` (p. 6). -/
def pairM {R : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix (ι × κ) (ι × κ) R) (B : Matrix κ κ R) : Matrix ι ι R :=
  trBlocks (Aᵀ * Matrix.kroneckerMap (· * ·) (1 : Matrix ι ι R) B)

/-- The inner product `⟨N₁, N₂⟩ = tr(N₁ᵀ N₂)` (p. 5). -/
def innerMat {R : Type*} [CommRing R] [Fintype κ] (N₁ N₂ : Matrix κ κ R) : R :=
  Matrix.trace (N₁ᵀ * N₂)

/-- The `k`-th truncated matrix quadratic module `𝒬^m_k(G)` (p. 7): the polynomial matrices
`Σ₀ + (Σ₁, G)_m` with `Σ₀` (`m × m`) and `Σ₁` (`mq × mq`) SOS matrices and
`deg(Σ₀), deg((Σ₁, G)_m) ≤ 2k`. -/
def QM [Fintype ι] [DecidableEq ι] [Fintype κ] (k : ℕ) (G : Matrix κ κ (MvPolynomial σ ℝ)) :
    Set (Matrix ι ι (MvPolynomial σ ℝ)) :=
  {F | ∃ (Sig0 : Matrix ι ι (MvPolynomial σ ℝ)) (Sig1 : Matrix (ι × κ) (ι × κ) (MvPolynomial σ ℝ)),
    IsSOSMat Sig0 ∧ IsSOSMat Sig1 ∧ degMat Sig0 ≤ 2 * k ∧ degMat (pairM Sig1 G) ≤ 2 * k ∧
      F = Sig0 + pairM Sig1 G}

end SOS

/-! ## Matrix-valued moment sequences (§2.3, pp. 8–9) -/

section Moments

variable {σ ι κ : Type*} [Fintype σ] [DecidableEq σ]

/-- `ℕⁿ_d = {α ∈ ℕⁿ : |α| ≤ d}` (p. 5), as a finite set of exponents. -/
def monos (d : ℕ) : Finset (σ →₀ ℕ) :=
  (Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ => d)).filter fun α => α.degree ≤ d

/-- A (matrix-valued) sequence `S = (S_α)_α`, `S_α ∈ ℝ^{m × m}`. Only finitely many entries are
read by each object below. -/
abbrev MatSeq (σ ι : Type*) := (σ →₀ ℕ) → Matrix ι ι ℝ

/-- The Riesz functional `𝓛_S(F) = ∑_{α ∈ supp(F)} tr(F_α S_α)` (p. 8). -/
def riesz [Fintype ι] (S : MatSeq σ ι) (F : Matrix ι ι (MvPolynomial σ ℝ)) : ℝ :=
  ∑ α ∈ suppMat F, Matrix.trace (coeffMat F α * S α)

/-- Definition 2.12 (p. 8): the `d`-th order moment matrix `M_d(S)`, with block rows and columns
indexed by `ℕⁿ_d` and `(α, β)`-th block `S_{α+β}`. -/
def momentMat (d : ℕ) (S : MatSeq σ ι) :
    Matrix ((monos (σ := σ) d) × ι) ((monos (σ := σ) d) × ι) ℝ :=
  Matrix.of fun p p' => S (p.1.1 + p'.1.1) p.2 p'.2

/-- Definition 2.12 (p. 8): the `d`-th order localizing matrix `M_d(GS)`, with block rows and
columns indexed by `ℕⁿ_d` and `(α, β)`-th block `∑_{γ ∈ supp(G)} S_{α+β+γ} ⊗ G_γ`. -/
def locMat [Fintype κ] (d : ℕ) (G : Matrix κ κ (MvPolynomial σ ℝ)) (S : MatSeq σ ι) :
    Matrix ((monos (σ := σ) d) × (ι × κ)) ((monos (σ := σ) d) × (ι × κ)) ℝ :=
  Matrix.of fun p p' =>
    ∑ γ ∈ suppMat G, S (p.1.1 + p'.1.1 + γ) p.2.1 p'.2.1 * coeff γ (G p.2.2 p'.2.2)

/-- `d_G := ⌈deg(G)/2⌉` (p. 9). -/
def dG [Fintype κ] (G : Matrix κ κ (MvPolynomial σ ℝ)) : ℕ :=
  (degMat G + 1) / 2

/-- `𝓜^m_k(G)` (p. 9): sequences `(S_α)_{α ∈ ℕⁿ_{2k}}` of symmetric matrices with
`M_k(S) ⪰ 0` and `M_{k - d_G}(GS) ⪰ 0`. Entries `S_α` with `|α| > 2k` are not constrained and
are not read. -/
def MM [Fintype ι] [Fintype κ] (k : ℕ) (G : Matrix κ κ (MvPolynomial σ ℝ)) : Set (MatSeq σ ι) :=
  {S | (∀ α : σ →₀ ℕ, α.degree ≤ 2 * k → (S α).IsSymm) ∧ (momentMat k S).PosSemidef ∧
    (locMat (k - dG G) G S).PosSemidef}

/-- `𝓜^m(G) := ⋂_{k ≥ d_G} 𝓜^m_k(G)` (p. 9). -/
def MMall [Fintype ι] [Fintype κ] (G : Matrix κ κ (MvPolynomial σ ℝ)) : Set (MatSeq σ ι) :=
  {S | ∀ k : ℕ, dG G ≤ k → S ∈ MM k G}

/-- A scalar sequence `s = (s_α)_α`, viewed as a sequence of `1 × 1` matrices (`m = 1`). -/
def scalarSeq (s : (σ →₀ ℕ) → ℝ) : MatSeq σ (Fin 1) :=
  fun α => Matrix.of fun _ _ => s α

/-- The linear functional `𝓗_s(h) = ∑_{α ∈ supp(h)} h_α s_α` (p. 19). -/
def Hs (s : (σ →₀ ℕ) → ℝ) (h : MvPolynomial σ ℝ) : ℝ :=
  ∑ α ∈ h.support, coeff α h * s α

/-- `s_e = (s_{e_1}, …, s_{e_ℓ})` (p. 20). -/
def sE (s : (σ →₀ ℕ) → ℝ) : σ → ℝ :=
  fun j => s (Finsupp.single j 1)

/-- Remark 2.16 (p. 9): `𝒬_k(Θ) = 𝒬^1_k(diag(θ₁, …, θ_s))`. -/
def QTheta {s : ℕ} (k : ℕ) (θ : Fin s → MvPolynomial σ ℝ) : Set (MvPolynomial σ ℝ) :=
  {h | (Matrix.of fun _ _ => h : Matrix (Fin 1) (Fin 1) (MvPolynomial σ ℝ)) ∈
    QM k (Matrix.diagonal θ)}

/-- Remark 2.16 (p. 9): `𝓜_k(Θ) = 𝓜^1_k(diag(θ₁, …, θ_s))`. -/
def MTheta {s : ℕ} (k : ℕ) (θ : Fin s → MvPolynomial σ ℝ) : Set ((σ →₀ ℕ) → ℝ) :=
  {v | scalarSeq v ∈ MM k (Matrix.diagonal θ)}

end Moments

/-! ## The problem (RPMIO) (pp. 1–2) and its data -/

section Problem

variable {ℓ n m q s : ℕ}

/-- `𝒴 := {y ∈ ℝ^ℓ : θ₁(y) ≥ 0, …, θ_s(y) ≥ 0}` (1.1), p. 2. -/
def Yset (θ : Fin s → MvPolynomial (Fin ℓ) ℝ) : Set (Fin ℓ → ℝ) :=
  {y | ∀ j, 0 ≤ eval y (θ j)}

/-- `𝒳 := {x ∈ ℝⁿ : G(x) ⪰ 0}` (1.2), p. 2. -/
def Xset (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) : Set (Fin n → ℝ) :=
  {x | (G.map (eval x)).PosSemidef}

/-- `P(y, x) ∈ ℝ^{m × m}`; in `P` the variables `Sum.inl j` are `y_j` and `Sum.inr i` are `x_i`. -/
def evalP (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ)) (y : Fin ℓ → ℝ)
    (x : Fin n → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  P.map (eval (Sum.elim y x))

/-- The feasible set of (RPMIO): `y ∈ 𝒴` with `P(y, x) ⪰ 0` for all `x ∈ 𝒳` (p. 1). -/
def Feasible (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) : Set (Fin ℓ → ℝ) :=
  {y | y ∈ Yset θ ∧ ∀ x ∈ Xset G, (evalP P y x).PosSemidef}

/-- The optimal value `f⋆` of (RPMIO) (p. 1), as a real infimum; it is attained under the
standing assumption of p. 2 that (RPMIO) has an optimizer. -/
def fstar (f : MvPolynomial (Fin ℓ) ℝ) (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) : ℝ :=
  sInf ((fun y => eval y f) '' Feasible θ P G)

/-- `y` is a global minimizer (optimal solution) of (RPMIO). -/
def IsGlobalMin (f : MvPolynomial (Fin ℓ) ℝ) (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) (y : Fin ℓ → ℝ) : Prop :=
  y ∈ Feasible θ P G ∧ ∀ y' ∈ Feasible θ P G, eval y f ≤ eval y' f

/-- `P(·, x) ∈ 𝕊[y]^m`: the polynomial matrix in `y` obtained by fixing `x`. -/
def Patx (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ)) (x : Fin n → ℝ) :
    Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ) ℝ) :=
  P.map (aeval (Sum.elim (X : Fin ℓ → MvPolynomial (Fin ℓ) ℝ) fun i => C (x i)))

/-- `P` regarded as a polynomial matrix in `y` with coefficients in `ℝ[x]`. -/
def Py (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ)) :
    Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ) (MvPolynomial (Fin n) ℝ)) :=
  P.map (sumAlgEquiv ℝ (Fin ℓ) (Fin n))

/-- `P_β(x) ∈ 𝕊[x]^m`, the coefficient matrix of `y^β` in `P(y, x) = ∑_β P_β(x) y^β` (p. 16). -/
def Pbeta (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ)) (β : Fin ℓ →₀ ℕ) :
    Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ) :=
  coeffMat (Py P) β

/-- `𝓛_S(P(y, x)) := ∑_β 𝓛_S(P_β(x)) y^β ∈ ℝ[y]` (p. 17). -/
def rieszP (S : MatSeq (Fin n) (Fin m))
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ)) : MvPolynomial (Fin ℓ) ℝ :=
  ∑ β ∈ suppMat (Py P), monomial β (riesz S (Pbeta P β))

/-- `𝓗_s(P(y, x)) := ∑_β P_β(x) 𝓗_s(y^β) = ∑_β s_β P_β(x) ∈ 𝕊[x]^m` (pp. 17, 19). -/
def HsP (v : (Fin ℓ →₀ ℕ) → ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ)) :
    Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ) :=
  ∑ β ∈ suppMat (Py P), v β • Pbeta P β

/-- `deg_y(p)`: the degree of a polynomial in `(y, x)` in the variables `y`. -/
def degY (p : MvPolynomial (Fin ℓ ⊕ Fin n) ℝ) : ℕ :=
  p.support.sup fun α => ∑ j, α (Sum.inl j)

/-- `deg_x(p)`: the degree of a polynomial in `(y, x)` in the variables `x`. -/
def degX (p : MvPolynomial (Fin ℓ ⊕ Fin n) ℝ) : ℕ :=
  p.support.sup fun α => ∑ i, α (Sum.inr i)

/-- `k_y := max {deg(f), deg(θ₁), …, deg(θ_s), deg_y(P_ij)}` (p. 19). -/
def ky (f : MvPolynomial (Fin ℓ) ℝ) (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ)) : ℕ :=
  max f.totalDegree (max (Finset.univ.sup fun j => (θ j).totalDegree)
    (Finset.univ.sup fun p : Fin m × Fin m => degY (P p.1 p.2)))

/-- `k_x := max {deg_x(P_ij), deg(G)}` (p. 19). -/
def kx (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) : ℕ :=
  max (Finset.univ.sup fun p : Fin m × Fin m => degX (P p.1 p.2)) (degMat G)

/-- The primal value (4.4) (p. 19): `f_k^primal := sup ρ` over `ρ ∈ ℝ`, `S ∈ 𝓜^m_k(G)` with
`f(y) − ρ − 𝓛_S(P(y, x)) ∈ 𝒬_{⌈k_y/2⌉}(Θ)`, in `EReal` (`⊥` if infeasible, `⊤` if unbounded). -/
def fprimal (f : MvPolynomial (Fin ℓ) ℝ) (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) (k : ℕ) : EReal :=
  sSup {r : EReal | ∃ (ρ : ℝ) (S : MatSeq (Fin n) (Fin m)), S ∈ MM k G ∧
    f - C ρ - rieszP S P ∈ QTheta ((ky f θ P + 1) / 2) θ ∧ r = (ρ : EReal)}

/-- Feasibility for the dual problem (4.5) (p. 19): `s ∈ 𝓜_{⌈k_y/2⌉}(Θ)`, `𝓗_s(1) = 1` and
`𝓗_s(P(y, x)) ∈ 𝒬^m_k(G)`. -/
def DualFeasible (f : MvPolynomial (Fin ℓ) ℝ) (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) (k : ℕ)
    (v : (Fin ℓ →₀ ℕ) → ℝ) : Prop :=
  v ∈ MTheta ((ky f θ P + 1) / 2) θ ∧ Hs v 1 = 1 ∧ HsP v P ∈ QM k G

/-- The dual value (4.5) (p. 19): `f_k^dual := inf 𝓗_s(f)` over dual-feasible `s`, in `EReal`
(`⊤` if infeasible). -/
def fdual (f : MvPolynomial (Fin ℓ) ℝ) (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) (k : ℕ) : EReal :=
  sInf {r : EReal | ∃ v, DualFeasible f θ P G k v ∧ r = (Hs v f : EReal)}

/-- `s` is a minimizer of (4.5) at relaxation order `k`. -/
def IsDualMinimizer (f : MvPolynomial (Fin ℓ) ℝ) (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) (k : ℕ)
    (v : (Fin ℓ →₀ ℕ) → ℝ) : Prop :=
  DualFeasible f θ P G k v ∧ ∀ v', DualFeasible f θ P G k v' → Hs v f ≤ Hs v' f

/-- Definition 2.7 (p. 7): a finitely atomic PSD matrix-valued measure
`Φ = ∑_{i=1}^r W_i δ_{x^{(i)}}` on `𝒳`, with distinct points `x^{(i)} ∈ 𝒳` and `W_i ⪰ 0`. -/
structure AtomicMeasure (m : ℕ) (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) where
  /-- number of atoms -/
  r : ℕ
  /-- the atoms `x^{(i)}` -/
  pts : Fin r → Fin n → ℝ
  /-- the weights `W_i` -/
  W : Fin r → Matrix (Fin m) (Fin m) ℝ
  inj : Function.Injective pts
  mem : ∀ i, pts i ∈ Xset G
  psd : ∀ i, (W i).PosSemidef

/-- The moments `S_α = ∫ x^α dΦ(x) = ∑_i (x^{(i)})^α W_i` of a finitely atomic measure ((2.5), p. 8). -/
def AtomicMeasure.moments {G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)}
    (μ : AtomicMeasure m G) : MatSeq (Fin n) (Fin m) :=
  fun α => ∑ i, eval (μ.pts i) (monomial α (1 : ℝ)) • μ.W i

/-- `𝓛_Φ(P(y, x))` evaluated at `y`: `∑_i tr(P(y, x^{(i)}) W_i)` ((2.2), p. 7; p. 20). -/
def AtomicMeasure.rieszP {G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)}
    (μ : AtomicMeasure m G) (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (y : Fin ℓ → ℝ) : ℝ :=
  ∑ i, Matrix.trace (evalP P y (μ.pts i) * μ.W i)

/-- Assumption 1 (p. 2): (i) `f, −θ₁, …, −θ_s` are SOS-convex; (ii) `−P(y, x)` is PSD-SOS-convex
in `y` for all `x ∈ 𝒳`; (iii) `𝒳` is compact. -/
def Assumption1 (f : MvPolynomial (Fin ℓ) ℝ) (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) : Prop :=
  IsSOSConvex f ∧ (∀ j, IsSOSConvex (-θ j)) ∧
    (∀ x ∈ Xset G, IsPSDSOSConvex (-(Patx P x))) ∧ IsCompact (Xset G)

/-- Assumption 2 (p. 6): there are `r ∈ ℝ` and an SOS matrix `Σ(x) ∈ 𝕊[x]^q` such that
`r² − ‖x‖² − ⟨Σ(x), G(x)⟩` is SOS. -/
def Assumption2 (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) : Prop :=
  ∃ (r : ℝ) (Sig : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)), IsSOSMat Sig ∧
    IsSOSPoly (C (r ^ 2) - ∑ i, X i ^ 2 - innerMat Sig G)

/-- Assumption 3 (p. 17, Slater): some `ȳ ∈ 𝒴` has `θ_i(ȳ) > 0` for all `i` and
`P(ȳ, x) ≻ 0` for all `x ∈ 𝒳`. -/
def Assumption3 (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) : Prop :=
  ∃ ybar ∈ Yset θ, (∀ j, 0 < eval ybar (θ j)) ∧ ∀ x ∈ Xset G, (evalP P ybar x).PosDef

end Problem

end

end RobustPMI.Hierarchy


