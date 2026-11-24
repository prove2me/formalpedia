-- Prove2me | Definitions.Def_RobustPMI_Hierarchy_Supplement_Model
-- name    : RobustPMI_Hierarchy_Supplement_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T01:41:17.095556+00:00
-- url     : https://prove2.me/theorems/55664bea-51fc-4aa4-ab5f-90a880ec54f6
-- title:
--   pp. 6–7, 10, 18–29 — PSD matrix-valued measures, conic pair (4.2)–(4.3), FEC (4.8), Assumptions 4–5, (RPSDP), eigenvalue relaxations, hierarchy (5.1)–(5.2)
-- statement:
--   Objects used by the companion theorems of the paper, on top of the published definitions of the mission (polynomial matrices, $\mathcal Q^m_k(G)$, moment and localizing matrices $M_d(S)$, $M_d(GS)$, $\mathcal M^m_k(G)$, the hierarchy (4.4)–(4.5), finitely atomic measures). Throughout, $\mathcal X=\{x\in\mathbb R^n: G(x)\succeq0\}$ and $\mathcal Y=\{y\in\mathbb R^\ell:\theta_j(y)\ge0\}$.
--
--   1. **Flat extensions.** A finitely atomic measure $\Phi=\sum_i W_i\delta_{x^{(i)}}$ on $\mathcal X$ *represents $S$ up to order $2d$* if $S_\alpha=\sum_i (x^{(i)})^\alpha W_i$ for all $|\alpha|\le 2d$. The flat extension condition (4.8) at order $t$ is $\lceil\kappa/2\rceil\le t\le k$ and $\operatorname{rank}M_t(S)=\operatorname{rank}M_{t-d_G}(S)$.
--   2. **PSD matrix-valued measures** (Definition 2.6). $\Phi=[\phi_{ij}]$ with finite signed Borel measures $\phi_{ij}=\phi_{ji}$ vanishing outside $\mathcal X$ and $v^\top\Phi(A)v\ge0$ for all Borel $A$ and $v\in\mathbb R^m$; $\mathscr L_\Phi(F)=\sum_{i,j}\int F_{ij}\,d\phi_{ij}$.
--   3. **The conic pair (4.2)–(4.3).**
--   $$\tilde f=\sup_{\rho,\Phi}\{\rho:\ f(y)-\rho-\mathscr L_\Phi(P(y,x))\ge0\ \forall y\in\mathcal Y\},\qquad \hat f=\inf_\mu\Big\{\int f\,d\mu:\ \mu\in\mathfrak m_+(\mathcal Y),\ \mu(\mathbb R^\ell)=1,\ \textstyle\sum_\beta P_\beta(x)\int y^\beta d\mu\succeq0\ \forall x\in\mathcal X\Big\}.$$
--   4. **Optimal solutions of (4.4)**, Assumption 4 ((i) $\theta_1=b^2-\|y\|^2$, $b\ne0$; (ii) $\mathcal X$ has nonempty interior) and the interior $\mathcal Q^\circ_k(\Theta)$ of $\mathcal Q_k(\Theta)$ in $\mathbb R[y]_{2k}$.
--   5. **(RPSDP)** $\tau^\star=\inf\{c^\top y:\sum_i P_i(x)y_i-P_0(x)\succeq0\ \forall x\in\mathcal X\}$ and its relaxations
--   $$\tau_k^{\mathrm{primal}}=\sup_{S\in\mathcal M^m_k(G)}\{\mathscr L_S(P_0):\mathscr L_S(P_i)=c_i\},\qquad \tau_k^{\mathrm{dual}}=\inf_y\Big\{c^\top y:\sum_iP_iy_i-P_0\in\mathcal Q^m_k(G)\Big\}.$$
--   6. **Smallest eigenvalue** $\lambda^\star=\inf_{x\in\mathcal X}\lambda_{\min}(F(x))$ and its relaxations $\lambda_k^{\mathrm{primal}}=\inf\{\mathscr L_S(F):S\in\mathcal M^m_k(G),\mathscr L_S(I_m)=1\}$, $\lambda_k^{\mathrm{dual}}=\sup\{\lambda:F-\lambda I_m\in\mathcal Q^m_k(G)\}$.
--   7. **The convex setting of §5.** PSD-convexity (Definition 2.3), Assumption 5, the hierarchy (5.1)–(5.2) with $\mathcal Q_k(\Theta)$ and $\mathcal M_k(\Theta)$, $d_\Theta=\max_j\lceil\deg\theta_j/2\rceil$, finitely atomic probability measures on $\mathcal Y$ and representing probability measures.
--
--   These are the objects in which Theorems 3.2, 4.3, 4.11, 4.14, 4.17, 4.18, 4.20, 4.21, 5.2, 5.4, 5.7 and Lemmas 4.12, 5.1 are stated.
--
--   **Formalization Note** All optimal values are `EReal` suprema/infima ($\bot$/$\top$ for infeasible problems). Signed-measure integrals use the Jordan decomposition, and every polynomial is required to be integrable against $|\phi_{ij}|$ and against $\mu$, so that $\mathscr L_\Phi$ and $\mathscr H_\mu$ are defined on all polynomials, as the paper presupposes (p. 18). $\lambda_{\min}$ is the minimum of the Rayleigh quotient $v^\top Av$ over unit vectors, which is the smallest eigenvalue of a symmetric matrix. $k_x$ for (RPSDP) is $\max(\deg P_0,\dots,\deg P_\ell,\deg G)$. The interior in Lemma 4.12 is taken in the coefficient space $\mathbb R^{\mathbb N^\ell_{2k}}$ of $\mathbb R[y]_{2k}$.
-- source:
--   Guo, Wang, A moment-SOS hierarchy for robust polynomial matrix inequality optimization with SOS-convexity, arXiv:2304.12628v5, pp. 6–7, 10, 18–29, Definitions 2.3, 2.6, 2.8, (4.2), (4.3), (4.8), Assumptions 4, 5, (RPSDP), (4.14)–(4.19), (5.1)–(5.4)

import Mathlib
import Definitions.Def_RobustPMI_Hierarchy_Model

namespace RobustPMI.Hierarchy.Supplement

open MvPolynomial Matrix MeasureTheory

noncomputable section

/-! ## Flat-extension data (§3.1, p. 10; (4.8), p. 21) -/

section Flat

variable {n m q : ℕ}

/-- `Φ` represents the truncated sequence `S` up to order `2d`: `S_α = ∑_i (x^{(i)})^α W_i` for
every `|α| ≤ 2d` (Definition 2.11, p. 8, restricted to `ℕⁿ_{2d}`). -/
def Represents {G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)} (μ : AtomicMeasure m G)
    (d : ℕ) (S : MatSeq (Fin n) (Fin m)) : Prop :=
  ∀ α ∈ monos (σ := Fin n) (2 * d), μ.moments α = S α

/-- The flat extension condition (4.8) (p. 21) at the order `t`, for a matrix sequence `S`, the
lower order bound `κ` (`κ = k_x` in (4.8), (5.3)) and the relaxation order `k`:
`⌈κ/2⌉ ≤ t ≤ k` and `rank M_t(S) = rank M_{t-d_G}(S)`. -/
def FECAt (κ : ℕ) (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) (k t : ℕ)
    (S : MatSeq (Fin n) (Fin m)) : Prop :=
  (κ + 1) / 2 ≤ t ∧ t ≤ k ∧ (momentMat t S).rank = (momentMat (t - dG G) S).rank

/-- `W = ∑_{l=1}^{m'} v^{(l)} (v^{(l)})ᵀ`: a decomposition of a PSD matrix into rank-one terms
(Theorem 4.11 (iv), p. 21). -/
def IsRankOneDecomp {m' : ℕ} (W : Matrix (Fin m) (Fin m) ℝ) (v : Fin m' → Fin m → ℝ) : Prop :=
  W = ∑ l, Matrix.vecMulVec (v l) (v l)

end Flat

/-! ## PSD matrix-valued measures and the conic pair (4.2)–(4.3) (pp. 7, 18) -/

section Conic

variable {ℓ n m q s : ℕ}

/-- The integral `∫ g dϕ` of a real function against a finite signed Borel measure `ϕ`, through its
Jordan decomposition `ϕ = ϕ⁺ − ϕ⁻`. -/
def sIntegral {α : Type*} [MeasurableSpace α] (ϕ : SignedMeasure α) (g : α → ℝ) : ℝ :=
  (∫ x, g x ∂ϕ.toJordanDecomposition.posPart) - ∫ x, g x ∂ϕ.toJordanDecomposition.negPart

/-- Definition 2.6 (p. 7): an element of `𝔐^m_+(𝒳)`, an `m × m` symmetric PSD matrix-valued
measure on `𝒳 = {x : G(x) ⪰ 0}`: every entry `ϕ_ij` is a finite signed Borel measure on `ℝⁿ`
vanishing outside `𝒳`, `ϕ_ij = ϕ_ji`, and `vᵀ Φ(A) v ≥ 0` for every Borel `A` and `v ∈ ℝ^m`.
Every polynomial is integrable against every `|ϕ_ij|`, so that `𝓛_Φ` is defined on all of
`𝕊[x]^m` (Definition 2.8, p. 7). -/
structure PSDMatMeasure (m : ℕ) (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) where
  /-- the entries `ϕ_ij` -/
  φ : Fin m → Fin m → SignedMeasure (Fin n → ℝ)
  symm : ∀ i j, φ i j = φ j i
  supp : ∀ i j (A : Set (Fin n → ℝ)), MeasurableSet A → A ⊆ (Xset G)ᶜ → φ i j A = 0
  psd : ∀ A : Set (Fin n → ℝ), MeasurableSet A → (Matrix.of fun i j => φ i j A).PosSemidef
  integrable : ∀ i j (p : MvPolynomial (Fin n) ℝ),
    Integrable (fun x => eval x p) (φ i j).totalVariation

/-- The moment sequence `S_α = ∫ x^α dΦ(x)` of a PSD matrix-valued measure, so that
`𝓛_Φ(F) = 𝓛_S(F)` and `𝓛_Φ(P(y, x)) = 𝓛_S(P(y, x))` (p. 8, p. 18). -/
def PSDMatMeasure.moments {G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)}
    (Φ : PSDMatMeasure m G) : MatSeq (Fin n) (Fin m) :=
  fun α => Matrix.of fun i j => sIntegral (Φ.φ i j) fun x => eval x (monomial α (1 : ℝ))

/-- The moment vector `(∫ y^β dµ)_β` of a measure `µ` on `ℝ^ℓ`. -/
def measMoments (μ : Measure (Fin ℓ → ℝ)) : (Fin ℓ →₀ ℕ) → ℝ :=
  fun β => ∫ y, eval y (monomial β (1 : ℝ)) ∂μ

/-- The value `f̃` of the conic program (4.2) (p. 18):
`sup ρ` s.t. `f(y) − ρ − 𝓛_Φ(P(y, x)) ∈ 𝒫(𝒴)`, `ρ ∈ ℝ`, `Φ ∈ 𝔐^m_+(𝒳)`
(`𝒫(𝒴)`: polynomials nonnegative on `𝒴`). `⊥` if infeasible. -/
def ftilde (f : MvPolynomial (Fin ℓ) ℝ) (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) : EReal :=
  sSup {r : EReal | ∃ (ρ : ℝ) (Φ : PSDMatMeasure m G),
    (∀ y ∈ Yset θ, 0 ≤ eval y (f - C ρ - rieszP Φ.moments P)) ∧ r = (ρ : EReal)}

/-- The feasible set of (4.3) (p. 18): finite Borel measures `µ ∈ 𝔪_+(𝒴)` on `ℝ^ℓ`
(`µ(𝒴ᶜ) = 0`) integrating every polynomial, with `𝓗_µ(1) = 1` and
`𝓗_µ(P(y, x)) = ∑_β P_β(x) ∫ y^β dµ ∈ 𝒫^m(𝒳)`. -/
def ConicDualFeasible (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) (μ : Measure (Fin ℓ → ℝ)) : Prop :=
  IsFiniteMeasure μ ∧ μ (Yset θ)ᶜ = 0 ∧
    (∀ p : MvPolynomial (Fin ℓ) ℝ, Integrable (fun y => eval y p) μ) ∧
    (∫ _y, (1 : ℝ) ∂μ) = 1 ∧
    ∀ x ∈ Xset G, ((HsP (measMoments μ) P).map (eval x)).PosSemidef

/-- The value `f̂` of the conic program (4.3) (p. 18): `inf 𝓗_µ(f) = ∫ f dµ` over the feasible set
of (4.3). `⊤` if infeasible. -/
def fhat (f : MvPolynomial (Fin ℓ) ℝ) (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) : EReal :=
  sInf {r : EReal | ∃ μ : Measure (Fin ℓ → ℝ), ConicDualFeasible θ P G μ ∧
    r = ((∫ y, eval y f ∂μ : ℝ) : EReal)}

end Conic

/-! ## Optimal solutions of (4.4), Assumption 4, the interior of `𝒬_k(Θ)` (pp. 19–22) -/

section Hierarchy

variable {ℓ n m q s : ℕ}

/-- `(ρ, S)` is an optimal solution of (4.4) (p. 19): it is feasible
(`S ∈ 𝓜^m_k(G)`, `f − ρ − 𝓛_S(P(y, x)) ∈ 𝒬_{⌈k_y/2⌉}(Θ)`) and `ρ = f_k^primal`. -/
def IsPrimalOpt (f : MvPolynomial (Fin ℓ) ℝ) (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) (k : ℕ) (ρ : ℝ)
    (S : MatSeq (Fin n) (Fin m)) : Prop :=
  S ∈ MM k G ∧ f - C ρ - rieszP S P ∈ QTheta ((ky f θ P + 1) / 2) θ ∧
    fprimal f θ P G k = (ρ : EReal)

/-- Assumption 4 (i) (p. 22): `s ≥ 1` and `θ₁(y) = b² − ∑_{i=1}^ℓ y_i²` for some `b ≠ 0`. -/
def Assumption4i (θ : Fin s → MvPolynomial (Fin ℓ) ℝ) : Prop :=
  ∃ (hs : 0 < s) (b : ℝ), b ≠ 0 ∧ θ ⟨0, hs⟩ = C (b ^ 2) - ∑ i, X i ^ 2

/-- Assumption 4 (ii) (p. 22): `𝒳` has non-empty interior. -/
def Assumption4ii (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) : Prop :=
  (interior (Xset G)).Nonempty

/-- The coefficient vector `(h_α)_{α ∈ ℕ^ℓ_{d}}` of a polynomial, identifying `ℝ[y]_d` with the
finite-dimensional space `ℝ^{ℕ^ℓ_d}`. -/
def coeffVec (d : ℕ) (h : MvPolynomial (Fin ℓ) ℝ) : monos (σ := Fin ℓ) d → ℝ :=
  fun α => coeff α.1 h

/-- `h ∈ 𝒬°_k(Θ)` (Lemma 4.12, p. 22): `h` lies in the interior of `𝒬_k(Θ)` taken inside the
finite-dimensional space `ℝ[y]_{2k}` of polynomials of degree at most `2k` (identified with
coefficient vectors). -/
def InInteriorQTheta (k : ℕ) (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (h : MvPolynomial (Fin ℓ) ℝ) : Prop :=
  h.totalDegree ≤ 2 * k ∧
    coeffVec (2 * k) h ∈
      interior (coeffVec (2 * k) '' {g | g ∈ QTheta k θ ∧ g.totalDegree ≤ 2 * k})

end Hierarchy

/-! ## The robust polynomial SDP (RPSDP) and its relaxations (4.14)–(4.15) (pp. 25–26) -/

section RPSDP

variable {ℓ n m q : ℕ}

/-- The polynomial matrix `∑_{i=1}^ℓ P_i(x) y_i − P_0(x)` of (RPSDP) (p. 25). -/
def lmi (P0 : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ))
    (Pv : Fin ℓ → Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ)) (y : Fin ℓ → ℝ) :
    Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ) :=
  ∑ i, y i • Pv i - P0

/-- Feasible set of (RPSDP): `y ∈ ℝ^ℓ` with `∑ P_i(x) y_i − P_0(x) ⪰ 0` for all `x ∈ 𝒳`. -/
def FeasibleSDP (P0 : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ))
    (Pv : Fin ℓ → Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) : Set (Fin ℓ → ℝ) :=
  {y | ∀ x ∈ Xset G, ((lmi P0 Pv y).map (eval x)).PosSemidef}

/-- `τ⋆ := inf_{y} cᵀy` over the feasible set of (RPSDP) (p. 25). -/
def taustar (c : Fin ℓ → ℝ) (P0 : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ))
    (Pv : Fin ℓ → Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) : ℝ :=
  sInf ((fun y => ∑ i, c i * y i) '' FeasibleSDP P0 Pv G)

/-- `y` is an optimal solution of (RPSDP). -/
def IsOptSDP (c : Fin ℓ → ℝ) (P0 : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ))
    (Pv : Fin ℓ → Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) (y : Fin ℓ → ℝ) : Prop :=
  y ∈ FeasibleSDP P0 Pv G ∧
    ∀ y' ∈ FeasibleSDP P0 Pv G, ∑ i, c i * y i ≤ ∑ i, c i * y' i

/-- `k_x` for (RPSDP): the maximal degree of `P_0, …, P_ℓ` and `G` (the `x`-degree of
`∑ P_i(x) y_i − P_0(x)` and `deg G`, as in (RPMIO), p. 19). -/
def kxSDP (P0 : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ))
    (Pv : Fin ℓ → Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) : ℕ :=
  max (degMat P0) (max (Finset.univ.sup fun i => degMat (Pv i)) (degMat G))

/-- Feasibility in (4.14): `S ∈ 𝓜^m_k(G)` and `𝓛_S(P_i) = c_i` for `i = 1, …, ℓ`. -/
def TauPrimalFeasible (c : Fin ℓ → ℝ)
    (Pv : Fin ℓ → Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) (k : ℕ)
    (S : MatSeq (Fin n) (Fin m)) : Prop :=
  S ∈ MM k G ∧ ∀ i, riesz S (Pv i) = c i

/-- (4.14) (p. 26): `τ_k^primal := sup 𝓛_S(P_0)` over the feasible set of (4.14). -/
def tauprimal (c : Fin ℓ → ℝ) (P0 : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ))
    (Pv : Fin ℓ → Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) (k : ℕ) : EReal :=
  sSup {r : EReal | ∃ S, TauPrimalFeasible c Pv G k S ∧ r = (riesz S P0 : EReal)}

/-- (4.15) (p. 26): `τ_k^dual := inf cᵀy` s.t. `∑ P_i(x) y_i − P_0(x) ∈ 𝒬^m_k(G)`. -/
def taudual (c : Fin ℓ → ℝ) (P0 : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ))
    (Pv : Fin ℓ → Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) (k : ℕ) : EReal :=
  sInf {r : EReal | ∃ y : Fin ℓ → ℝ, lmi P0 Pv y ∈ QM k G ∧ r = ((∑ i, c i * y i : ℝ) : EReal)}

/-- `S` is an optimal solution of (4.14). -/
def IsTauPrimalOpt (c : Fin ℓ → ℝ) (P0 : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ))
    (Pv : Fin ℓ → Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) (k : ℕ)
    (S : MatSeq (Fin n) (Fin m)) : Prop :=
  TauPrimalFeasible c Pv G k S ∧
    ∀ S', TauPrimalFeasible c Pv G k S' → riesz S' P0 ≤ riesz S P0

/-- `y` is an optimal solution of (4.15). -/
def IsTauDualOpt (c : Fin ℓ → ℝ) (P0 : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ))
    (Pv : Fin ℓ → Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) (k : ℕ) (y : Fin ℓ → ℝ) : Prop :=
  lmi P0 Pv y ∈ QM k G ∧
    ∀ y' : Fin ℓ → ℝ, lmi P0 Pv y' ∈ QM k G → ∑ i, c i * y i ≤ ∑ i, c i * y' i

/-- Assumption 3 (Slater, p. 17) for (RPSDP), where `𝒴 = ℝ^ℓ`: there is `ȳ ∈ ℝ^ℓ` with
`∑ P_i(x) ȳ_i − P_0(x) ≻ 0` for all `x ∈ 𝒳`. -/
def Assumption3SDP (P0 : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ))
    (Pv : Fin ℓ → Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) : Prop :=
  ∃ ybar : Fin ℓ → ℝ, ∀ x ∈ Xset G, ((lmi P0 Pv ybar).map (eval x)).PosDef

end RPSDP

/-! ## The smallest eigenvalue of a polynomial matrix (4.16), (4.18)–(4.19) (p. 27) -/

section Eigen

variable {n m q : ℕ}

/-- `λ_min(A)` of a real symmetric matrix, as the minimum of the Rayleigh quotient
`vᵀ A v` over unit vectors (for a symmetric `A` with `m ≥ 1` this is its smallest eigenvalue). -/
def lamMin (A : Matrix (Fin m) (Fin m) ℝ) : EReal :=
  ⨅ v ∈ {v : Fin m → ℝ | ∑ i, v i ^ 2 = 1}, ((v ⬝ᵥ A *ᵥ v : ℝ) : EReal)

/-- (4.16) (p. 27): `λ⋆ := inf_{x ∈ 𝒳} λ_min(F(x))` (`⊤` if `𝒳 = ∅`). -/
def lamstar (F : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) : EReal :=
  ⨅ x ∈ Xset G, lamMin (F.map (eval x))

/-- Feasibility in (4.18): `S ∈ 𝓜^m_k(G)` and `𝓛_S(I_m) = 1`. -/
def LamPrimalFeasible (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) (k : ℕ)
    (S : MatSeq (Fin n) (Fin m)) : Prop :=
  S ∈ MM k G ∧ riesz S (1 : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ)) = 1

/-- (4.18) (p. 27): `λ_k^primal := inf 𝓛_S(F)` over the feasible set of (4.18). -/
def lamprimal (F : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) (k : ℕ) : EReal :=
  sInf {r : EReal | ∃ S, LamPrimalFeasible G k S ∧ r = (riesz S F : EReal)}

/-- (4.19) (p. 27): `λ_k^dual := sup λ` s.t. `F(x) − λ I_m ∈ 𝒬^m_k(G)`. -/
def lamdual (F : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) (k : ℕ) : EReal :=
  sSup {r : EReal | ∃ lam : ℝ, F - lam • (1 : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ)) ∈
    QM k G ∧ r = (lam : EReal)}

/-- `S` is an optimal solution of (4.18). -/
def IsLamPrimalOpt (F : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) (k : ℕ)
    (S : MatSeq (Fin n) (Fin m)) : Prop :=
  LamPrimalFeasible G k S ∧ ∀ S', LamPrimalFeasible G k S' → riesz S F ≤ riesz S' F

end Eigen

/-! ## The general convex and non-convex settings (§5, pp. 6, 29) -/

section Convex

variable {ℓ n m q s : ℕ}

/-- Definition 2.3 (p. 6): `Q(y) ∈ 𝕊[y]^m` is PSD-convex if
`t Q(y¹) + (1 − t) Q(y²) − Q(t y¹ + (1 − t) y²) ⪰ 0` for all `y¹, y² ∈ ℝ^ℓ`, `t ∈ (0, 1)`. -/
def IsPSDConvex (Q : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ) ℝ)) : Prop :=
  ∀ (y₁ y₂ : Fin ℓ → ℝ) (t : ℝ), 0 < t → t < 1 →
    (t • Q.map (eval y₁) + (1 - t) • Q.map (eval y₂) - Q.map (eval (t • y₁ + (1 - t) • y₂))).PosSemidef

/-- Assumption 5 (p. 29): (i) `f, −θ_1, …, −θ_s` are convex; (ii) `−P(y, x)` is PSD-convex in `y`
for all `x ∈ 𝒳`; (iii) `𝒳` is compact. -/
def Assumption5 (f : MvPolynomial (Fin ℓ) ℝ) (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) : Prop :=
  ConvexOn ℝ Set.univ (fun y => eval y f) ∧
    (∀ j, ConvexOn ℝ Set.univ (fun y => eval y (-θ j))) ∧
    (∀ x ∈ Xset G, IsPSDConvex (-(Patx P x))) ∧ IsCompact (Xset G)

/-- (5.1) (p. 29): `f_k^primal := sup ρ` s.t. `f − ρ − 𝓛_S(P(y, x)) ∈ 𝒬_k(Θ)`, `S ∈ 𝓜^m_k(G)`. -/
def fprimal5 (f : MvPolynomial (Fin ℓ) ℝ) (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) (k : ℕ) : EReal :=
  sSup {r : EReal | ∃ (ρ : ℝ) (S : MatSeq (Fin n) (Fin m)), S ∈ MM k G ∧
    f - C ρ - rieszP S P ∈ QTheta k θ ∧ r = (ρ : EReal)}

/-- Feasibility in (5.2): `s ∈ 𝓜_k(Θ)`, `𝓗_s(1) = 1`, `𝓗_s(P(y, x)) ∈ 𝒬^m_k(G)`. -/
def DualFeasible5 (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) (k : ℕ)
    (v : (Fin ℓ →₀ ℕ) → ℝ) : Prop :=
  v ∈ MTheta k θ ∧ Hs v 1 = 1 ∧ HsP v P ∈ QM k G

/-- (5.2) (p. 29): `f_k^dual := inf 𝓗_s(f)` over the feasible set of (5.2). -/
def fdual5 (f : MvPolynomial (Fin ℓ) ℝ) (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) (k : ℕ) : EReal :=
  sInf {r : EReal | ∃ v, DualFeasible5 θ P G k v ∧ r = (Hs v f : EReal)}

/-- `(ρ, S)` is an optimal solution of (5.1): feasible and `ρ = f_k^primal`. -/
def IsPrimalOpt5 (f : MvPolynomial (Fin ℓ) ℝ) (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) (k : ℕ) (ρ : ℝ)
    (S : MatSeq (Fin n) (Fin m)) : Prop :=
  S ∈ MM k G ∧ f - C ρ - rieszP S P ∈ QTheta k θ ∧ fprimal5 f θ P G k = (ρ : EReal)

/-- `v` is a minimizer (optimal solution) of (5.2). -/
def IsDualMinimizer5 (f : MvPolynomial (Fin ℓ) ℝ) (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) (k : ℕ)
    (v : (Fin ℓ →₀ ℕ) → ℝ) : Prop :=
  DualFeasible5 θ P G k v ∧ ∀ v', DualFeasible5 θ P G k v' → Hs v f ≤ Hs v' f

/-- `d_Θ := max{⌈deg(θ_i)/2⌉ : i = 1, …, s}` (p. 29; `0` if `s = 0`). -/
def dTheta (θ : Fin s → MvPolynomial (Fin ℓ) ℝ) : ℕ :=
  Finset.univ.sup fun j => ((θ j).totalDegree + 1) / 2

/-- A representing probability measure `µ = ∑_{j=1}^r λ_j δ_{y^{(j)}} ∈ 𝔪_+(𝒴)` with distinct
atoms `y^{(j)} ∈ 𝒴` and positive weights `λ_j` summing to `1` (Theorem 5.4 (ii), p. 30). -/
structure AtomicProb (θ : Fin s → MvPolynomial (Fin ℓ) ℝ) where
  r : ℕ
  pts : Fin r → Fin ℓ → ℝ
  wt : Fin r → ℝ
  inj : Function.Injective pts
  mem : ∀ j, pts j ∈ Yset θ
  pos : ∀ j, 0 < wt j
  sum_one : ∑ j, wt j = 1

/-- The moments `∑_j λ_j (y^{(j)})^α` of an atomic probability measure. -/
def AtomicProb.moments {θ : Fin s → MvPolynomial (Fin ℓ) ℝ} (μ : AtomicProb θ) :
    (Fin ℓ →₀ ℕ) → ℝ :=
  fun α => ∑ j, μ.wt j * eval (μ.pts j) (monomial α (1 : ℝ))

/-- The barycenter `∑_j λ_j y^{(j)}` of an atomic probability measure (Theorem 5.4 (iv)). -/
def AtomicProb.barycenter {θ : Fin s → MvPolynomial (Fin ℓ) ℝ} (μ : AtomicProb θ) :
    Fin ℓ → ℝ :=
  ∑ j, μ.wt j • μ.pts j

/-- `s = (s_α)_{α ∈ ℕ^ℓ}` admits a representing probability measure (Lemma 5.1, p. 29): a Borel
probability measure `µ` on `ℝ^ℓ`, every monomial `µ`-integrable, with `s_α = ∫ y^α dµ` for all
`α`. -/
def HasRepProb (v : (Fin ℓ →₀ ℕ) → ℝ) : Prop :=
  ∃ μ : Measure (Fin ℓ → ℝ), IsProbabilityMeasure μ ∧
    ∀ α : Fin ℓ →₀ ℕ, Integrable (fun y => eval y (monomial α (1 : ℝ))) μ ∧
      v α = ∫ y, eval y (monomial α (1 : ℝ)) ∂μ

end Convex

end

end RobustPMI.Hierarchy.Supplement


