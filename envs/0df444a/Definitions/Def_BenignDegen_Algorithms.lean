-- Prove2me | Definitions.Def_BenignDegen_Algorithms
-- name    : BenignDegen_Algorithms
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:54:49.740194+00:00
-- url     : https://prove2.me/theorems/5f9a94cd-082b-406f-a5ca-ab3ce9201264
-- title:
--   Exact ADMM, exact sGS–ADMM, fixed-step PDHG, the shadow $Z^k$, the metrics $G_\tau$, $G_P$, the chart (F.8), $L_{\eta_x,\eta_y}$ (F.9), and the conclusions of Corollaries 5.1–5.2
-- statement:
--   For the SDP pair (3.1):
--
--   1. **Exact ADMM** with penalty $\sigma$ and step $\tau$ (F.2)–(F.4): $\lambda^{k+1}=(\mathcal A\mathcal A^*)^{-1}[\sigma^{-1}b-\mathcal A(\sigma^{-1}X^k+S^k-C)]$, $S^{k+1}=\Pi_+(C-\mathcal A^*\lambda^{k+1}-\sigma^{-1}X^k)$, $X^{k+1}=X^k+\tau\sigma(\mathcal A^*\lambda^{k+1}+S^{k+1}-C)$, from any $(X^0,S^0)$.
--   2. **Exact sGS–ADMM**: $\lambda^{k+1/2}$ by (F.2), $S^{k+1}$ by (F.3) with $\lambda^{k+1/2}$, $\lambda^{k+1}$ by (F.2) with $S^{k+1}$, then (F.4).
--   3. The **shadow** $Z^k=\mathsf P^\perp X^k+X_b-\sigma\mathsf PS^k-\sigma\mathsf P^\perp C$ and the metric $\mathsf G_\tau=\mathsf P+\tau^{-1}\mathsf P^\perp$.
--   4. **Fixed-step PDHG** on $w=(X,\lambda)$: $X^+=\Pi_+(X-\eta_x(C-\mathcal A^*\lambda))$, $\lambda^+=\lambda+\eta_y(b-\mathcal A(2X^+-X))$; the map $T_P$, $\mathcal W_\star=\operatorname{Fix}T_P$, the chart $\Phi(X,\lambda)=(X-\eta_x(C-\mathcal A^*\lambda),\mathcal AX-b)$, the map $L_{\eta_x,\eta_y}(R^\parallel,R^\perp,r)=(R^\parallel-R^\perp-\mathcal A^\dagger r-\eta_x\eta_y\mathcal A^*(2\mathcal AR^\parallel-r),\ \mathcal AR^\parallel-r)$, and the metric $\mathsf G_P=\begin{bmatrix}\eta_x^{-1}\mathrm{Id}&\mathcal A^*\\\mathcal A&\eta_y^{-1}I_m\end{bmatrix}$.
--   5. The **conclusions of Corollary 5.1** for a run: the shadow converges to some $\bar Z\in\mathcal Z_\star$, $\operatorname{dist}_{\mathsf G_\tau}(Z^k,\mathcal Z_\star)$ contracts eventually Q-linearly, $Z^k\to\bar Z$ R-linearly, and $X^k,S^k,\lambda^k$ converge R-linearly to a KKT triple $(\bar X,\bar\lambda,\bar S)$ with $\bar Z=\bar X-\sigma\bar S$.
--   6. The **conclusions of Corollary 5.2** for a PDHG run: $(X^k,\lambda^k)$ converges to a KKT pair in $\mathcal W_\star$, $\operatorname{dist}_{\mathsf G_P}$ to $\mathcal W_\star$ contracts eventually Q-linearly, and $X^k$, $\lambda^k$, $S^k=C-\mathcal A^*\lambda^k$ converge R-linearly.
--
--   **Formalization Note** A run is any sequence satisfying the update equations for every $k$; the unused $\lambda^0$ is free. The PDHG state space $\mathbb S^p\times\mathbb R^m$ carries the product Euclidean norm.
-- source:
--   Kang, Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations, arXiv:2610.20270v1, §5, pp.10–11; Appendix F.2, (F.2)–(F.7), pp.28–29; Appendix F.4, (F.8)–(F.9) and Proposition F.4, pp.29–30

import Mathlib
import Definitions.Def_BenignDegen_SDP
import Definitions.Def_BenignDegen_Convergence

namespace BenignDegen

open SunNLSDP.Equiv Filter Topology
open scoped RealInnerProductSpace

noncomputable section

/-! # Exact ADMM, exact sGS–ADMM, fixed-step PDHG, their metrics and their conclusions

Kang, *Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations*,
arXiv:2610.20270v1, §5, pp.10–11 (shadow map, `G_τ`, PDHG and its chart, Corollaries 5.1–5.2);
Appendix F.2, (F.2)–(F.7), pp.28–29; Appendix F.4, (F.8)–(F.9) and Proposition F.4, pp.29–30.

**Formalization Note** A run of an algorithm is a sequence satisfying the update equations for
every `k`, from an arbitrary initialization; every theorem quantifies over all runs. The
multiplier `λ_0` of ADMM/sGS–ADMM is not used by the recursion and is left free. The PDHG state
space `S^p × ℝ^m` is `WithLp 2 (SymMat ι × EuclideanSpace ℝ κ)`, whose norm is the product
Euclidean norm `√(‖X‖_F² + ‖λ‖₂²)`. `G_P` is the operator `(X, λ) ↦ (η_x^{-1}X + A^*λ, AX + η_y^{-1}λ)`,
so `‖(X, λ)‖²_{G_P} = η_x^{-1}‖X‖²_F + 2⟨AX, λ⟩ + η_y^{-1}‖λ‖²₂`. -/

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The PDHG state space `S^p × ℝ^m` with the product Euclidean norm. -/
abbrev PDSpace (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] : Type :=
  WithLp 2 (SymMat ι × EuclideanSpace ℝ κ)

/-- The point `(X, λ) ∈ S^p × ℝ^m`. -/
def pdPt (X : SymMat ι) (lam : EuclideanSpace ℝ κ) : PDSpace ι κ := WithLp.toLp 2 (X, lam)

/-- The `X`-component of `w ∈ S^p × ℝ^m`. -/
def pdX (w : PDSpace ι κ) : SymMat ι := (WithLp.ofLp w).1

/-- The `λ`-component of `w ∈ S^p × ℝ^m`. -/
def pdLam (w : PDSpace ι κ) : EuclideanSpace ℝ κ := (WithLp.ofLp w).2

namespace SDPData

variable (D : SDPData ι κ)

/-- The metric `G_τ := P + τ^{-1}P^⊥` on `S^p` (§5, Proposition F.2). -/
def Gtau (τ : ℝ) : SymMat ι →L[ℝ] SymMat ι := D.P + τ⁻¹ • D.Pperp

/-- The shadow `Z^k := P^⊥X^k + X_b − σPS^k − σP^⊥C` (§5, Appendix F.2). -/
def shadow (σ : ℝ) (X S : ℕ → SymMat ι) (k : ℕ) : SymMat ι :=
  D.Pperp (X k) + D.Xb - σ • D.P (S k) - σ • D.Pperp D.C

/-- A run of exact ADMM on the dual SDP with penalty `σ` and multiplier step `τ`
((F.2)–(F.4), p.28), from an arbitrary `(X^0, S^0)`. -/
def IsADMMRun (σ τ : ℝ) (X S : ℕ → SymMat ι) (lam : ℕ → EuclideanSpace ℝ κ) : Prop :=
  ∀ k : ℕ,
    lam (k + 1) = D.AAinv (σ⁻¹ • D.b - D.A (σ⁻¹ • X k + S k - D.C)) ∧
    S (k + 1) = PiPlus (D.C - D.Aadj (lam (k + 1)) - σ⁻¹ • X k) ∧
    X (k + 1) = X k + (τ * σ) • (D.Aadj (lam (k + 1)) + S (k + 1) - D.C)

/-- A run of exact sGS–ADMM (Appendix F.2, p.29): `λ^{k+1/2}` by (F.2), `S^{k+1}` by (F.3) with
`λ^{k+1/2}`, `λ^{k+1}` by (F.2) with `S^{k+1}`, then (F.4); from an arbitrary `(X^0, S^0)`.
`lamH k` is `λ^{k+1/2}`. -/
def IsSGSRun (σ τ : ℝ) (X S : ℕ → SymMat ι) (lamH lam : ℕ → EuclideanSpace ℝ κ) : Prop :=
  ∀ k : ℕ,
    lamH k = D.AAinv (σ⁻¹ • D.b - D.A (σ⁻¹ • X k + S k - D.C)) ∧
    S (k + 1) = PiPlus (D.C - D.Aadj (lamH k) - σ⁻¹ • X k) ∧
    lam (k + 1) = D.AAinv (σ⁻¹ • D.b - D.A (σ⁻¹ • X k + S (k + 1) - D.C)) ∧
    X (k + 1) = X k + (τ * σ) • (D.Aadj (lam (k + 1)) + S (k + 1) - D.C)

/-- The conclusions of Corollary 5.1 (pp.10–11, proof p.29) for one run `(X^k, S^k, λ^k)` of
exact ADMM or exact sGS–ADMM: the shadow converges to an endpoint `Z̄ ∈ Z_⋆`, its `G_τ`-distance
to `Z_⋆` contracts eventually Q-linearly, `Z^k → Z̄` R-linearly, and the raw iterates converge
R-linearly to a KKT triple `(X̄, λ̄, S̄)` with `Z̄ = X̄ − σS̄`. -/
def ADMMConclusions (σ τ : ℝ) (X S : ℕ → SymMat ι) (lam : ℕ → EuclideanSpace ℝ κ) : Prop :=
  ∃ Zbar ∈ D.Zstar σ,
    Tendsto (D.shadow σ X S) atTop (𝓝 Zbar) ∧
    EventuallyQLinear (fun k => gDist (D.Gtau τ) (D.shadow σ X S k) (D.Zstar σ)) ∧
    RLinearTo (D.shadow σ X S) Zbar ∧
    ∃ Xbar Sbar lbar, Zbar = Xbar - σ • Sbar ∧ D.IsKKTTriple Xbar lbar Sbar ∧
      RLinearTo X Xbar ∧ RLinearTo S Sbar ∧ RLinearTo lam lbar

/-- One step of fixed-step PDHG (§5, p.10) on `w = (X, λ)`:
`X⁺ = Π₊(X − η_x(C − A^*λ))`, `λ⁺ = λ + η_y(b − A(2X⁺ − X))`. -/
def pdhgMap (ηx ηy : ℝ) (w : PDSpace ι κ) : PDSpace ι κ :=
  pdPt (PiPlus (pdX w - ηx • (D.C - D.Aadj (pdLam w))))
    (pdLam w + ηy • (D.b - D.A ((2 : ℝ) • PiPlus (pdX w - ηx • (D.C - D.Aadj (pdLam w)))
      - pdX w)))

/-- `W_⋆ := Fix T_P` (§5). -/
def Wstar (ηx ηy : ℝ) : Set (PDSpace ι κ) := fixedPts (D.pdhgMap ηx ηy)

/-- A PDHG run from an arbitrary `(X^0, λ^0)`. -/
def IsPDHGRun (ηx ηy : ℝ) (X : ℕ → SymMat ι) (lam : ℕ → EuclideanSpace ℝ κ) : Prop :=
  ∀ k : ℕ, X (k + 1) = PiPlus (X k - ηx • (D.C - D.Aadj (lam k))) ∧
    lam (k + 1) = lam k + ηy • (D.b - D.A ((2 : ℝ) • X (k + 1) - X k))

/-- The chart `Φ(X, λ) = (Z, r)`, `Z := X − η_x(C − A^*λ)`, `r := AX − b` ((F.8), p.29). -/
def chart (ηx : ℝ) (w : PDSpace ι κ) : PDSpace ι κ :=
  pdPt (pdX w - ηx • (D.C - D.Aadj (pdLam w))) (D.A (pdX w) - D.b)

/-- The linear map `L_{η_x,η_y}(R^∥, R^⊥, r) = (R^∥ − R^⊥ − A†r − η_xη_yA^*(2AR^∥ − r), AR^∥ − r)`
of (F.9), p.29. -/
def Lmap (ηx ηy : ℝ) (Rpar Rperp : SymMat ι) (r : EuclideanSpace ℝ κ) : PDSpace ι κ :=
  pdPt (Rpar - Rperp - D.Apinv r - (ηx * ηy) • D.Aadj ((2 : ℝ) • D.A Rpar - r))
    (D.A Rpar - r)

/-- The PDHG metric `G_P = [[η_x^{-1} Id, A^*], [A, η_y^{-1} I_m]]` (Proposition F.4, p.30), as a
linear map `(X, λ) ↦ (η_x^{-1}X + A^*λ, AX + η_y^{-1}λ)`. -/
def GP (ηx ηy : ℝ) : PDSpace ι κ →L[ℝ] PDSpace ι κ :=
  LinearMap.toContinuousLinearMap
    ((WithLp.linearEquiv 2 ℝ (SymMat ι × EuclideanSpace ℝ κ)).symm.toLinearMap ∘ₗ
      (LinearMap.prod
        (ηx⁻¹ • LinearMap.fst ℝ (SymMat ι) (EuclideanSpace ℝ κ) +
          (D.Aadj : EuclideanSpace ℝ κ →ₗ[ℝ] SymMat ι) ∘ₗ
            LinearMap.snd ℝ (SymMat ι) (EuclideanSpace ℝ κ))
        ((D.A : SymMat ι →ₗ[ℝ] EuclideanSpace ℝ κ) ∘ₗ
            LinearMap.fst ℝ (SymMat ι) (EuclideanSpace ℝ κ) +
          ηy⁻¹ • LinearMap.snd ℝ (SymMat ι) (EuclideanSpace ℝ κ))) ∘ₗ
      (WithLp.linearEquiv 2 ℝ (SymMat ι × EuclideanSpace ℝ κ)).toLinearMap)

/-- The conclusions of Corollary 5.2 (p.11, proof p.30) for one PDHG run: `(X^k, λ^k)` converges to
a KKT pair `(X̄, λ̄) ∈ W_⋆`; its `G_P`-distance to `W_⋆` contracts eventually Q-linearly; `X^k`,
`λ^k` and the slack `S^k = C − A^*λ^k` converge R-linearly. -/
def PDHGConclusions (ηx ηy : ℝ) (X : ℕ → SymMat ι) (lam : ℕ → EuclideanSpace ℝ κ) : Prop :=
  ∃ Xbar lbar, pdPt Xbar lbar ∈ D.Wstar ηx ηy ∧
    D.IsKKTTriple Xbar lbar (D.C - D.Aadj lbar) ∧
    Tendsto (fun k => pdPt (X k) (lam k)) atTop (𝓝 (pdPt Xbar lbar)) ∧
    EventuallyQLinear (fun k => gDist (D.GP ηx ηy) (pdPt (X k) (lam k)) (D.Wstar ηx ηy)) ∧
    RLinearTo X Xbar ∧ RLinearTo lam lbar ∧
    RLinearTo (fun k => D.C - D.Aadj (lam k)) (D.C - D.Aadj lbar)

end SDPData

end

end BenignDegen


