-- Prove2me | Definitions.Def_BenignDegen_SDP
-- name    : BenignDegen_SDP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:53:58.696097+00:00
-- url     : https://prove2.me/theorems/878c171a-a03a-4961-bd93-7acd50e81684
-- title:
--   The SDP pair (3.1), the canonical DR residual $\delta_\sigma$ (3.2), the shadow map $T_{\sigma,\tau}$, optimal sets, KKT pairs, stall cone and the error bound (3.9)
-- statement:
--   Let $\mathbb S^p$ be the space of real symmetric $p\times p$ matrices with the trace inner product $\langle H_1,H_2\rangle=\operatorname{tr}(H_1H_2)$ and Frobenius norm. Given a linear map $\mathcal A:\mathbb S^p\to\mathbb R^m$, $b\in\mathbb R^m$ and $C\in\mathbb S^p$, consider the primal–dual pair
--
--   $$
--   (\mathrm P)\ \min_{X\succeq0}\langle C,X\rangle\ \text{s.t. }\mathcal AX=b,\qquad (\mathrm D)\ \max_{\lambda\in\mathbb R^m,\,S\succeq0} b^\top\lambda\ \text{s.t. }\mathcal A^*\lambda+S=C .
--   $$
--
--   With $\mathcal R=\operatorname{ran}\mathcal A^*$, $\mathcal N=\ker\mathcal A$, $\mathcal A^\dagger=\mathcal A^*(\mathcal A\mathcal A^*)^{-1}$, $\mathsf P$ the orthogonal projector onto $\mathcal R$, $\mathsf P^\perp=\mathrm{Id}-\mathsf P$, $X_b=\mathcal A^\dagger b$, $\Pi_+$ the Frobenius projection onto $\mathbb S^p_+$ and $\Pi_-=\mathrm{Id}-\Pi_+$, this module defines:
--
--   1. the residual components $r^\parallel(Z)=\mathsf P(\Pi_+(Z)-X_b)$, $r^\perp_\sigma(Z)=\mathsf P^\perp(\Pi_-(Z)+\sigma C)$ and the canonical Douglas–Rachford residual $\delta_\sigma=-r^\parallel-r^\perp_\sigma$;
--   2. the shadow map $T_{\sigma,\tau}=\mathrm{Id}-\mathsf D_\tau(r^\parallel+r^\perp_\sigma)$ with $\mathsf D_\tau=\mathsf P+\tau\mathsf P^\perp$ (so $T_{\sigma,1}=\mathrm{Id}+\delta_\sigma$), its residual $\delta_{\sigma,\tau}=T_{\sigma,\tau}-\mathrm{Id}$, and the endpoint set $\mathcal Z_\star=\operatorname{Fix}T_{\sigma,1}$;
--   3. the primal optimal set $\mathcal X_\star$, the optimal slack set $\mathcal S_\star$ (slacks of dual optimal pairs), KKT triples $(X,\lambda,S)$ ($X\succeq0$, $\mathcal AX=b$, $S\succeq0$, $\mathcal A^*\lambda+S=C$, $XS=0$) and KKT pairs;
--   4. the proximal point $\operatorname{prox}_{\sigma F}(W)$ of $F(X)=\langle C,X\rangle+\iota_{\{\mathcal AX=b\}}(X)$, as a predicate;
--   5. the stall cone $\mathcal C(\bar Z)=\{H:\delta_\sigma'(\bar Z;H)=0\}$ (3.6) with the one-sided directional derivative;
--   6. the setwise error bound (3.9): there are $c_\sigma,t_\sigma>0$ with $\|\delta_\sigma(Z)\|_F\ge c_\sigma\operatorname{dist}_F(Z,\mathcal Z_\star)$ whenever $\operatorname{dist}_F(Z,\mathcal Z_\star)\le t_\sigma$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** $\mathbb S^p$ is the published `SunNLSDP.Equiv.SymMat ι` (finite index type $\iota$), $\mathbb R^m$ is `EuclideanSpace ℝ κ`. $\Pi_+$ is the published `metricProj` onto `psdCone`. $\mathcal A^\dagger$ is written with `ContinuousLinearMap.inverse`, which is the true inverse when $\mathcal A$ is surjective — the standing assumption of (3.1), carried as a hypothesis by every theorem.
-- source:
--   Kang, Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations, arXiv:2610.20270v1, §3.1, (3.1)–(3.2), (3.4), p.6; (3.6), (3.9), p.7; §5, p.10; Lemma C.1 and its proof, pp.16–17

import Mathlib
import Definitions.Def_SunNLSDP_Equiv_Setting
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
import Definitions.Def_RobinsonSR_Reduction_Setting

namespace BenignDegen

open SunNLSDP.Equiv
open scoped RealInnerProductSpace

noncomputable section

/-! # The abstract SDP pair (3.1) and the canonical DR residual (3.2)

Kang, *Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations*,
arXiv:2610.20270v1, §3.1, (3.1)–(3.2), p.6; Lemma C.1 and the KKT conditions of its proof,
p.16–17; §5, p.10 (the shadow map `T_{σ,τ}`).

**Formalization Note** `S^p` is `SunNLSDP.Equiv.SymMat ι` over a finite index type `ι`, with the
Frobenius (trace) inner product; `ℝ^m` is `EuclideanSpace ℝ κ` for a finite row type `κ`. The
adjoint `A^*` is `ContinuousLinearMap.adjoint`. `Π₊` is the published `metricProj` onto the
published `psdCone`, and `Π₋ := Id − Π₊` (p.4). `A† := A^*(AA^*)^{-1}` is written with
`ContinuousLinearMap.inverse`, which is the true inverse whenever `A` is surjective (the standing
assumption of (3.1), carried as a hypothesis by every theorem that uses `A†`). `P` is the
orthogonal projector onto `R = ran A^*` (`Submodule.starProjection`); it equals `A†A` when `A` is
surjective. -/

/-- The data `(A, b, C)` of the primal–dual SDP pair (3.1), p.6: a linear map
`A : S^p → ℝ^m`, a right-hand side `b ∈ ℝ^m` and a cost `C ∈ S^p`. Surjectivity of `A` is
stated separately (`Function.Surjective D.A`) wherever it is assumed. -/
structure SDPData (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] where
  /-- the constraint map `A : S^p → ℝ^m` -/
  A : SymMat ι →L[ℝ] EuclideanSpace ℝ κ
  /-- the right-hand side `b ∈ ℝ^m` -/
  b : EuclideanSpace ℝ κ
  /-- the cost matrix `C ∈ S^p` -/
  C : SymMat ι

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The PSD projection `Π₊ : S^p → S^p_+` (the Frobenius projection onto `S^p_+`, p.4). -/
def PiPlus (Z : SymMat ι) : SymMat ι := metricProj (psdCone ι) Z

/-- `Π₋ := Id − Π₊` (p.4). -/
def PiMinus (Z : SymMat ι) : SymMat ι := Z - PiPlus Z

namespace SDPData

variable (D : SDPData ι κ)

/-- The adjoint `A^* : ℝ^m → S^p`. -/
def Aadj : EuclideanSpace ℝ κ →L[ℝ] SymMat ι := ContinuousLinearMap.adjoint D.A

/-- `R := ran(A^*)` (p.6). -/
def rowSpace : Submodule ℝ (SymMat ι) :=
  LinearMap.range (D.Aadj : EuclideanSpace ℝ κ →ₗ[ℝ] SymMat ι)

/-- `N := ker(A)` (p.6). -/
def nullSpace : Submodule ℝ (SymMat ι) :=
  LinearMap.ker (D.A : SymMat ι →ₗ[ℝ] EuclideanSpace ℝ κ)

/-- `P`: the orthogonal projector onto `R` (p.6). -/
def P : SymMat ι →L[ℝ] SymMat ι := D.rowSpace.starProjection

/-- `P^⊥ := Id − P`, the orthogonal projector onto `N` (p.6). -/
def Pperp : SymMat ι →L[ℝ] SymMat ι := ContinuousLinearMap.id ℝ (SymMat ι) - D.P

/-- `(AA^*)^{-1}` (inverse of `A ∘ A^*`; a genuine inverse when `A` is surjective). -/
def AAinv : EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ := (D.A ∘L D.Aadj).inverse

/-- `A† := A^*(AA^*)^{-1}` (p.6). -/
def Apinv : EuclideanSpace ℝ κ →L[ℝ] SymMat ι := D.Aadj ∘L D.AAinv

/-- `X_b := A† b` (p.6). -/
def Xb : SymMat ι := D.Apinv D.b

/-- `r^∥(Z) := P(Π₊(Z) − X_b)` (3.2). -/
def rPar (Z : SymMat ι) : SymMat ι := D.P (PiPlus Z - D.Xb)

/-- `r^⊥_σ(Z) := P^⊥(Π₋(Z) + σC)` (3.2). -/
def rPerp (σ : ℝ) (Z : SymMat ι) : SymMat ι := D.Pperp (PiMinus Z + σ • D.C)

/-- The canonical DR residual `δ_σ := −r^∥ − r^⊥_σ` (3.2). -/
def delta (σ : ℝ) (Z : SymMat ι) : SymMat ι := -D.rPar Z - D.rPerp σ Z

/-- `D_τ := P + τP^⊥` (§5, p.10). -/
def Dtau (τ : ℝ) (W : SymMat ι) : SymMat ι := D.P W + τ • D.Pperp W

/-- The shadow map `T_{σ,τ}` with `T_{σ,τ} − Id = −D_τ(r^∥ + r^⊥_σ)` (§5, p.10). At `τ = 1`
it is the canonical DR map `T_{σ,1} = Id + δ_σ` of (3.2) (checked in the sanity file). -/
def T (σ τ : ℝ) (Z : SymMat ι) : SymMat ι := Z - D.Dtau τ (D.rPar Z + D.rPerp σ Z)

/-- `δ_{σ,τ} := T_{σ,τ} − Id` (§5, p.10). -/
def deltaTau (σ τ : ℝ) (Z : SymMat ι) : SymMat ι := D.T σ τ Z - Z

/-- The fixed-point set `Z_⋆ := Fix T_{σ,1}` (3.4), the set of endpoints. -/
def Zstar (σ : ℝ) : Set (SymMat ι) := {Z | D.T σ 1 Z = Z}

/-- Primal feasibility in (3.1): `X ⪰ 0`, `AX = b`. -/
def PrimalFeasible (X : SymMat ι) : Prop := X ∈ psdCone ι ∧ D.A X = D.b

/-- The primal optimal set `X_⋆` of (P) in (3.1): feasible points minimizing `⟨C, X⟩`. -/
def Xstar : Set (SymMat ι) :=
  {X | D.PrimalFeasible X ∧ ∀ Y, D.PrimalFeasible Y → ⟪D.C, X⟫ ≤ ⟪D.C, Y⟫}

/-- Dual feasibility in (3.1): `S ⪰ 0`, `A^*λ + S = C`. -/
def DualFeasible (lam : EuclideanSpace ℝ κ) (S : SymMat ι) : Prop :=
  S ∈ psdCone ι ∧ D.Aadj lam + S = D.C

/-- The optimal slack set `S_⋆` of (D) in (3.1): the slacks `S` of dual optimal pairs
`(λ, S)` (maximizing `b^⊤λ`). -/
def Sstar : Set (SymMat ι) :=
  {S | ∃ lam, D.DualFeasible lam S ∧
    ∀ lam' S', D.DualFeasible lam' S' → ⟪D.b, lam'⟫ ≤ ⟪D.b, lam⟫}

/-- A KKT triple `(X, λ, S)` of (3.1): `X ⪰ 0`, `AX = b`, `S ⪰ 0`, `A^*λ + S = C`, `XS = 0`
(proof of Lemma C.1, p.16–17). -/
def IsKKTTriple (X : SymMat ι) (lam : EuclideanSpace ℝ κ) (S : SymMat ι) : Prop :=
  X ∈ psdCone ι ∧ D.A X = D.b ∧ S ∈ psdCone ι ∧ D.Aadj lam + S = D.C ∧
    X.toMat * S.toMat = 0

/-- A KKT pair `(X, S)`: some multiplier `λ` makes `(X, λ, S)` a KKT triple (Lemma C.1). -/
def IsKKT (X S : SymMat ι) : Prop := ∃ lam, D.IsKKTTriple X lam S

/-- `X` is the proximal point `prox_{σF}(W)` of `F(X) = ⟨C, X⟩ + ι_{AX=b}(X)` (Lemma C.1):
`X` minimizes `F(Y) + ‖Y − W‖²/(2σ)` over `Y`. -/
def IsProxF (σ : ℝ) (W X : SymMat ι) : Prop :=
  D.A X = D.b ∧ ∀ Y, D.A Y = D.b →
    ⟪D.C, X⟫ + (1 / (2 * σ)) * ‖X - W‖ ^ 2 ≤ ⟪D.C, Y⟫ + (1 / (2 * σ)) * ‖Y - W‖ ^ 2

/-- The stall cone `C(Z̄) := {H ∈ S^p : δ'_σ(Z̄; H) = 0}` (3.6), with the one-sided directional
derivative of Appendix C (`NonsmoothNewton.Local.HasDirDerivAt`). -/
def stallCone (σ : ℝ) (Zbar : SymMat ι) : Set (SymMat ι) :=
  {H | NonsmoothNewton.Local.HasDirDerivAt (D.delta σ) Zbar H 0}

/-- The setwise error bound (3.9): there are `c_σ, t_σ > 0` with
`‖δ_σ(Z)‖_F ≥ c_σ dist_F(Z, Z_⋆)` whenever `dist_F(Z, Z_⋆) ≤ t_σ`. -/
def ErrorBound (σ : ℝ) : Prop :=
  ∃ c > (0 : ℝ), ∃ t > (0 : ℝ), ∀ Z : SymMat ι,
    Metric.infDist Z (D.Zstar σ) ≤ t → c * Metric.infDist Z (D.Zstar σ) ≤ ‖D.delta σ Z‖

end SDPData

end

end BenignDegen


