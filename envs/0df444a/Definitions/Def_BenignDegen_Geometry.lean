-- Prove2me | Definitions.Def_BenignDegen_Geometry
-- name    : BenignDegen_Geometry
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:54:47.602548+00:00
-- url     : https://prove2.me/theorems/f2404483-59f0-43f3-8e00-00c6081e960f
-- title:
--   Assumption 3.1, the direction spaces $\mathcal M,\mathcal L,\mathcal D$ (3.3), the identities (3.8), kernel cones $\mathcal K(\cdot)$, and conditions (i)–(v) of Theorem 3.2
-- statement:
--   For a subspace $E\subseteq\mathbb R^p$ with orthogonal projector $P_E$, $\mathbb S(E)=\{H\in\mathbb S^p: H=P_EHP_E\}$ are the symmetric matrices supported on $E$, and $\mathcal K(E)=\{W\succeq0:\operatorname{ran}W\subseteq E\}$.
--
--   **Assumption 3.1.** $\mathcal X_\star$ and $\mathcal S_\star$ are nonempty and compact, and the anchor pair $(X_{\rm sc},S_{\rm sc})\in\mathcal X_\star\times\mathcal S_\star$ satisfies $X_{\rm sc}S_{\rm sc}=0$, $X_{\rm sc}+S_{\rm sc}\succ0$ and $1\le\operatorname{rank}X_{\rm sc}<p$. With $U=\operatorname{ran}X_{\rm sc}$, $V=\operatorname{ran}S_{\rm sc}$,
--
--   $$
--   \mathcal M=\mathcal N\cap\mathbb S(U),\qquad \mathcal L=\mathcal R\cap\mathbb S(V),\qquad \mathcal D=\mathcal M\oplus\mathcal L .
--   $$
--
--   The **primal identity** at $\bar S$ is $\{E\in\mathcal N:P_VEP_V=0,\ E\bar S=0\}=\mathcal M$ and the **dual identity** at $\bar X$ is $\{F\in\mathcal R:P_UFP_U=0,\ \bar XF=0\}=\mathcal L$ (3.8). The five conditions of Theorem 3.2 at $\sigma>0$ are:
--
--   1. (i) $\mu_{\rm ri}>0$: a uniform lower bound on $\|\delta'_\sigma(\bar Z;H)\|_F$ over $\bar Z\in\operatorname{ri}\mathcal Z_\star$ and unit $H\in\mathcal D^\perp$;
--   2. (ii) the primal identity at every $\bar S\in\operatorname{rb}\mathcal S_\star$ and the dual identity at every $\bar X\in\operatorname{rb}\mathcal X_\star$;
--   3. (iii) the setwise error bound (3.9);
--   4. (iv) $\mu_{\rm nor}>0$: the same bound over $\bar Z\in\mathcal Z_\star$ and unit $H\in N_{\mathcal Z_\star}(\bar Z)$;
--   5. (v) $\mathcal C(\bar Z)=T_{\mathcal Z_\star}(\bar Z)$ for every $\bar Z\in\operatorname{rb}\mathcal Z_\star$.
--
--   The module also defines the Frobenius norm of a rectangular matrix, the operator norm, the Sylvester operator $Y\mapsto AY+\sigma YB$ and blocks $H_{EF}=B_E^\top HB_F$ in orthonormal bases.
--
--   **Formalization Note** $\mu_{\rm ri}>0$ and $\mu_{\rm nor}>0$ are encoded as "some $\mu>0$ bounds every derivative norm from below (and the derivative exists)", which matches $\inf\emptyset=+\infty$ and avoids the junk value `sInf ∅ = 0`. $\operatorname{ri}$ is `intrinsicInterior`, $\operatorname{rb}C=C\setminus\operatorname{ri}C$ (only used for closed sets). Tangent and normal cones are the published `SunNLSDP.Equiv.tangentCone` and `RobinsonSR.Reduction.normalCone`.
-- source:
--   Kang, Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations, arXiv:2610.20270v1, Assumption 3.1 and (3.3), p.6; (3.7)–(3.9) and Theorem 3.2, p.7; Appendix C conventions, p.16; §C.4, p.19

import Mathlib
import Definitions.Def_BenignDegen_SDP

namespace BenignDegen

open SunNLSDP.Equiv
open scoped RealInnerProductSpace Pointwise

noncomputable section

/-! # Two-sided optimal geometry (Assumption 3.1, (3.3)), endpoint cones, and the five conditions
of Theorem 3.2

Kang, *Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations*,
arXiv:2610.20270v1, §3.1–§3.3, pp.6–7 (Assumption 3.1, (3.3), (3.6)–(3.9)); Appendix C
conventions, p.16; §C.4, p.19 (the kernel cones `K(X̄)`, `K(S̄)`).

**Formalization Note** Vectors of `ℝ^p` are `EuclideanSpace ℝ ι`; a symmetric matrix acts on
them through `Matrix.toEuclideanLin`. `ran X`, `ker X` are the range and kernel of that map.
`P_E` is the matrix of the orthogonal projector onto `E` (`Submodule.starProjection`), and
`S(E) := {H ∈ S^p : H = P_E H P_E}` exactly as in Appendix C. "`X_UU ≻ 0`" (positive definite on
`U`) is `∀ u ∈ U, u ≠ 0 → 0 < ⟨u, Xu⟩`, which does not depend on the basis `B_U`;
"`P_K M P_K ⪰ 0`" is `∀ v ∈ K, 0 ≤ ⟨v, Mv⟩`. `ri` is `intrinsicInterior ℝ`, and
`rb C := C \ ri C` (the paper's `cl C \ ri C`; all sets to which it is applied are closed). The
moduli `μ_ri > 0`, `μ_nor > 0` of (3.7) are encoded as "there is `μ > 0` such that for every
admissible `(Z̄, H)` the directional derivative `δ'_σ(Z̄; H)` exists and has norm `≥ μ`"; this
avoids the junk value `sInf ∅ = 0` and matches `inf ∅ = +∞`. Tangent cones are the published
contingent cone `SunNLSDP.Equiv.tangentCone`, equal to Appendix C's sequential `T_C(z)`; normal
cones are the published `RobinsonSR.Reduction.normalCone` (`∅` off `C`, as in Appendix C). -/

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The underlying matrix, as a linear map `S^p → ℝ^{p×p}`. -/
def toMatLin : SymMat ι →ₗ[ℝ] Matrix ι ι ℝ where
  toFun X := X.toMat
  map_add' X Y := by ext i j; rfl
  map_smul' c X := by ext i j; rfl

/-- The action of a symmetric matrix on `ℝ^p`. -/
def act (X : SymMat ι) : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι :=
  Matrix.toEuclideanLin X.toMat

/-- `ran X ⊆ ℝ^p`. -/
def ranSub (X : SymMat ι) : Submodule ℝ (EuclideanSpace ℝ ι) := LinearMap.range (act X)

/-- `ker X ⊆ ℝ^p`. -/
def kerSub (X : SymMat ι) : Submodule ℝ (EuclideanSpace ℝ ι) := LinearMap.ker (act X)

/-- The matrix `P_E` of the orthogonal projector onto a subspace `E ⊆ ℝ^p`. -/
def projMat (E : Submodule ℝ (EuclideanSpace ℝ ι)) : Matrix ι ι ℝ :=
  Matrix.toEuclideanLin.symm
    (E.starProjection : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)

/-- The linear map `H ↦ H − P_E H P_E`. -/
def offSupport (E : Submodule ℝ (EuclideanSpace ℝ ι)) : SymMat ι →ₗ[ℝ] Matrix ι ι ℝ :=
  toMatLin - (LinearMap.mulLeft ℝ (projMat E) ∘ₗ LinearMap.mulRight ℝ (projMat E)) ∘ₗ toMatLin

/-- `S(E) := {H ∈ S^p : H = P_E H P_E}`, the symmetric matrices supported on `E` (Appendix C). -/
def supported (E : Submodule ℝ (EuclideanSpace ℝ ι)) : Submodule ℝ (SymMat ι) :=
  LinearMap.ker (offSupport E)

/-- `H` is positive definite on `E` ("`H_EE ≻ 0`"). -/
def PosDefOn (E : Submodule ℝ (EuclideanSpace ℝ ι)) (H : SymMat ι) : Prop :=
  ∀ v ∈ E, v ≠ 0 → 0 < ⟪v, act H v⟫

/-- `P_E H P_E ⪰ 0`, i.e. `H` is positive semidefinite on `E`. -/
def PSDOn (E : Submodule ℝ (EuclideanSpace ℝ ι)) (H : SymMat ι) : Prop :=
  ∀ v ∈ E, 0 ≤ ⟪v, act H v⟫

/-- `rb C := C \ ri C`, the relative boundary of a closed set. -/
def relBdry (s : Set (SymMat ι)) : Set (SymMat ι) := s \ intrinsicInterior ℝ s

/-- The kernel-supported PSD cone `K(E) := {W ∈ S^p_+ : ran W ⊆ E}` (§C.4, p.19), used with
`E = K_X̄` and `E = K_S̄`. -/
def kerCone (E : Submodule ℝ (EuclideanSpace ℝ ι)) : Set (SymMat ι) :=
  {W | W ∈ psdCone ι ∧ ranSub W ≤ E}

/-- The Frobenius norm `‖M‖_F := (Σ_{i,j} M_ij²)^{1/2}` of a rectangular real matrix. -/
def frob {m n : Type} [Fintype m] [Fintype n] (M : Matrix m n ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, M i j ^ 2)

/-- The operator norm `‖X‖_op` of a symmetric matrix acting on `(ℝ^p, ‖·‖₂)` (Appendix C). -/
def opNorm (X : SymMat ι) : ℝ := ‖LinearMap.toContinuousLinearMap (act X)‖

/-- The Sylvester operator `Syl : Y ↦ AY + σYB` on `r × s` matrices (Lemma C.3, (3.5)). -/
def sylv {r s : ℕ} (σ : ℝ) (A : Matrix (Fin r) (Fin r) ℝ) (B : Matrix (Fin s) (Fin s) ℝ)
    (Y : Matrix (Fin r) (Fin s) ℝ) : Matrix (Fin r) (Fin s) ℝ :=
  A * Y + σ • (Y * B)

/-- The block `H_EF := B_E^⊤ H B_F` of `H ∈ S^p` in fixed orthonormal bases `B_E`, `B_F` of the
subspaces `E`, `F` (Appendix C, "Blocks"). -/
def blk {E F : Submodule ℝ (EuclideanSpace ℝ ι)} {r s : ℕ}
    (bE : OrthonormalBasis (Fin r) ℝ E) (bF : OrthonormalBasis (Fin s) ℝ F) (H : SymMat ι) :
    Matrix (Fin r) (Fin s) ℝ :=
  fun i j => ⟪(bE i : EuclideanSpace ℝ ι), act H (bF j : EuclideanSpace ℝ ι)⟫

namespace SDPData

variable (D : SDPData ι κ)

/-- Assumption 3.1 (two-sided optimal geometry), p.6, for the anchor pair `(X_sc, S_sc)`:
`X_⋆` and `S_⋆` are nonempty and compact, `(X_sc, S_sc)` is an optimal pair with
`X_sc S_sc = 0`, `X_sc + S_sc ≻ 0`, and `1 ≤ rank X_sc < p`. -/
def Assumption31 (Xsc Ssc : SymMat ι) : Prop :=
  D.Xstar.Nonempty ∧ IsCompact D.Xstar ∧ D.Sstar.Nonempty ∧ IsCompact D.Sstar ∧
    Xsc ∈ D.Xstar ∧ Ssc ∈ D.Sstar ∧ Xsc.toMat * Ssc.toMat = 0 ∧
    (Xsc + Ssc).toMat.PosDef ∧ 1 ≤ Xsc.toMat.rank ∧ Xsc.toMat.rank < Fintype.card ι

/-- The primal direction space `M := N ∩ S(U)`, `U = ran X_sc` (3.3). -/
def Mdir (Xsc : SymMat ι) : Submodule ℝ (SymMat ι) := D.nullSpace ⊓ supported (ranSub Xsc)

/-- The dual direction space `L := R ∩ S(V)`, `V = ran S_sc` (3.3). -/
def Ldir (Ssc : SymMat ι) : Submodule ℝ (SymMat ι) := D.rowSpace ⊓ supported (ranSub Ssc)

/-- `D := M ⊕ L` (3.3) (the sum is direct because `S(U) ⊥ S(V)`). -/
def Ddir (Xsc Ssc : SymMat ι) : Submodule ℝ (SymMat ι) := D.Mdir Xsc ⊔ D.Ldir Ssc

/-- The primal identity of (3.8) at `S̄`:
`{E ∈ N : P_V E P_V = 0, E S̄ = 0} = M`. -/
def PrimalIdentity (Xsc Ssc Sbar : SymMat ι) : Prop :=
  {E : SymMat ι | E ∈ D.nullSpace ∧
      projMat (ranSub Ssc) * E.toMat * projMat (ranSub Ssc) = 0 ∧ E.toMat * Sbar.toMat = 0} =
    (D.Mdir Xsc : Set (SymMat ι))

/-- The dual identity of (3.8) at `X̄`:
`{F ∈ R : P_U F P_U = 0, X̄ F = 0} = L`. -/
def DualIdentity (Xsc Ssc Xbar : SymMat ι) : Prop :=
  {F : SymMat ι | F ∈ D.rowSpace ∧
      projMat (ranSub Xsc) * F.toMat * projMat (ranSub Xsc) = 0 ∧ Xbar.toMat * F.toMat = 0} =
    (D.Ldir Ssc : Set (SymMat ι))

/-- Condition (i) of Theorem 3.2: `μ_ri > 0` (3.7). -/
def CondI (σ : ℝ) (Xsc Ssc : SymMat ι) : Prop :=
  ∃ μ > (0 : ℝ), ∀ Zbar ∈ intrinsicInterior ℝ (D.Zstar σ), ∀ H ∈ (D.Ddir Xsc Ssc)ᗮ,
    ‖H‖ = 1 → ∃ d, NonsmoothNewton.Local.HasDirDerivAt (D.delta σ) Zbar H d ∧ μ ≤ ‖d‖

/-- Condition (ii) of Theorem 3.2: the primal identity of (3.8) at every `S̄ ∈ rb S_⋆` and the
dual identity at every `X̄ ∈ rb X_⋆`. -/
def CondII (Xsc Ssc : SymMat ι) : Prop :=
  (∀ Sbar ∈ relBdry D.Sstar, D.PrimalIdentity Xsc Ssc Sbar) ∧
    ∀ Xbar ∈ relBdry D.Xstar, D.DualIdentity Xsc Ssc Xbar

/-- Condition (iii) of Theorem 3.2: the setwise error bound (3.9). -/
def CondIII (σ : ℝ) : Prop := D.ErrorBound σ

/-- Condition (iv) of Theorem 3.2: `μ_nor > 0` (3.7), over the normal cones `N_{Z_⋆}(Z̄)`. -/
def CondIV (σ : ℝ) : Prop :=
  ∃ μ > (0 : ℝ), ∀ Zbar ∈ D.Zstar σ, ∀ H ∈ RobinsonSR.Reduction.normalCone (D.Zstar σ) Zbar,
    ‖H‖ = 1 → ∃ d, NonsmoothNewton.Local.HasDirDerivAt (D.delta σ) Zbar H d ∧ μ ≤ ‖d‖

/-- Condition (v) of Theorem 3.2: `C(Z̄) = T_{Z_⋆}(Z̄)` for every `Z̄ ∈ rb Z_⋆`. -/
def CondV (σ : ℝ) : Prop :=
  ∀ Zbar ∈ relBdry (D.Zstar σ),
    D.stallCone σ Zbar = SunNLSDP.Equiv.tangentCone (D.Zstar σ) Zbar

end SDPData

end

end BenignDegen


