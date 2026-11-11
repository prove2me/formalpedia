-- Prove2me | Definitions.Def_HigherOrderId_Certify_TallCompletion
-- name    : HigherOrderId_Certify_TallCompletion
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:17:25.336933+00:00
-- url     : https://prove2.me/theorems/d21a5bcd-f8e4-42b8-95b6-9f8ee93768c0
-- title:
--   Tall completion: the rest space R_{U,V}, D_rest, M = D_U^† D_rest, L, the completion estimator of (55) and its covariance
-- statement:
--   Let $[U,V]$ be a $d\times d$ orthogonal matrix, $U$ of size $d\times m$ and $V$ ($=V_{\mathrm{env}}$) of size $d\times k$. Relative to $\mathrm{Sym}_d=\{UBU^\top:B\in\mathrm{Sym}_m\}\oplus R_{U,V}$ (71), the **rest space** $R_{U,V}$ holds the $UV$, $VU$ and $VV$ blocks: the symmetric $X$ with $U^\top XU=0$. It has the orthonormal basis $(u_iv_l^\top+v_lu_i^\top)/\sqrt2$, $v_lv_l^\top$, $(v_lv_{l'}^\top+v_{l'}v_l^\top)/\sqrt2$ ($l<l'$). Diagonal extraction $D$ splits as $(D_U,D_{\mathrm{rest}})$; the adjoints are $D_U^*(y)=U^\top\operatorname{Diag}(y)U$ and $D_{\mathrm{rest}}^*(y)=\operatorname{Diag}(y)-UU^\top\operatorname{Diag}(y)UU^\top$.
--
--   With $D_U$ of full column rank and $D_U^\dagger=(D_U^*D_U)^{-1}D_U^*$, put $M=D_U^\dagger D_{\mathrm{rest}}$ and $L(r)=r-U\,M(r)\,U^\top$.
--
--   The centered gradient channel (55) observes $\widehat M_g=QV+\sqrt{v_N}Z\in\mathbb R^{d\times k}$ with $Z$ standard Gaussian entries. The **linear completion** rebuilds the rest block
--   $$\hat r=U(U^\top\widehat M_g)V^\top+V(U^\top\widehat M_g)^\top U^\top+V\operatorname{sym}(V^\top\widehat M_g)V^\top,\qquad \operatorname{sym}(A)=\tfrac12(A+A^\top),$$
--   applies $L$ and projects orthogonally onto $S^d_0$: $\widehat Q=P_0L(\hat r)$. Since $\widehat Q$ is linear in $\widehat M_g$, its noise is $\sqrt{v_N}\,K(Z)$ for the linear map $K:\widehat M_g\mapsto\widehat Q$, and its noise covariance is $\Gamma_{U,V}=v_NKK^*$. The explicit estimator of $\vartheta$ in coordinates (99) pairs $\widehat Q_{ij}$ ($i<j$) with the independent $\hat b=b+(\sigma/\sqrt N)z_b$, so its covariance $\Gamma$ is block diagonal with blocks $(\sigma^2/N)I_d$ and $(\operatorname{Cov}(\widehat Q_{ij},\widehat Q_{i'j'}))$.
--
--   **Formalization Note.** `MMadj U V` is the matrix of $MM^*$ on $\mathrm{Sym}_m$ in its orthonormal basis, computed as $\sum_s M(\rho_s)M(\rho_s)^\top$ over the orthonormal basis $\rho_s$ of $R_{U,V}$; `LsqSpec U V` are the eigenvalues of $L^*L$ on $R_{U,V}$ (Gram matrix of the $L(\rho_s)$). `GammaEntry U V v = v • K Kᵀ` is the covariance of the entries of $\widehat Q$ (an operator on $\mathbb R^{d\times d}$ that vanishes off $S^d_0$, so its trace and the trace of its square are those of $\Gamma_{U,V}$ on $S^d_0$). `GammaTheta` assembles $\Gamma$ in coordinates (99). `P0` is the Frobenius projection onto $S^d_0$.
-- source:
--   Zhang, Yan, Qiao, Yu, The Higher-Order Identifiability Paradox: Learning and Certifying Hypergraph Order, STOC 2027 submission (manuscript sha256 7e0ce916…), pp. 24–25, Eqs. (55), (71)–(76), Lemma B.5; p. 21 (estimator of b); p. 31, Eq. (101)

import Mathlib
import Definitions.Def_HigherOrderId_Certify_Model
import Definitions.Def_HigherOrderId_Certify_Completion

open Matrix

namespace HigherOrderId.Certify

/-!
# Tall completion: the rest space, D_rest, M = D_U^† D_rest, L, the linear completion estimator
and its noise covariance

Zhang, Yan, Qiao, Yu, *The Higher-Order Identifiability Paradox: Learning and Certifying
Hypergraph Order*, STOC 2027 submission (manuscript sha256 7e0ce916…), pp. 24–25, Eqs. (55),
(71)–(76), Lemma B.5; p. 31, Eq. (101) and the estimator of `b` (p. 21).

Throughout, `U` is `d × m` and `V` (the paper's `V_env`) is `d × k`, with `[U, V]` orthogonal.
All matrix spaces carry the Frobenius inner product.

* `Sym_d = {U B Uᵀ : B ∈ Sym_m} ⊕ R_{U,V}`, where `R_{U,V}` holds the `UV`, `VU` and `VV` blocks.
  `InRest U X` says `X ∈ R_{U,V}`: `X` is symmetric and `Uᵀ X U = 0`.
  `restBasis U V` is the orthonormal basis of `R_{U,V}` indexed by
  `RestIdx m k = (Fin m × Fin k) ⊕ {(l, l') : l ≤ l'}`:
  `(u_i v_lᵀ + v_l u_iᵀ)/√2`, `v_l v_lᵀ`, and `(v_l v_l'ᵀ + v_l' v_lᵀ)/√2` for `l < l'`.
  So `dim R_{U,V} = card (RestIdx m k)` and `t = card (SymIdx m)`.
* `D` is diagonal extraction `X ↦ diagVec X`; `D_rest` is its restriction to `R_{U,V}`.
  The adjoints are `D_U*(y) = Uᵀ Diag(y) U` and `D_rest*(y) = Diag(y) − U Uᵀ Diag(y) U Uᵀ`
  (orthogonal projection of `Diag(y)` onto `R_{U,V}`).
* `Mc U X` are the `symBasis` coordinates of `M(X) = D_U^† D_rest(X)`, with
  `D_U^† = (D_U* D_U)⁻¹ D_U*` (the Moore–Penrose pseudo-inverse under full column rank).
  `L(X) = X − U M(X) Uᵀ`.
* `MMadj U V` is the matrix of `M M*` on `Sym_m` (orthonormal coordinates), computed as
  `Σ_s M(ρ_s) M(ρ_s)ᵀ` over the orthonormal basis `ρ_s` of `R_{U,V}`. `LGram U V` is the
  matrix of `L* L` on `R_{U,V}` in the basis `ρ_s`.
* The completion estimator from the centered channel (55) `M̂_g = Q V + √v_N Z ∈ ℝ^{d×k}`:
  the rest block is rebuilt from `Uᵀ M̂_g` and `sym(Vᵀ M̂_g)` as
  `r̂ = U (Uᵀ M̂_g) Vᵀ + V (Uᵀ M̂_g)ᵀ Uᵀ + V sym(Vᵀ M̂_g) Vᵀ`, then `L` is applied and the result
  is projected orthogonally (Frobenius) onto `S^d_0` by `P0`.
* `Qhat U V` is linear in `M̂_g`, so `Q̂ − Q = √v_N · Qhat U V Z` for every `Q` it reproduces.
  `noiseMap U V` is its matrix (columns `Qhat U V E_{al}` for the standard basis `E_{al}` of
  `ℝ^{d×k}`), and, since `Z` has independent standard normal entries, the noise covariance of
  `Q̂` is `GammaEntry U V v_N = v_N · K Kᵀ`, as an operator on `ℝ^{d×d} ⊇ S^d_0`
  (it vanishes on the orthocomplement of `S^d_0`, so its trace and the trace of its square are
  those of `Γ_{U,V}` on `S^d_0`).
* `GammaTheta U V σ N v_N` is the covariance of the explicit estimator of
  `ϑ = (b, {Q_ij}_{i<j})` (coordinates (99)): `b̂ = b + (σ/√N) z_b` (covariance `(σ²/N) I_d`,
  independent of `Q̂`) together with the entries `Q̂_ij`, `i < j`.
-/

/-- Index set of the orthonormal basis of the rest space `R_{U,V}`. -/
abbrev RestIdx (m k : ℕ) := (Fin m × Fin k) ⊕ {p : Fin k × Fin k // p.1 ≤ p.2}

/-- The symmetric outer product `x_i y_lᵀ + y_l x_iᵀ` of column `i` of `X` and column `l` of `Y`. -/
def colOuterSym {d a b : ℕ} (X : Matrix (Fin d) (Fin a) ℝ) (Y : Matrix (Fin d) (Fin b) ℝ)
    (i : Fin a) (l : Fin b) : Matrix (Fin d) (Fin d) ℝ :=
  fun r s => X r i * Y s l + Y r l * X s i

/-- The orthonormal basis of `R_{U,V}`. -/
noncomputable def restBasis {d m k : ℕ} (U : Matrix (Fin d) (Fin m) ℝ)
    (V : Matrix (Fin d) (Fin k) ℝ) : RestIdx m k → Matrix (Fin d) (Fin d) ℝ
  | .inl c => (1 / Real.sqrt 2) • colOuterSym U V c.1 c.2
  | .inr p => if p.1.1 = p.1.2 then (fun r s => V r p.1.1 * V s p.1.1)
      else (1 / Real.sqrt 2) • colOuterSym V V p.1.1 p.1.2

/-- `X ∈ R_{U,V}`: `X` is symmetric with vanishing `UU` block. -/
def InRest {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (X : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  X.IsSymm ∧ Uᵀ * X * U = 0

/-- Diagonal extraction `D(X) = diag(X)`. -/
def diagVec {d : ℕ} (X : Matrix (Fin d) (Fin d) ℝ) : Fin d → ℝ := fun a => X a a

/-- The adjoint `D_U*(y) = Uᵀ Diag(y) U ∈ Sym_m`. -/
def DUadj {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (y : Fin d → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Uᵀ * Matrix.diagonal y * U

/-- The adjoint `D_rest*(y)`: the orthogonal projection of `Diag(y)` onto `R_{U,V}`. -/
def DrestAdj {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (y : Fin d → ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.diagonal y - U * (Uᵀ * Matrix.diagonal y * U) * Uᵀ

/-- Coordinates (in `symBasis`) of `M(X) = D_U^† D_rest(X)`, `D_U^† = (D_U* D_U)⁻¹ D_U*`. -/
noncomputable def Mc {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (X : Matrix (Fin d) (Fin d) ℝ) :
    SymIdx m → ℝ :=
  ((DUmat U)ᴴ * DUmat U)⁻¹ *ᵥ ((DUmat U)ᴴ *ᵥ diagVec X)

/-- `M(X) ∈ Sym_m` as a matrix. -/
noncomputable def Mmap {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (X : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  ∑ p, Mc U X p • symBasis p

/-- The graph map `L(X) = X − U M(X) Uᵀ`. -/
noncomputable def Lmap {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (X : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  X - U * Mmap U X * Uᵀ

/-- The matrix of `M M*` on `Sym_m` in the orthonormal basis `symBasis`. -/
noncomputable def MMadj {d m k : ℕ} (U : Matrix (Fin d) (Fin m) ℝ)
    (V : Matrix (Fin d) (Fin k) ℝ) : Matrix (SymIdx m) (SymIdx m) ℝ :=
  ∑ s, vecMulVec (Mc U (restBasis U V s)) (Mc U (restBasis U V s))

/-- The entries of `L(ρ_s)`, one column per basis element `ρ_s` of `R_{U,V}`. -/
noncomputable def Lcols {d m k : ℕ} (U : Matrix (Fin d) (Fin m) ℝ)
    (V : Matrix (Fin d) (Fin k) ℝ) : Matrix (Fin d × Fin d) (RestIdx m k) ℝ :=
  fun p s => Lmap U (restBasis U V s) p.1 p.2

/-- The matrix of `L* L` on `R_{U,V}` in the orthonormal basis `restBasis`. -/
noncomputable def LGram {d m k : ℕ} (U : Matrix (Fin d) (Fin m) ℝ)
    (V : Matrix (Fin d) (Fin k) ℝ) : Matrix (RestIdx m k) (RestIdx m k) ℝ :=
  (Lcols U V)ᴴ * Lcols U V

/-- The squared singular values of `L` (eigenvalues of `L* L`), indexed by `RestIdx m k`. -/
noncomputable def LsqSpec {d m k : ℕ} (U : Matrix (Fin d) (Fin m) ℝ)
    (V : Matrix (Fin d) (Fin k) ℝ) : RestIdx m k → ℝ :=
  (Matrix.isHermitian_conjTranspose_mul_self (Lcols U V)).eigenvalues

/-- Orthogonal (Frobenius) projection of a `d × d` matrix onto `S^d_0`. -/
noncomputable def P0 {d : ℕ} (X : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => if i = j then 0 else (X i j + X j i) / 2

/-- The rest block rebuilt from `Uᵀ M̂_g` and `sym(Vᵀ M̂_g)`. -/
noncomputable def rhat {d m k : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin k) ℝ)
    (Mg : Matrix (Fin d) (Fin k) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  U * (Uᵀ * Mg) * Vᵀ + V * (Uᵀ * Mg)ᵀ * Uᵀ +
    V * ((1 / 2 : ℝ) • (Vᵀ * Mg + (Vᵀ * Mg)ᵀ)) * Vᵀ

/-- The linear completion `Q̂ = P0(L(r̂))` of Lemma B.5, as a function of `M̂_g`. -/
noncomputable def Qhat {d m k : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin k) ℝ)
    (Mg : Matrix (Fin d) (Fin k) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  P0 (Lmap U (rhat U V Mg))

/-- The matrix `K` of the linear map `M̂_g ↦ Q̂` (entries of `Q̂` against entries of `M̂_g`). -/
noncomputable def noiseMap {d m k : ℕ} (U : Matrix (Fin d) (Fin m) ℝ)
    (V : Matrix (Fin d) (Fin k) ℝ) : Matrix (Fin d × Fin d) (Fin d × Fin k) ℝ :=
  fun p c => Qhat U V (Matrix.single c.1 c.2 1) p.1 p.2

/-- The noise covariance `Γ_{U,V} = v_N K Kᵀ` of `Q̂` (entries of `Q̂`). -/
noncomputable def GammaEntry {d m k : ℕ} (U : Matrix (Fin d) (Fin m) ℝ)
    (V : Matrix (Fin d) (Fin k) ℝ) (v : ℝ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℝ :=
  v • (noiseMap U V * (noiseMap U V)ᵀ)

/-- The covariance of the explicit estimator `(b̂, Q̂)` of `ϑ` in the coordinates (99):
`(σ²/N) I_d` on the `b` block, `Cov(Q̂_ij, Q̂_i'j')` on the `Q_ij` (`i < j`) block, zero
across. -/
noncomputable def GammaTheta {d m k : ℕ} (U : Matrix (Fin d) (Fin m) ℝ)
    (V : Matrix (Fin d) (Fin k) ℝ) (σ : ℝ) (N : ℕ) (v : ℝ) :
    Matrix (ThetaIdx d) (ThetaIdx d) ℝ
  | .inl i, .inl i' => if i = i' then σ ^ 2 / (N : ℝ) else 0
  | .inr p, .inr q => GammaEntry U V v p.1 q.1
  | .inl _, .inr _ => 0
  | .inr _, .inl _ => 0

end HigherOrderId.Certify


