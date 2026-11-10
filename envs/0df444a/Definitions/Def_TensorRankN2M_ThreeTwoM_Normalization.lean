-- Prove2me | Definitions.Def_TensorRankN2M_ThreeTwoM_Normalization
-- name    : TensorRankN2M_ThreeTwoM_Normalization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:16:14.599836+00:00
-- url     : https://prove2.me/theorems/0f1ebfaa-427e-4521-aa94-4ef0ba3244f8
-- title:
--   The maps D, ℬ, W, the change of basis, the maps f_i and strong normalization of a decomposition (§2, §3)
-- statement:
--   Fix an $R$-rank decomposition $(\alpha_r,\beta_r,C_r)_{0\le r<R}$ of $\langle k,l,m\rangle$ over a field $\mathbb F$. Define
--   $$D(A)=\operatorname{diag}(\alpha_0(A),\dots,\alpha_{R-1}(A))\in\mathbb F^{R\times R},\qquad \mathcal B(B)=(\beta_0(B),\dots,\beta_{R-1}(B))\in\mathbb F^R,\qquad W(t)=\sum_r t_r C_r\in\mathbb F^{k\times m}$$
--   for $A\in\mathbb F^{k\times l}$, $B\in\mathbb F^{l\times m}$, $t\in\mathbb F^R$; the decomposition equation reads $AB=W\,D(A)\,\mathcal B(B)$.
--
--   For invertible $S\in\mathbb F^{k\times k}$ and $T\in\mathbb F^{l\times l}$, the **change of basis** is the decomposition
--   $$(\alpha'_r(A),\beta'_r(B),C'_r)=(\alpha_r(S^{-1}AT),\ \beta_r(T^{-1}B),\ SC_r),$$
--   again an $R$-rank decomposition of $\langle k,l,m\rangle$.
--
--   Let $e_{i,j}$ be the matrix with a single $1$ at position $(i,j)$ (indices start at $0$; its shape is read from context). For $0\le i<k$ define $f_i(x)=D(e_{i,0})\,\mathcal B(x)\in\mathbb F^R$ for $x\in\mathbb F^{l\times m}$, where $e_{i,0}$ has shape $k\times l$. The decomposition is **strongly normalized** if
--   $$\forall v\in\mathbb F^{l\times m},\ v\neq 0:\ \{f_i(v):0\le i<k\}\ \text{is linearly independent, and } D(e_{0,0})\ \text{is invertible.}$$
--
--   These maps turn statements about the decomposition into linear algebra in $\mathbb F^R$; strong normalization is the normal form that the paper's lower-bound arguments start from.
--
--   **Formalization Note.** `D`, `Bvec` ($\mathcal B$), `W`, `changeBasis`, `f` and `StronglyNormalized` are in namespace `Decomposition`. $S,T$ are elements of `GL (Fin k) 𝔽`, `GL (Fin l) 𝔽`; `sandwich P Q` is the linear map $A\mapsto PAQ$ (so $\beta'_r(B)=\beta_r(T^{-1}B\cdot 1)$). $e_{i,j}$ is `Matrix.single i j 1`. "Linearly independent" is `LinearIndependent` of the family $i\mapsto f_i(v)$, which also excludes repetitions. `f` needs `[NeZero l]` and `StronglyNormalized` needs `[NeZero k] [NeZero l]` so that the index $0$ exists.
-- source:
--   Jason Yang, New lower bounds on tensor rank of (n,2,m) matrix multiplication with GPT-6 Astra, STOC 2027 submission (manuscript of October 2026, sha256 6c1df229…), p. 2, §2 (D, ℬ, W); p. 3 (change of basis, e_{i,j}, f_i); p. 4, §3, Lemma 6 (strong normalization)

import Mathlib
import Definitions.Def_TensorRankN2M_ThreeTwoM_Decomposition

/-!
# The maps D, ℬ, W, the change of basis, the maps f_i and strong normalization

Jason Yang, *New lower bounds on tensor rank of (n,2,m) matrix multiplication with GPT-6 Astra*,
STOC 2027 submission (manuscript of October 2026), p. 2 (§2: D, ℬ, W), p. 3 (change of basis,
`e_{i,j}`, `f_i`), p. 4 (§3: strong normalization, Lemma 6).

* `D d A = diag(α_0(A), …, α_{R-1}(A))`, `Bvec d B = (β_0(B), …, β_{R-1}(B))`,
  `W d t = ∑_r t_r C_r`; the decomposition equation reads `AB = W D(A) ℬ(B)`.
* `changeBasis d S T` is `(α_r(S⁻¹AT), β_r(T⁻¹B), S C_r)` for invertible `S`, `T` (p. 3).
* `e_{i,j}` is `Matrix.single i j 1`, the 1-hot matrix; indices are 0-based (`Fin`).
* `f d i x = D(e_{i,0}) ℬ(x)` for `i : Fin k` (`e_{i,0}` of shape `k×l`; needs `l ≥ 1`).
* `StronglyNormalized d`: for every nonzero `v ∈ 𝔽^{l×m}` the family `(f_i(v))_{0≤i<k}` is
  linearly independent, and `D(e_{0,0})` is invertible (needs `k, l ≥ 1`).
-/

namespace TensorRankN2M.ThreeTwoM

namespace Decomposition

variable {𝔽 : Type*} [Field 𝔽] {k l m R : ℕ}

/-- `D(A) = diag(α_0(A), …, α_{R-1}(A))`, an `R × R` diagonal matrix (p. 2). -/
def D (d : Decomposition 𝔽 k l m R) (A : Matrix (Fin k) (Fin l) 𝔽) : Matrix (Fin R) (Fin R) 𝔽 :=
  Matrix.diagonal fun r => d.α r A

/-- `ℬ(B) = (β_0(B), …, β_{R-1}(B)) ∈ 𝔽^R` (p. 2). -/
def Bvec (d : Decomposition 𝔽 k l m R) : Matrix (Fin l) (Fin m) 𝔽 →ₗ[𝔽] (Fin R → 𝔽) :=
  LinearMap.pi d.β

/-- `W(t) = ∑_r t_r C_r` for `t ∈ 𝔽^R` (p. 2). -/
def W (d : Decomposition 𝔽 k l m R) : (Fin R → 𝔽) →ₗ[𝔽] Matrix (Fin k) (Fin m) 𝔽 :=
  Fintype.linearCombination 𝔽 d.C

/-- The linear map `A ↦ P * A * Q` on matrices (used by the change of basis). -/
def sandwich {a b c e : ℕ} (P : Matrix (Fin a) (Fin b) 𝔽) (Q : Matrix (Fin c) (Fin e) 𝔽) :
    Matrix (Fin b) (Fin c) 𝔽 →ₗ[𝔽] Matrix (Fin a) (Fin e) 𝔽 where
  toFun A := P * A * Q
  map_add' A A' := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c A := by simp [Matrix.mul_smul, Matrix.smul_mul]

/-- The change of basis `(α'_r(A), β'_r(B), C'_r) = (α_r(S⁻¹AT), β_r(T⁻¹B), S C_r)` for invertible
`S ∈ 𝔽^{k×k}`, `T ∈ 𝔽^{l×l}` (p. 3); it is again an `R`-rank decomposition of ⟨k,l,m⟩. -/
def changeBasis (d : Decomposition 𝔽 k l m R) (S : GL (Fin k) 𝔽) (T : GL (Fin l) 𝔽) :
    Decomposition 𝔽 k l m R where
  α r := (d.α r).comp (sandwich (↑S⁻¹ : Matrix (Fin k) (Fin k) 𝔽) (↑T : Matrix (Fin l) (Fin l) 𝔽))
  β r := (d.β r).comp (sandwich (↑T⁻¹ : Matrix (Fin l) (Fin l) 𝔽) (1 : Matrix (Fin m) (Fin m) 𝔽))
  C r := (↑S : Matrix (Fin k) (Fin k) 𝔽) * d.C r
  eq A B := by
    have h := d.eq ((↑S⁻¹ : Matrix (Fin k) (Fin k) 𝔽) * A * (↑T : Matrix (Fin l) (Fin l) 𝔽))
      ((↑T⁻¹ : Matrix (Fin l) (Fin l) 𝔽) * B * (1 : Matrix (Fin m) (Fin m) 𝔽))
    have key : (↑S⁻¹ : Matrix (Fin k) (Fin k) 𝔽) * A * (↑T : Matrix (Fin l) (Fin l) 𝔽) *
        ((↑T⁻¹ : Matrix (Fin l) (Fin l) 𝔽) * B * (1 : Matrix (Fin m) (Fin m) 𝔽)) =
          (↑S⁻¹ : Matrix (Fin k) (Fin k) 𝔽) * (A * B) := by
      rw [Matrix.mul_one, Matrix.mul_assoc _ (↑T : Matrix (Fin l) (Fin l) 𝔽),
        ← Matrix.mul_assoc (↑T : Matrix (Fin l) (Fin l) 𝔽), Units.mul_inv, Matrix.one_mul,
        Matrix.mul_assoc]
    calc A * B = (↑S : Matrix (Fin k) (Fin k) 𝔽) *
          ((↑S⁻¹ : Matrix (Fin k) (Fin k) 𝔽) * (A * B)) := by
          rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      _ = _ := by
          rw [← key, h, Matrix.mul_sum]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Matrix.mul_smul]
          rfl

/-- `f_i(x) = D(e_{i,0}) ℬ(x)` for `0 ≤ i < k` and `x ∈ 𝔽^{l×m}` (p. 3; `e_{i,0}` has shape
`k × l`). -/
def f [NeZero l] (d : Decomposition 𝔽 k l m R) (i : Fin k) :
    Matrix (Fin l) (Fin m) 𝔽 →ₗ[𝔽] (Fin R → 𝔽) :=
  (d.D (Matrix.single i 0 1)).mulVecLin ∘ₗ d.Bvec

/-- Strong normalization (p. 4, Lemma 6): for every nonzero `v ∈ 𝔽^{l×m}`,
`{f_i(v) : 0 ≤ i < k}` is linearly independent, and `D(e_{0,0})` is invertible. -/
def StronglyNormalized [NeZero k] [NeZero l] (d : Decomposition 𝔽 k l m R) : Prop :=
  (∀ v : Matrix (Fin l) (Fin m) 𝔽, v ≠ 0 → LinearIndependent 𝔽 fun i : Fin k => d.f i v) ∧
    IsUnit (d.D (Matrix.single 0 0 1))

end Decomposition

end TensorRankN2M.ThreeTwoM


