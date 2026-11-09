-- Prove2me | Definitions.Def_WalkTreeCluster_Filter
-- name    : WalkTreeCluster_Filter
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:48:42.711541+00:00
-- url     : https://prove2.me/theorems/5f774b76-3823-486a-a5fb-58f03d18f261
-- title:
--   The filter $F_i$ and the diagonal matrices $D_j$ (Eq. (10), Definition 2.8)
-- statement:
--   Let $D_0=I$ and $D_j=(1-\delta)\operatorname{diag}_{z\in V}\big(\mathbb E[\mathrm{Keep}(z,j-1)]\big)$ for $j\ge1$. The low-pass and high-pass factors are (Eq. (10))
--   $$A_j(L)=D_jM^t,\qquad A_j(H)=I-\sum_{s\ge1}d_s\,[A_j(L)]^{2s}.$$
--   The filter $F_i$ maps $f\in\mathbb R^V$ to the matrix with rows (Eq. (16))
--   $$(F_if)(\sigma,\cdot)^\top=A_1(\sigma_1)\cdots A_i(\sigma_i)f\qquad(\sigma\in\{L,H\}^i),\qquad F_0=I .$$
--   Also $D_j^{1/2}$ is the diagonal matrix of square roots, and $K_i=D_i^{1/2}M^tD_i^{1/2}$.
--
--   $F_i$ is the target that the walk tree samples without bias (Lemma 6.4); its inner products $\langle F_i\mathbb 1_u,F_i\mathbb 1_v\rangle_w$ are what the classifier estimates.
--
--   **Formalization Note.** The root letter $\sigma_i$ selects $A_i$, applied first; $A_1(\sigma_1)$ is applied last. $A_j(H)$ is the matrix series, not a matrix square root ($D_jM^t$ is not symmetric); the sanity files prove that $\sum_s d_s=1$ and that the series converges whenever the powers of $D_jM^t$ have entries in $[-1,1]$.
-- source:
--   Kapralov–Kochetkova, Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise, STOC 2027 submission (manuscript sha256 638eeef1…), Eq. (10), p.10; Definition 2.8, Eq. (16), p.12; Table 1 ($D_j$), p.18; Section 7.1 ($K_i$), p.37

import Mathlib
import Definitions.Def_WalkTreeCluster_Laws

open MeasureTheory

namespace WalkTreeCluster

/-!
# The filter `F_i` and the diagonal matrices `D_j`

Kapralov–Kochetkova, *Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise*, STOC 2027
submission (manuscript sha256 638eeef1…), Eq. (10), p.10; Definition 2.8, Eq. (16), p.12; Table 1,
p.18 (`D_j`); `K_i = D_i^{1/2} M^t D_i^{1/2}`, Section 7.1, p.37.

`D_0 = I` and `D_j = (1 − δ) diag_{z ∈ V}(E[Keep(z, j − 1)])` for `j ≥ 1`;
`A_j(L) = D_j M^t`, `A_j(H) = I − Σ_{s ≥ 1} d_s [A_j(L)]^{2s}`; and `F_i f` has rows
`(F_i f)(σ, ·)ᵀ = A_1(σ_1) ⋯ A_i(σ_i) f` for `σ ∈ {L, H}^i`, `F_0 = I`.

**Formalization Note.**
* With the filter path convention of the filter-paths module, `σ_k` is `σ ⟨k − 1, _⟩`. The root
  letter `σ_i` selects `A_i`, which is applied **first** (rightmost), and `A_1(σ_1)` is applied last.
  The recursion is `(F_{j+1} f)(σ) = (F_j (A_{j+1}(σ_{j+1}) f))(σ_1 ⋯ σ_j)`.
* `A_j(H)` is the matrix series of Eq. (10) (a `tsum` in `Matrix`), not a matrix square root:
  `D_j M^t` is not symmetric. The series converges since `Σ d_s = 1` and every entry of
  `(D_j M^t)^{2s}` lies in `[0, 1]`.
* `E[Keep(z, j − 1)]` is the Bochner integral of the identity under `keepLaw (j − 1) z`.
* `Dsqrt j` is the diagonal matrix of the square roots of the diagonal entries of `D_j`
  (`D_j^{1/2}`; the entries are in `[0, 1]`).
-/

/-- `E[Keep(z, j)]`. -/
noncomputable def meanKeep {n d : ℕ} (nbr : Fin n → Fin d → Fin n) (ϵ ϕ : ℝ) (j : ℕ) (z : Fin n) :
    ℝ :=
  ∫ x, x ∂(keepLaw nbr ϵ ϕ j z)

/-- `D_0 = I`, `D_j = (1 − δ) diag(E[Keep(z, j − 1)])` for `j ≥ 1` (Table 1). -/
noncomputable def Ddiag {n d : ℕ} (nbr : Fin n → Fin d → Fin n) (ϵ ϕ : ℝ) (j : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  if j = 0 then 1
  else Matrix.diagonal (fun z => (1 - deltaParam ϵ ϕ) * meanKeep nbr ϵ ϕ (j - 1) z)

/-- `D_j^{1/2}`. -/
noncomputable def Dsqrt {n d : ℕ} (nbr : Fin n → Fin d → Fin n) (ϵ ϕ : ℝ) (j : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun z => Real.sqrt (Ddiag nbr ϵ ϕ j z z))

/-- `A_j(L) = D_j M^t`, Eq. (10). -/
noncomputable def lowPass {n d : ℕ} (nbr : Fin n → Fin d → Fin n) (ϵ ϕ : ℝ) (j : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Ddiag nbr ϵ ϕ j * (walkMatrix nbr) ^ tParam ϵ ϕ

/-- `A_j(H) = I − Σ_{s ≥ 1} d_s [A_j(L)]^{2s}`, Eq. (10). -/
noncomputable def highPass {n d : ℕ} (nbr : Fin n → Fin d → Fin n) (ϵ ϕ : ℝ) (j : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  1 - ∑' s : ℕ, seriesCoeff (s + 1) • (lowPass nbr ϵ ϕ j) ^ (2 * (s + 1))

/-- `A_j(b)`: `A_j(L)` for `b = false`, `A_j(H)` for `b = true`. -/
noncomputable def factor {n d : ℕ} (nbr : Fin n → Fin d → Fin n) (ϵ ϕ : ℝ) (j : ℕ) (b : Bool) :
    Matrix (Fin n) (Fin n) ℝ :=
  if b then highPass nbr ϵ ϕ j else lowPass nbr ϵ ϕ j

/-- The filter `F_i`, Eq. (16): `(F_i f)(σ, ·)ᵀ = A_1(σ_1) ⋯ A_i(σ_i) f`, `F_0 = I`. -/
noncomputable def filter {n d : ℕ} (nbr : Fin n → Fin d → Fin n) (ϵ ϕ : ℝ) :
    (i : ℕ) → (Fin n → ℝ) → Mat n i
  | 0, f => fun _ => f
  | j + 1, f => fun σ =>
      filter nbr ϵ ϕ j ((factor nbr ϵ ϕ (j + 1) (σ (Fin.last j))).mulVec f) (Fin.init σ)

/-- `K_i = D_i^{1/2} M^t D_i^{1/2}` (Section 7.1). -/
noncomputable def Kmat {n d : ℕ} (nbr : Fin n → Fin d → Fin n) (ϵ ϕ : ℝ) (i : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Dsqrt nbr ϵ ϕ i * (walkMatrix nbr) ^ tParam ϵ ϕ * Dsqrt nbr ϵ ϕ i

end WalkTreeCluster


