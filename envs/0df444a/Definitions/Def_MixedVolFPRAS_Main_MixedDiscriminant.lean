-- Prove2me | Definitions.Def_MixedVolFPRAS_Main_MixedDiscriminant
-- name    : MixedVolFPRAS_Main_MixedDiscriminant
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:29:50.371709+00:00
-- url     : https://prove2.me/theorems/db7f0a63-ddb9-4502-a1bb-ac012f829f0b
-- title:
--   Mixed discriminant D_{n−1} and the restricted Hessian D²F(θ) on θ^⊥
-- statement:
--   For $m$ matrices $A_1,\dots,A_m\in\mathbb{R}^{m\times m}$ the **mixed discriminant** is
--
--   $$D_m(A_1,\dots,A_m)=\frac{1}{m!}\sum_{\tau,\sigma\in S_m}\mathrm{sign}(\tau)\,\mathrm{sign}(\sigma)\prod_{j=1}^m A_j(\tau(j),\sigma(j)),$$
--
--   equivalently $\frac{1}{m!}\partial_{t_1}\cdots\partial_{t_m}\det(t_1A_1+\dots+t_mA_m)$; the paper uses $m=n-1$.
--
--   For $F:\mathbb{R}^n\setminus\{0\}\to\mathbb{R}$ twice differentiable and $\theta\in S^{n-1}$, write $\theta^\perp=\{x:\langle x,\theta\rangle=0\}$. The **restricted Hessian** $D^2F(\theta)=\nabla^2F(\theta)|_{\theta^\perp}$ is represented, in an orthonormal basis $u_1,\dots,u_{n-1}$ of $\theta^\perp$, by the $(n-1)\times(n-1)$ matrix with entries
--
--   $$D^2F(\theta)_{ab}=\nabla^2F(\theta)[u_a,u_b].$$
--
--   Determinants, mixed discriminants and the Loewner order of these matrices do not depend on the basis (p. 8: "the quantities we use … do not depend on this choice").
--
--   **Formalization Note.** `mixedDiscriminant A` takes `A : Fin m → Matrix (Fin m) (Fin m) ℝ`. `perpBasis θ hθ` is Mathlib's `stdOrthonormalBasis` of `(ℝ ∙ θ)ᗮ`, reindexed by `Fin (n - 1)` (the structural lemma `finrank_perp` gives the dimension). `restrictedHessian F θ a b = fderiv ℝ (fderiv ℝ F) θ (u a) (u b)` for `θ ≠ 0`, and `0` at `θ = 0`. For 1-homogeneous $F$ the Hessian maps $\theta^\perp$ to itself (Euler's identity), so this compression is the paper's $D^2F(\theta)$.
-- source:
--   Chen, Liu, An FPRAS for Mixed Volumes, STOC 2027 submission (manuscript sha256 0acf8d97…), p. 8 (restricted Hessian, Linear Algebra) and p. 9, §2.2 (mixed discriminant)

import Mathlib
import Definitions.Def_MixedVolFPRAS_Main_ConvexGeometry

noncomputable section

namespace MixedVolFPRAS.Main

/-!
# Mixed discriminants and the restricted Hessian `D²F(θ)` on `θ^⊥`

Chen, Liu, *An FPRAS for Mixed Volumes*, p. 8 (restricted Hessian) and p. 9 (mixed discriminant).

* `mixedDiscriminant A = (1/m!) ∑_{τ,σ ∈ S_m} sign τ sign σ ∏_j A_j(τ(j), σ(j))` for `m` matrices
  of size `m × m` (the paper's `D_{n−1}` with `m = n − 1`).
* For `θ ≠ 0` in `ℝⁿ`, `perpBasis θ` is an orthonormal basis of `θ^⊥ = (span θ)^⊥`, indexed by
  `Fin (n − 1)`.
* `restrictedHessian F θ` is the `(n−1) × (n−1)` matrix of the second derivative of `F` at `θ` on
  `θ^⊥` in that basis: entry `(a, b)` is `D²F(θ)[u_a, u_b]`. For a twice differentiable
  1-homogeneous `F` this is the paper's `D²F(θ) = ∇²F(θ)|_{θ^⊥}`; determinants, mixed
  discriminants and the Loewner order of it do not depend on the chosen basis. It is `0` at
  `θ = 0`.
-/

/-- The mixed discriminant `D_m(A₁, …, A_m)` of `m` square matrices of size `m`. -/
def mixedDiscriminant {m : ℕ} (A : Fin m → Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  (1 / (m.factorial : ℝ)) *
    ∑ τ : Equiv.Perm (Fin m), ∑ σ : Equiv.Perm (Fin m),
      ((Equiv.Perm.sign τ : ℤ) : ℝ) * ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ j, A j (τ j) (σ j)

/-- `dim θ^⊥ = n − 1` for `θ ≠ 0` in `ℝⁿ`. -/
theorem finrank_perp {n : ℕ} (θ : E n) (hθ : θ ≠ 0) :
    Module.finrank ℝ (ℝ ∙ θ)ᗮ = n - 1 := by
  have h1 := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ θ)
  rw [finrank_span_singleton hθ, finrank_euclideanSpace_fin] at h1
  omega

/-- An orthonormal basis of `θ^⊥`, indexed by `Fin (n − 1)`. -/
def perpBasis {n : ℕ} (θ : E n) (hθ : θ ≠ 0) : OrthonormalBasis (Fin (n - 1)) ℝ (ℝ ∙ θ)ᗮ :=
  (stdOrthonormalBasis ℝ (ℝ ∙ θ)ᗮ).reindex (finCongr (finrank_perp θ hθ))

/-- The restricted Hessian `D²F(θ)` on `θ^⊥` as an `(n−1) × (n−1)` matrix. -/
def restrictedHessian {n : ℕ} (F : E n → ℝ) (θ : E n) : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ :=
  if hθ : θ ≠ 0 then
    fun a b => fderiv ℝ (fderiv ℝ F) θ ((perpBasis θ hθ a : E n)) ((perpBasis θ hθ b : E n))
  else 0

end MixedVolFPRAS.Main


