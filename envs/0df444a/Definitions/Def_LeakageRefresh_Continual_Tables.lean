-- Prove2me | Definitions.Def_LeakageRefresh_Continual_Tables
-- name    : LeakageRefresh_Continual_Tables
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T23:08:24.003766+00:00
-- url     : https://prove2.me/theorems/a1ce6e18-2f7b-4eac-846b-a96527386ec8
-- title:
--   Tables: probability-normalized inner products and norms, the nuclear norm, orthonormal expansions and truncation, product representations, factor energies, four-cycle averages
-- statement:
--   A **table** is a real function $F(x,y)$ of a row $x\in\alpha$ and a column $y\in\beta$, for finite sets $\alpha,\beta$ (in the paper $U_L\times U_R$ and $U_L^2\times U_R^2$). All averages use the uniform measures (**probability normalization**): $\mathbb E_x[g]=|\alpha|^{-1}\sum_x g(x)$, $\langle a,b\rangle=\mathbb E[ab]$, $\|a\|_2=(\mathbb E[a^2])^{1/2}$, $\langle F,W\rangle=\mathbb E_{x,y}[F W]$, $\|F\|_2=(\mathbb E_{x,y}[F^2])^{1/2}$, with $x,y$ independent. A **product table** is $a\cdot b^T:(x,y)\mapsto a(x)b(y)$.
--
--   An **orthonormal expansion** of $F$ is $F=\sum_{j=1}^m\sigma_j u_j v_j^T$ with $\sigma_j>0$ and $(u_j)$, $(v_j)$ orthonormal for $\langle\cdot,\cdot\rangle$; the $\sigma_j$ (the **singular coefficients**) are the ordinary singular values of the matrix $(F(x,y))$ divided by $\sqrt{|\alpha||\beta|}$. The **nuclear norm** is
--   $$\|F\|_*=\sum_j\sigma_j .$$
--   The **truncation** at $\beta$ keeps the coefficients strictly greater than $\beta$: $F^{>\beta}=\sum_{j:\sigma_j>\beta}\sigma_j u_jv_j^T$; its **balanced factors** $\sqrt{\sigma_j}u_j$, $\sqrt{\sigma_j}v_j$ have energies $\Phi_\beta(x)=\sum_{\sigma_j>\beta}\sigma_ju_j(x)^2$ and $\Psi_\beta(y)=\sum_{\sigma_j>\beta}\sigma_jv_j(y)^2$. A **product representation** is $F=\sum_{j=1}^m a_jb_j^T$ with arbitrary factors; its **factor energies** are $\Phi_F(x)=\sum_j a_j(x)^2$, $\Psi_F(y)=\sum_j b_j(y)^2$. The **four-cycle average** is $\mathrm{Cyc}(F)=\mathbb E[F(x_1,y_1)F(x_1,y_2)F(x_2,y_1)F(x_2,y_2)]$ over independent uniform $x_1,x_2,y_1,y_2$, and $\|F\|_\infty=\max|F|$.
--
--   **Formalization Note.** `Table α β = α → β → ℝ`. `avg`, `ip`, `l2`, `tableIp`, `tableL2`, `outer` are the averages above. `nuclearNorm F` is computed as $(|\alpha||\beta|)^{-1/2}\sum_j\sqrt{\lambda_j}$, where $\lambda_j$ are the eigenvalues (`Matrix.IsHermitian.eigenvalues`) of the positive semidefinite matrix $F^TF$; this equals the sum of the singular coefficients of any orthonormal expansion. `OrthoExpansion F` bundles $m$, $\sigma$, $u$, $v$ with positivity, orthonormality and the expansion identity; `trunc`, `truncPhi`, `truncPsi` are $F^{>\beta}$ and its balanced energies. `ProdRep F` bundles a product representation; `ProdRep.Φ`, `ProdRep.Ψ` are its energies. `cyc` is the four-cycle average and `supNorm` the iterated supremum of $|F|$ over the finite (bounded) index sets.
-- source:
--   Dziembowski, Faust, Leakage-Resilient Computation via Matrix Refreshing, arXiv:2611.04876 (sha256 fdbb2454…), pp. 18–21, Definitions 2.5, 2.6, 2.8, 2.11, 2.12, 2.16, 2.17 and Lemma 2.10 (Eq. (2.3)); p. 30, Eq. (4.7); p. 33 (‖·‖_∞); p. 37, Eq. (4.41)

import Mathlib

/-!
# Tables: probability-normalized inner products, the nuclear norm, orthonormal expansions,
# product representations, factor energies and four-cycle averages

Dziembowski, Faust, *Leakage-Resilient Computation via Matrix Refreshing*, arXiv:2611.04876
(sha256 fdbb2454…), §2.3: Definitions 2.5, 2.6, 2.8, 2.11, 2.12, 2.16, 2.17, Lemma 2.10 /
Eq. (2.3) (pp. 18–21); §4.3: Eq. (4.7) (p. 30), `‖·‖_∞` (p. 33), Eq. (4.41) (p. 37).

A table is a real function `F : α → β → ℝ` on a product of two finite sets (rows `α`, columns
`β`); the paper uses `α = U_L, β = U_R` and `α = U_L², β = U_R²`. Every average, inner product
and norm uses the uniform measures on the row and column sets (the *probability
normalization*): `avg f = |α|⁻¹ ∑ f`, `ip a b = E[a b]`, `l2 a = (E[a²])^{1/2}`,
`tableIp F W = E_{x,y}[F W]`, `tableL2 F = (E_{x,y}[F²])^{1/2}`.

* `nuclearNorm F` is the sum of the singular coefficients of `F` for these inner products
  (Definition 2.11). It is computed as `(|α| |β|)^{-1/2}` times the ordinary nuclear norm of the
  matrix `(F x y)`, the sum of the square roots of the eigenvalues of `Fᵀ F` (all eigenvalues are
  nonnegative): the paper notes (p. 17, p. 30) that the singular coefficients are the ordinary
  singular values divided by `√(|α| |β|)`.
* `OrthoExpansion F`: an orthonormal expansion `F = ∑ⱼ σⱼ uⱼ vⱼᵀ` with `σⱼ > 0` and orthonormal
  families `(uⱼ)`, `(vⱼ)` (Lemma 2.10, Eq. (2.3)). `trunc E β = ∑_{σⱼ > β} σⱼ uⱼ vⱼᵀ` keeps the
  coefficients strictly greater than `β` (Eq. (4.7)); `truncPhi`, `truncPsi` are the energies
  `∑_{σⱼ > β} σⱼ uⱼ(x)²`, `∑_{σⱼ > β} σⱼ vⱼ(y)²` of its balanced factors `√σⱼ uⱼ`, `√σⱼ vⱼ`
  (Definitions 2.16, 2.17).
* `ProdRep F`: a finite product representation `F = ∑ⱼ aⱼ bⱼᵀ` (Definition 2.12), with factor
  energies `Φ x = ∑ⱼ aⱼ(x)²`, `Ψ y = ∑ⱼ bⱼ(y)²` (Definition 2.16).
* `cyc F`: the four-cycle average `E[F(x₁,y₁) F(x₁,y₂) F(x₂,y₁) F(x₂,y₂)]` (Eq. (4.41));
  `supNorm F = max |F|`.
-/

namespace LeakageRefresh.Continual

/-- A real table on rows `α` and columns `β`. -/
abbrev Table (α β : Type*) := α → β → ℝ

section

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The uniform average `E_{x ←$ α}[f(x)] = |α|⁻¹ ∑ₓ f(x)` (Definition 2.5). -/
noncomputable def avg (f : α → ℝ) : ℝ :=
  (Fintype.card α : ℝ)⁻¹ * ∑ x, f x

/-- The probability-normalized inner product `⟨a, b⟩ = E[a b]` (Definition 2.5). -/
noncomputable def ip (a b : α → ℝ) : ℝ :=
  avg (fun x => a x * b x)

/-- The L2 norm `‖a‖₂ = (E[a²])^{1/2}` (Definition 2.5). -/
noncomputable def l2 (a : α → ℝ) : ℝ :=
  Real.sqrt (avg (fun x => a x ^ 2))

/-- The pairing `⟨F, W⟩ = E_{x,y}[F(x, y) W(x, y)]` of two tables (Definition 2.5). -/
noncomputable def tableIp (F W : Table α β) : ℝ :=
  avg (fun p : α × β => F p.1 p.2 * W p.1 p.2)

/-- The L2 norm `‖F‖₂ = (E_{x,y}[F(x, y)²])^{1/2}` of a table (Definition 2.5). -/
noncomputable def tableL2 (F : Table α β) : ℝ :=
  Real.sqrt (avg (fun p : α × β => F p.1 p.2 ^ 2))

/-- The product table `a · bᵀ : (x, y) ↦ a(x) b(y)` (Definition 2.6). -/
def outer (a : α → ℝ) (b : β → ℝ) : Table α β :=
  fun x y => a x * b y

/-- The nuclear norm `‖F‖_*` (Definition 2.11): the sum of the singular coefficients of `F` for
the probability-normalized inner products, i.e. `(|α| |β|)^{-1/2}` times the sum of the
ordinary singular values `√λⱼ(Fᵀ F)` of the matrix `(F x y)`. -/
noncomputable def nuclearNorm [DecidableEq β] (F : Table α β) : ℝ :=
  (Real.sqrt ((Fintype.card α : ℝ) * (Fintype.card β : ℝ)))⁻¹ *
    ∑ j, Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self (Matrix.of F)).eigenvalues j)

/-- An orthonormal expansion `F(x, y) = ∑ⱼ σⱼ uⱼ(x) vⱼ(y)` (Lemma 2.10, Eq. (2.3)): positive
coefficients and families orthonormal for the uniform inner products (Definition 2.8). -/
structure OrthoExpansion (F : Table α β) where
  /-- the number of terms -/
  m : ℕ
  /-- the singular coefficients `σⱼ` -/
  σ : Fin m → ℝ
  /-- the left singular functions `uⱼ` -/
  u : Fin m → α → ℝ
  /-- the right singular functions `vⱼ` -/
  v : Fin m → β → ℝ
  σ_pos : ∀ j, 0 < σ j
  u_orthonormal : ∀ j k, ip (u j) (u k) = if j = k then 1 else 0
  v_orthonormal : ∀ j k, ip (v j) (v k) = if j = k then 1 else 0
  expand : ∀ x y, F x y = ∑ j, σ j * u j x * v j y

/-- The truncation `F^{>β} = ∑_{j : σⱼ > β} σⱼ uⱼ vⱼᵀ` of an orthonormal expansion (Eq. (4.7)):
only the coefficients strictly greater than `β` are kept. -/
noncomputable def OrthoExpansion.trunc {F : Table α β} (E : OrthoExpansion F) (β' : ℝ) :
    Table α β :=
  fun x y => ∑ j ∈ Finset.univ.filter (fun j => β' < E.σ j), E.σ j * E.u j x * E.v j y

/-- The left energy `Φ_β(x) = ∑_{σⱼ > β} σⱼ uⱼ(x)²` of the balanced factors `√σⱼ uⱼ` of the
truncation (Definitions 2.16, 2.17; Lemma 4.6). -/
noncomputable def OrthoExpansion.truncPhi {F : Table α β} (E : OrthoExpansion F) (β' : ℝ)
    (x : α) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => β' < E.σ j), E.σ j * E.u j x ^ 2

/-- The right energy `Ψ_β(y) = ∑_{σⱼ > β} σⱼ vⱼ(y)²` of the balanced factors `√σⱼ vⱼ` of the
truncation (Definitions 2.16, 2.17; Lemma 4.6). -/
noncomputable def OrthoExpansion.truncPsi {F : Table α β} (E : OrthoExpansion F) (β' : ℝ)
    (y : β) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => β' < E.σ j), E.σ j * E.v j y ^ 2

/-- A finite product representation `F = ∑ⱼ aⱼ bⱼᵀ` (Definition 2.12). -/
structure ProdRep (F : Table α β) where
  /-- the number of terms -/
  m : ℕ
  /-- the left factors -/
  a : Fin m → α → ℝ
  /-- the right factors -/
  b : Fin m → β → ℝ
  expand : ∀ x y, F x y = ∑ j, a j x * b j y

/-- The left factor energy `Φ_F(x) = ∑ⱼ aⱼ(x)²` of a product representation (Definition 2.16). -/
def ProdRep.Φ {F : Table α β} (R : ProdRep F) (x : α) : ℝ :=
  ∑ j, R.a j x ^ 2

/-- The right factor energy `Ψ_F(y) = ∑ⱼ bⱼ(y)²` of a product representation (Definition 2.16). -/
def ProdRep.Ψ {F : Table α β} (R : ProdRep F) (y : β) : ℝ :=
  ∑ j, R.b j y ^ 2

/-- The four-cycle average (Eq. (4.41)):
`Cyc(F) = E_{x₁,x₂,y₁,y₂}[F(x₁,y₁) F(x₁,y₂) F(x₂,y₁) F(x₂,y₂)]` with all four coordinates
independent and uniform. -/
noncomputable def cyc (F : Table α β) : ℝ :=
  avg (fun p : (α × α) × (β × β) =>
    F p.1.1 p.2.1 * F p.1.1 p.2.2 * F p.1.2 p.2.1 * F p.1.2 p.2.2)

/-- The largest absolute entry `‖F‖_∞ = max_{x,y} |F(x, y)|` (p. 33). -/
noncomputable def supNorm (F : Table α β) : ℝ :=
  ⨆ x, ⨆ y, |F x y|

end

end LeakageRefresh.Continual


