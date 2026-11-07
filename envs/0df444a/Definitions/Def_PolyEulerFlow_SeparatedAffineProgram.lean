-- Prove2me | Definitions.Def_PolyEulerFlow_SeparatedAffineProgram
-- name    : PolyEulerFlow_SeparatedAffineProgram
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:23.073906+00:00
-- url     : https://prove2.me/theorems/d71afb1f-591f-4cd7-8b14-0853499c6228
-- title:
--   Separated affine program (Definition 13), valid prefixes and interval gain bounds
-- statement:
--   Definition 13, p.9. A **separated affine program** with $m$ data registers and $g$ tests has rational affine tests $u_j(Y,h)=\sum_i a_{ji}Y_i+b_jh+c_j$ and, for every complete sign pattern $\sigma\in\{-1,1\}^g$, a branch
--   $$H_\sigma(Y)=D_\sigma Y+b_\sigma$$
--   with rational $D_\sigma$, $b_\sigma$ independent of $h$. At scale $h$, a set $\mathcal C_h\subseteq[0,1]^m$ specifies the valid configurations. There are constants $r_0,\kappa>0$ such that, for $0<h\le1/16$, every valid configuration $C$ and every test,
--   $$\|Y-C\|_\infty\le r_0h\implies \operatorname{sign}u_j(Y,h)=\operatorname{sign}u_j(C,h)\ \text{ and }\ |u_j(Y,h)|\ge\kappa h,\tag{3}$$
--   and the tests are normalized: $|u_j(Y,h)|\le1$ on $[-2,3]^m$ for $0<h\le1/16$.
--
--   A **valid prefix** $C_0,\dots,C_T$ follows the selected branches, $C_{j+1}=H_{\sigma(C_j)}(C_j)$, and has all its configurations valid. An **interval gain bound** is a number $\Gamma\ge1$ with
--   $$\|D_{\sigma_{j-1}}\cdots D_{\sigma_i}\|_\infty\le\Gamma\qquad(0\le i<j\le T),\tag{4}$$
--   for the induced sup norm (maximal row sum). A **resetting halt** at the end of the prefix enters $C_T$ by a constant branch, and the branch selected at $C_T$ is the constant map $Y\mapsto C_T$. Finally $D^*=\max(1,\max_\sigma\|D_\sigma\|_\infty)$ and $r^*=r_0/(4D^*)$ (p.32).
--
--   **Formalization Note** A sign pattern is a Boolean vector, `true` for $+1$; the selected pattern at $(Y,h)$ is the vector of the strict signs of the tests. In (3) the margin $|u_j|\ge\kappa h$ is part of the conclusion, on the whole ball. The optional designated Boolean coordinate of the decision semantics is not part of the structure.
-- source:
--   Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript, sha256 c4e01b2b…), Definition 13, p.9 (PDF 11), (3), (4); D∗ and r∗, p.32 (PDF 34)

import Mathlib

namespace PolyEulerFlow

/-- The induced sup norm of a matrix, the maximal row sum (p.5: "We use the sup norm for vectors, and its induced norm
for matrices"). -/
noncomputable def matInfNorm {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) : ℝ :=
  ⨆ i, ∑ j, |A i j|

/-- The product `D (i + n - 1) ⋯ D (i + 1) D i`; the empty product is the identity. -/
def intervalProd {ι : Type*} [Fintype ι] [DecidableEq ι] (D : ℕ → Matrix ι ι ℝ) (i : ℕ) : ℕ → Matrix ι ι ℝ
  | 0 => 1
  | n + 1 => D (i + n) * intervalProd D i n

/-- A rational affine form `Σ aᵢ Yᵢ + b h + c` of `(Y, h)`. -/
noncomputable def affineForm {m : ℕ} (a : Fin m → ℚ) (b c : ℚ) (Y : Fin m → ℝ) (h : ℝ) : ℝ :=
  ∑ i, (a i : ℝ) * Y i + (b : ℝ) * h + (c : ℝ)

/-- A separated affine program, Definition 13, p.9. Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript,
sha256 c4e01b2b…). `m` data registers and `g` tests.
**Formalization Note.** A sign pattern `σ ∈ {-1, 1}^g` is `Fin g → Bool`, `true` for `+1`. The valid sets are indexed by the real scale, and the
margin (3) and the normalization are imposed for `0 < h ≤ 1/16`. In (3) the bound `|u_j(Y, h)| ≥ κh` is part of the conclusion. Tests are affine jointly in
`(Y, h)`, as all the tests of the page are. Matrices and vectors are rational and independent of `h`. -/
structure SeparatedAffineProgram (m g : ℕ) where
  testCoeff : Fin g → Fin m → ℚ
  testScale : Fin g → ℚ
  testConst : Fin g → ℚ
  D : (Fin g → Bool) → Matrix (Fin m) (Fin m) ℚ
  b : (Fin g → Bool) → Fin m → ℚ
  valid : ℝ → Set (Fin m → ℝ)
  r0 : ℝ
  κ : ℝ
  r0_pos : 0 < r0
  κ_pos : 0 < κ
  valid_unit : ∀ h, ∀ C ∈ valid h, ∀ i, C i ∈ Set.Icc (0 : ℝ) 1
  margin : ∀ h, 0 < h → h ≤ 1 / 16 → ∀ C ∈ valid h, ∀ Y : Fin m → ℝ, ‖Y - C‖ ≤ r0 * h → ∀ j,
    SignType.sign (affineForm (testCoeff j) (testScale j) (testConst j) Y h) =
      SignType.sign (affineForm (testCoeff j) (testScale j) (testConst j) C h) ∧
    κ * h ≤ |affineForm (testCoeff j) (testScale j) (testConst j) Y h|
  normalized : ∀ h, 0 < h → h ≤ 1 / 16 → ∀ Y : Fin m → ℝ, (∀ i, Y i ∈ Set.Icc (-2 : ℝ) 3) → ∀ j,
    |affineForm (testCoeff j) (testScale j) (testConst j) Y h| ≤ 1

namespace SeparatedAffineProgram

variable {m g : ℕ} (prog : SeparatedAffineProgram m g)

/-- The test `u_j(Y, h)`. -/
noncomputable def test (j : Fin g) (Y : Fin m → ℝ) (h : ℝ) : ℝ :=
  affineForm (prog.testCoeff j) (prog.testScale j) (prog.testConst j) Y h

/-- The complete sign pattern of the tests at `(Y, h)`. -/
noncomputable def signPat (h : ℝ) (Y : Fin m → ℝ) : Fin g → Bool :=
  open Classical in
  fun j => decide (0 < prog.test j Y h)

/-- The matrix `D_σ` over the reals. -/
noncomputable def realD (σ : Fin g → Bool) : Matrix (Fin m) (Fin m) ℝ :=
  (prog.D σ).map (fun q : ℚ => (q : ℝ))

/-- The vector `b_σ` over the reals. -/
noncomputable def realb (σ : Fin g → Bool) : Fin m → ℝ :=
  fun i => (prog.b σ i : ℝ)

/-- The branch `H_σ(Y) = D_σ Y + b_σ`. -/
noncomputable def branch (σ : Fin g → Bool) (Y : Fin m → ℝ) : Fin m → ℝ :=
  (prog.realD σ).mulVec Y + prog.realb σ

/-- `C₀, …, C_T` is a valid prefix at scale `h`: it follows the selected branches and all its configurations are valid. -/
def IsValidPrefix (h : ℝ) (C : ℕ → Fin m → ℝ) (T : ℕ) : Prop :=
  (∀ j ≤ T, C j ∈ prog.valid h) ∧ ∀ j < T, C (j + 1) = prog.branch (prog.signPat h (C j)) (C j)

/-- `Γ` is an interval gain bound (4): `Γ ≥ 1` and `‖D_{σ_{j-1}} ⋯ D_{σ_i}‖∞ ≤ Γ` for `0 ≤ i < j ≤ T`. -/
def IsGainBound (h : ℝ) (C : ℕ → Fin m → ℝ) (T : ℕ) (Γ : ℝ) : Prop :=
  1 ≤ Γ ∧ ∀ i n, 0 < n → i + n ≤ T →
    matInfNorm (intervalProd (fun k => prog.realD (prog.signPat h (C k))) i n) ≤ Γ

/-- The branch `σ` is the constant map `Y ↦ Chalt`. -/
def IsConstantBranch (σ : Fin g → Bool) (Chalt : Fin m → ℝ) : Prop :=
  prog.realD σ = 0 ∧ prog.realb σ = Chalt

/-- The last transition of the prefix is a resetting halt (Definition 13): it enters `C_T` by a constant branch, and the branch selected at
`C_T` is the constant map `Y ↦ C_T`. -/
def IsResettingHaltRun (h : ℝ) (C : ℕ → Fin m → ℝ) (T : ℕ) : Prop :=
  1 ≤ T ∧ prog.IsConstantBranch (prog.signPat h (C (T - 1))) (C T) ∧
    prog.IsConstantBranch (prog.signPat h (C T)) (C T)

/-- `D∗ = max(1, max_σ ‖D_σ‖∞)` (p.32). -/
noncomputable def Dstar : ℝ :=
  max 1 (⨆ σ, matInfNorm (prog.realD σ))

/-- `r∗ = r₀/(4D∗)` (p.32). -/
noncomputable def rStar : ℝ :=
  prog.r0 / (4 * prog.Dstar)

end SeparatedAffineProgram

end PolyEulerFlow


