-- Prove2me | Definitions.Def_Garrido_BanachTarski
-- name    : Garrido_BanachTarski
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-09-24T13:58:38.046803+00:00
-- url     : https://prove2.me/theorems/1a627811-ff10-4373-9ded-717bf1c6ed09
-- title:
--   Spheres, rotations and isometries of Euclidean space
-- statement:
--   Five notions used by the Banach–Tarski paradox.
--
--   **Sphere $n$.** The unit sphere $S^n = \{x \in \mathbb{R}^{n+1} : \|x\| = 1\}$, where
--   $\mathbb{R}^{n+1}$ is Euclidean space on the coordinates $0, \dots, n$. So `Sphere 2` is the
--   $2$-sphere $S^2 \subseteq \mathbb{R}^3$. The source names “the $n$-sphere $\mathbb{S}^n$” (p. 3,
--   Corollary 1.9) without a defining sentence.
--
--   **The action of $SO(n+1,\mathbb{R})$ on $S^n$.** The rotation group is Mathlib's
--   `Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ`: the real $(n+1) \times (n+1)$ matrices $A$
--   with $A^{\mathsf T} A = 1$ and $\det A = 1$. It acts on $S^n$ by matrix-vector multiplication,
--   $A \cdot x = Ax$; the definition includes the proof that an orthogonal matrix preserves the
--   Euclidean norm, so $Ax$ stays on the sphere. The source names $SO(3,\mathbb{R})$ (p. 2,
--   Proposition 1.6) and $SO(n+1,\mathbb{R})$ (p. 3, Corollary 1.9) without defining them or their
--   action.
--
--   **EuclideanGroup $n$.** p. 3, Corollary 1.10: “Let $E(3)$ denote the group of isometries of
--   $\mathbb{R}^3$.” `EuclideanGroup n` is the group $E(n)$ of all isometries of $\mathbb{R}^n$
--   (bijections preserving Euclidean distance), with composition as multiplication, acting on
--   $\mathbb{R}^n$ by evaluation, $f \cdot x = f(x)$. It contains the translations and the orthogonal
--   maps, as the source's $E(3)$ does.
--
--   **ActsFreely $G$ $X$.** $G$ acts freely on $X$ when the only element of $G$ fixing
--   some point of $X$ is the identity: $g \cdot x = x$ implies $g = 1$ (stated for any monoid $G$ with a scalar operation on $X$; every use supplies a group action). The source uses the phrase
--   (Proposition 1.5) without defining it; this is its standard meaning.
--
--   **rho, sigma.** p. 2, proof of Proposition 1.6: “The rotations $\rho$ and $\sigma$ given by the
--   matrices below generate a copy of $F_2$ (for more details, see Theorem 2.1 of [14]):”
--
--   $$\rho = \begin{pmatrix} 1/3 & -2\sqrt{2}/3 & 0 \\ 2\sqrt{2}/3 & 1/3 & 0 \\ 0 & 0 & 1 \end{pmatrix}, \qquad
--   \sigma = \begin{pmatrix} 1 & 0 & 0 \\ 0 & 1/3 & -2\sqrt{2}/3 \\ 0 & 2\sqrt{2}/3 & 1/3 \end{pmatrix},$$
--
--   rotations by $\arccos(1/3)$ about the third and first coordinate axes. Each is given as an
--   element of $SO(3,\mathbb{R})$, with $\tfrac{2\sqrt{2}}{3}$ written out and with the proof that it
--   is orthogonal of determinant one.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 2-3, Propositions 1.5 and 1.6, Theorem 1.7, Corollaries 1.9 and 1.10; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf

import Mathlib

/-!
# Spheres, rotations and isometries for the Banach–Tarski paradox

Garrido, *An introduction to amenable groups*, Section 1.1 (pp. 1–3).

* `Sphere n`: the unit sphere `Sⁿ` in `ℝⁿ⁺¹`, the Euclidean space on `Fin (n + 1)`.
* The rotation group `SO(n + 1, ℝ)`, Mathlib's `Matrix.specialOrthogonalGroup`, acts on `Sⁿ` by
  matrix-vector multiplication.
* `EuclideanGroup n`: the group `E(n)` of isometries of `ℝⁿ`, acting on `ℝⁿ` by evaluation.
* `ActsFreely G X`: only the identity of `G` fixes a point of `X`.
* `rho`, `sigma`: the two rotations of Proposition 1.6 (p. 2).
-/

namespace Garrido

open Matrix

/-- The unit sphere `Sⁿ` in the Euclidean space `ℝⁿ⁺¹`. -/
abbrev Sphere (n : ℕ) : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  Metric.sphere 0 1

/-- An orthogonal matrix preserves the Euclidean norm. -/
theorem norm_toLp_mulVec_of_mem_orthogonalGroup {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℝ} (hA : A ∈ Matrix.orthogonalGroup m ℝ) (x : EuclideanSpace ℝ m) :
    ‖(WithLp.toLp 2 (A *ᵥ x.ofLp) : EuclideanSpace ℝ m)‖ = ‖x‖ := by
  have h1 : Aᵀ * A = 1 := by
    have := (Matrix.mem_orthogonalGroup_iff' (A := A)).mp hA
    simpa [Matrix.star_eq_conjTranspose] using this
  have key : inner ℝ (WithLp.toLp 2 (A *ᵥ x.ofLp) : EuclideanSpace ℝ m)
      (WithLp.toLp 2 (A *ᵥ x.ofLp)) = inner ℝ x x := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, ← Matrix.mulVec_transpose, h1,
      Matrix.transpose_one, Matrix.one_mulVec]
  have h2 := congrArg Real.sqrt key
  rwa [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (norm_nonneg _)] at h2

/-- `SO(n + 1, ℝ)` acts on `Sⁿ` by matrix-vector multiplication. -/
instance (priority := high) instSMulSphere (n : ℕ) :
    SMul (specialOrthogonalGroup (Fin (n + 1)) ℝ) (Sphere n) where
  smul A x := ⟨WithLp.toLp 2 ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) *ᵥ x.1.ofLp), by
    have hA : (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) ∈ Matrix.orthogonalGroup _ ℝ :=
      (Matrix.mem_specialOrthogonalGroup_iff.mp A.2).1
    rw [mem_sphere_zero_iff_norm, norm_toLp_mulVec_of_mem_orthogonalGroup hA]
    exact mem_sphere_zero_iff_norm.mp x.2⟩

/-- The action of `SO(n + 1, ℝ)` on `Sⁿ` is a group action. -/
instance (priority := high) instMulActionSphere (n : ℕ) :
    MulAction (specialOrthogonalGroup (Fin (n + 1)) ℝ) (Sphere n) where
  one_smul x := by
    apply Subtype.ext
    change WithLp.toLp 2 ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) *ᵥ x.1.ofLp) = x
    simp
  mul_smul A B x := by
    apply Subtype.ext
    change WithLp.toLp 2 (((A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) *
        (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)) *ᵥ x.1.ofLp) =
      WithLp.toLp 2 ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) *ᵥ
        ((B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) *ᵥ x.1.ofLp))
    rw [Matrix.mulVec_mulVec]

/-- The group `E(n)` of isometries of `ℝⁿ`. -/
abbrev EuclideanGroup (n : ℕ) :=
  EuclideanSpace ℝ (Fin n) ≃ᵢ EuclideanSpace ℝ (Fin n)

/-- `E(n)` acts on `ℝⁿ` by evaluation. -/
noncomputable instance instMulActionEuclideanGroup (n : ℕ) :
    MulAction (EuclideanGroup n) (EuclideanSpace ℝ (Fin n)) where
  smul f x := f x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- `G` acts freely on `X`: an element of `G` that fixes some point of `X` is the identity. -/
def ActsFreely (G X : Type*) [Monoid G] [SMul G X] : Prop :=
  ∀ (g : G) (x : X), g • x = x → g = 1

private theorem sqrt_two_sq : √2 * √2 = (2 : ℝ) := Real.mul_self_sqrt (by norm_num)

/-- The rotation `ρ` of Proposition 1.6 (p. 2), about the third coordinate axis. -/
noncomputable def rho : specialOrthogonalGroup (Fin 3) ℝ :=
  ⟨!![1 / 3, -(2 * √2 / 3), 0; 2 * √2 / 3, 1 / 3, 0; 0, 0, 1], by
    rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
    refine ⟨?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three] <;> nlinarith [sqrt_two_sq]
    · simp [Matrix.det_fin_three]; nlinarith [sqrt_two_sq]⟩

/-- The rotation `σ` of Proposition 1.6 (p. 2), about the first coordinate axis. -/
noncomputable def sigma : specialOrthogonalGroup (Fin 3) ℝ :=
  ⟨!![1, 0, 0; 0, 1 / 3, -(2 * √2 / 3); 0, 2 * √2 / 3, 1 / 3], by
    rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
    refine ⟨?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three] <;> nlinarith [sqrt_two_sq]
    · simp [Matrix.det_fin_three]; nlinarith [sqrt_two_sq]⟩

end Garrido


