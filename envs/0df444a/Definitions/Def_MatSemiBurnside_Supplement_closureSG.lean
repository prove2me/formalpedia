-- Prove2me | Definitions.Def_MatSemiBurnside_Supplement_closureSG
-- name    : MatSemiBurnside_Supplement_closureSG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:44:38.651024+00:00
-- url     : https://prove2.me/theorems/11de0901-05ed-42c4-bf97-927492ea68cb
-- title:
--   The Zariski closure $\overline{\langle X\rangle}$ in $\mathrm{Mat}_d(\overline{\mathbb Q})$
-- statement:
--   Let $\overline{\mathbb Q}$ be the field of algebraic numbers. For a set $T\subseteq\mathrm{Mat}_d(\overline{\mathbb Q})\cong\overline{\mathbb Q}^{d^2}$, its **Zariski closure** is the set of matrices at which every polynomial in the $d^2$ entries (with coefficients in $\overline{\mathbb Q}$) that vanishes on $T$ also vanishes; it is the smallest Zariski-closed set containing $T$.
--
--   For a finite $X\subseteq\mathrm{Mat}_d(\mathbb Q)$, $\overline{\langle X\rangle}$ is the Zariski closure in $\mathrm{Mat}_d(\overline{\mathbb Q})$ of the semigroup $\langle X\rangle$, viewed inside $\mathrm{Mat}_d(\overline{\mathbb Q})$ through the inclusion $\mathbb Q\subseteq\overline{\mathbb Q}$. By continuity of matrix multiplication it is again a semigroup.
--
--   This is the semigroup on which the congruence of Theorem 3 is defined.
--
--   **Formalization Note** $\overline{\mathbb Q}$ is `AlgebraicClosure ℚ`. The closure is the zero set of the vanishing ideal in all of $\mathrm{Mat}_d(\overline{\mathbb Q})$, singular matrices included (not inside $\mathrm{GL}_d$). The module proves that the closure of a multiplicatively closed set is multiplicatively closed, so $\overline{\langle X\rangle}$ is a `Subsemigroup`; `incl` is the entrywise embedding of $\langle X\rangle$ into it.
-- source:
--   Guttenberg, Lhote, Shirmohammadi, Worrell, Burnside Problems for Matrix Semigroup Quotients with Applications to Border Complexity, STOC 2027 submission (held version, sha256 1bc61d4e…), §2, pp.5–7 (ℚ̄, Zariski topology) and §3.3, p.13

import Mathlib
set_option autoImplicit false

namespace MatSemiBurnside.Supplement

open MvPolynomial

/-- **The field ℚ̄ of algebraic numbers.** Guttenberg, Lhote, Shirmohammadi, Worrell, *Burnside Problems for
Matrix Semigroup Quotients with Applications to Border Complexity*, STOC 2027 submission (held version,
sha256 1bc61d4e…), §2, p.5: "We denote by ℚ̄ the field of algebraic numbers, that is, the roots of nonzero
polynomials with rational coefficients."

**Formalization Note.** `AlgebraicClosure ℚ`, an algebraic closure of ℚ; it is isomorphic to the field of
algebraic numbers. -/
abbrev Qbar : Type := AlgebraicClosure ℚ

/-- **Zariski closure in Mat_d(ℚ̄).** Guttenberg, Lhote, Shirmohammadi, Worrell, STOC 2027 submission (held
version, sha256 1bc61d4e…), §2, pp.6–7: the Zariski closure of a subset of ℚ̄^m is the smallest Zariski-closed
set (common zero set of polynomials) containing it; matrices in Mat_d(ℚ̄) are points of ℚ̄^{d²}.

`zariskiClosureMat T` is the set of matrices M ∈ Mat_d(ℚ̄) at which every polynomial in the d² entries, with
ℚ̄ coefficients, that vanishes on T also vanishes.

**Formalization Note.** This is the common zero set of the vanishing ideal of T, which is the smallest
Zariski-closed subset of Mat_d(ℚ̄) ≅ ℚ̄^{d²} containing T. The closure is taken in all of Mat_d(ℚ̄), not in
GL_d. -/
def zariskiClosureMat {d : ℕ} (T : Set (Matrix (Fin d) (Fin d) Qbar)) : Set (Matrix (Fin d) (Fin d) Qbar) :=
  {M | ∀ p : MvPolynomial (Fin d × Fin d) Qbar,
    (∀ A ∈ T, eval (fun ij => A ij.1 ij.2) p = 0) → eval (fun ij => M ij.1 ij.2) p = 0}

/-- The entrywise embedding Mat_d(ℚ) → Mat_d(ℚ̄). -/
noncomputable abbrev toQbar {d : ℕ} : Matrix (Fin d) (Fin d) ℚ →+* Matrix (Fin d) (Fin d) Qbar :=
  (algebraMap ℚ Qbar).mapMatrix

theorem subset_zariskiClosureMat {d : ℕ} (T : Set (Matrix (Fin d) (Fin d) Qbar)) :
    T ⊆ zariskiClosureMat T := fun A hA _ hp => hp A hA

private theorem eval_lmul {d : ℕ} (a : Matrix (Fin d) (Fin d) Qbar) (p : MvPolynomial (Fin d × Fin d) Qbar)
    (M : Matrix (Fin d) (Fin d) Qbar) :
    eval (fun ij => M ij.1 ij.2) (bind₁ (fun ij : Fin d × Fin d => ∑ k, C (a ij.1 k) * X (k, ij.2)) p) =
      eval (fun ij => (a * M) ij.1 ij.2) p := by
  have := eval₂Hom_bind₁ (RingHom.id Qbar) (fun ij : Fin d × Fin d => M ij.1 ij.2)
    (fun ij : Fin d × Fin d => ∑ k, C (a ij.1 k) * X (k, ij.2)) p
  simp only [coe_eval₂Hom] at this
  change eval₂ _ _ _ = eval₂ _ _ _
  rw [this]
  congr 1
  funext ij
  simp [Matrix.mul_apply]

private theorem eval_rmul {d : ℕ} (b : Matrix (Fin d) (Fin d) Qbar) (p : MvPolynomial (Fin d × Fin d) Qbar)
    (M : Matrix (Fin d) (Fin d) Qbar) :
    eval (fun ij => M ij.1 ij.2) (bind₁ (fun ij : Fin d × Fin d => ∑ k, X (ij.1, k) * C (b k ij.2)) p) =
      eval (fun ij => (M * b) ij.1 ij.2) p := by
  have := eval₂Hom_bind₁ (RingHom.id Qbar) (fun ij : Fin d × Fin d => M ij.1 ij.2)
    (fun ij : Fin d × Fin d => ∑ k, X (ij.1, k) * C (b k ij.2)) p
  simp only [coe_eval₂Hom] at this
  change eval₂ _ _ _ = eval₂ _ _ _
  rw [this]
  congr 1
  funext ij
  simp [Matrix.mul_apply]

/-- The Zariski closure of a multiplicatively closed set of matrices is multiplicatively closed (p.7: "By
continuity of matrix multiplication, the Zariski closure of a matrix semigroup is again a semigroup"). -/
theorem zariskiClosureMat_mul_mem {d : ℕ} (T : Set (Matrix (Fin d) (Fin d) Qbar))
    (hT : ∀ a ∈ T, ∀ b ∈ T, a * b ∈ T) {a b : Matrix (Fin d) (Fin d) Qbar}
    (ha : a ∈ zariskiClosureMat T) (hb : b ∈ zariskiClosureMat T) : a * b ∈ zariskiClosureMat T := by
  -- first: T · closure(T) ⊆ closure(T)
  have h1 : ∀ x ∈ T, ∀ y ∈ zariskiClosureMat T, x * y ∈ zariskiClosureMat T := by
    intro x hx y hy p hp
    have := hy _ (fun A hA => by rw [eval_lmul]; exact hp _ (hT x hx A hA))
    rwa [eval_lmul] at this
  intro p hp
  have := ha _ (fun A hA => by rw [eval_rmul]; exact h1 A hA b hb p hp)
  rwa [eval_rmul] at this

/-- **The Zariski closure ⟨X⟩‾ in Mat_d(ℚ̄), as a semigroup.** Guttenberg, Lhote, Shirmohammadi, Worrell,
STOC 2027 submission (held version, sha256 1bc61d4e…), §3.3, p.13: "Write ⟨X⟩‾ for this closure in
Mat_d(ℚ̄)." Here ⟨X⟩ ⊆ Mat_d(ℚ) is the semigroup of all nonempty products of elements of X
(`Subsemigroup.closure X`), mapped entrywise into Mat_d(ℚ̄), and ⟨X⟩‾ is its Zariski closure there.

**Formalization Note.** The closure is in all of Mat_d(ℚ̄) (singular matrices included), with polynomials over
ℚ̄ in the d² entries. It is a subsemigroup by `zariskiClosureMat_mul_mem` (p.7). -/
noncomputable def closureSG {d : ℕ} (X : Finset (Matrix (Fin d) (Fin d) ℚ)) :
    Subsemigroup (Matrix (Fin d) (Fin d) Qbar) where
  carrier := zariskiClosureMat (toQbar '' (Subsemigroup.closure (X : Set (Matrix (Fin d) (Fin d) ℚ))))
  mul_mem' := by
    intro a b ha hb
    refine zariskiClosureMat_mul_mem _ ?_ ha hb
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact ⟨x * y, Subsemigroup.mul_mem _ hx hy, map_mul _ x y⟩

/-- The embedding of ⟨X⟩ ⊆ Mat_d(ℚ) into its Zariski closure ⟨X⟩‾ ⊆ Mat_d(ℚ̄) (entrywise). -/
noncomputable def incl {d : ℕ} (X : Finset (Matrix (Fin d) (Fin d) ℚ))
    (a : Subsemigroup.closure (X : Set (Matrix (Fin d) (Fin d) ℚ))) : closureSG X :=
  ⟨toQbar (a : Matrix (Fin d) (Fin d) ℚ), subset_zariskiClosureMat _ ⟨a, a.2, rfl⟩⟩

end MatSemiBurnside.Supplement


