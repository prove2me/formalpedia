-- Prove2me | Definitions.Def_MonoidProdQ_Supplement_UTBool
-- name    : MonoidProdQ_Supplement_UTBool
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:12:38.424194+00:00
-- url     : https://prove2.me/theorems/7a6f7882-dfac-40f9-9054-c58aa765cb99
-- title:
--   Boolean unitriangular monoid $\mathrm{UT}_k(\mathbb B)$
-- statement:
--   Let $\mathbb B=(\{0,1\},\vee,\wedge)$. The monoid $\mathrm{UT}_k(\mathbb B)$ consists of the $k\times k$ upper triangular Boolean matrices with all diagonal entries equal to $1$, under the Boolean matrix product
--
--   $$(AB)_{ij}=\bigvee_{l}\bigl(A_{il}\wedge B_{lj}\bigr),$$
--
--   with the identity matrix as identity. Theorem 51 determines its product breadth $\binom k2$ and the query complexity of its product problem up to constants.
--
--   **Formalization Note** An element is a Boolean matrix indexed by $\{0,\dots,k-1\}$ together with the two defining properties (unit diagonal, and an entry $(i,j)$ can be $1$ only if $i\le j$). Monoid, finiteness and decidable-equality instances are defined with the type.
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §9, p.67

import Mathlib

namespace MonoidProdQ.Supplement

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §9, p.67: "Let B = ({0, 1}, ∨, ∧), and let
UT_k(B) be the monoid of upper triangular Boolean matrices with diagonal entries one", under the
Boolean matrix product `(AB)_{ij} = ⋁_l (A_{il} ∧ B_{lj})`; the identity is the identity matrix.

**Formalization Note.** An element is a `k × k` matrix of booleans (`entry i j`, rows and columns
indexed by `Fin k`) together with the two defining properties: every diagonal entry is `true`
and an entry `(i, j)` can be `true` only when `i ≤ j`. The Boolean product is
`decide (∃ l, A i l ∧ B l j)`. The monoid, finite-type and decidable-equality instances are
defined in this module; two elements are equal exactly when their entries are. -/
structure UTBool (k : ℕ) where
  /-- The Boolean entries. -/
  entry : Fin k → Fin k → Bool
  /-- Diagonal entries are one. -/
  diag : ∀ i, entry i i = true
  /-- The matrix is upper triangular. -/
  upper : ∀ i j, entry i j = true → i ≤ j

namespace UTBool

variable {k : ℕ}

@[ext] theorem ext {A B : UTBool k} (h : ∀ i j, A.entry i j = B.entry i j) : A = B := by
  cases A; cases B; congr; funext i j; exact h i j

/-- The Boolean matrix product and the identity matrix. -/
instance : Monoid (UTBool k) where
  mul A B := ⟨fun i j => decide (∃ l, A.entry i l = true ∧ B.entry l j = true),
    fun i => by simp only [decide_eq_true_eq]; exact ⟨i, A.diag i, B.diag i⟩,
    fun i j h => by
      simp only [decide_eq_true_eq] at h
      obtain ⟨l, h1, h2⟩ := h
      exact le_trans (A.upper i l h1) (B.upper l j h2)⟩
  one := ⟨fun i j => decide (i = j), fun i => by simp, fun i j h => by
    simp only [decide_eq_true_eq] at h; exact le_of_eq h⟩
  mul_assoc A B C := by
    ext i j
    show decide (∃ l, decide (∃ m, A.entry i m = true ∧ B.entry m l = true) = true ∧
        C.entry l j = true) =
      decide (∃ m, A.entry i m = true ∧ decide (∃ l, B.entry m l = true ∧ C.entry l j = true) = true)
    simp only [decide_eq_true_eq, decide_eq_decide]
    constructor
    · rintro ⟨l, ⟨m, h1, h2⟩, h3⟩; exact ⟨m, h1, l, h2, h3⟩
    · rintro ⟨m, h1, l, h2, h3⟩; exact ⟨l, ⟨m, h1, h2⟩, h3⟩
  one_mul A := by
    ext i j
    show decide (∃ l, decide (i = l) = true ∧ A.entry l j = true) = A.entry i j
    cases h : A.entry i j <;> simp [h]
  mul_one A := by
    ext i j
    show decide (∃ l, A.entry i l = true ∧ decide (l = j) = true) = A.entry i j
    cases h : A.entry i j <;> simp [h]

theorem entry_injective : Function.Injective (fun A : UTBool k => A.entry) :=
  fun _ _ h => ext fun i j => congrFun (congrFun h i) j

instance : DecidableEq (UTBool k) := fun A B =>
  decidable_of_iff (A.entry = B.entry) entry_injective.eq_iff

noncomputable instance : Fintype (UTBool k) := Fintype.ofInjective _ entry_injective

end UTBool

end MonoidProdQ.Supplement


