-- Prove2me | Definitions.Def_ChapterBookBrstInstances
-- name    : ChapterBookBrstInstances
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-21T11:23:54.822677+00:00
-- url     : https://prove2.me/theorems/7b9f865d-d1fe-4f3a-a2c7-58b548021afb
-- title:
--   The Lean 4 theorem `is` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterBookBrstInstances.lean`): generated def bundle for ChapterBookBrstInstances. See BookProof/ChapterBookBrstInstances.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterBookBrstInstances.lean

import Theorems.Thm_BookProof_SmBrstGhost_su2Struct_antisymm

import Theorems.Thm_BookProof_SmBrstGhost_su2Struct_jacobi

import Theorems.Thm_BookProof_SmBrstGhost_smStruct_antisymm

import Theorems.Thm_BookProof_SmBrstGhost_smStruct_jacobi

import Definitions.Def_ChapterBookBrstYangMills
import Definitions.Def_ChapterSmBrstGhost
import Definitions.Def_ChapterBookBrstGaugeFixing
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Mathlib


/-!
# Instances of the book's BRST charge: `su(2)`, the Standard Model, and inner derivations

`BookProof.ChapterBookBrstYangMills` builds the BRST charge exactly as `book.tex` defines it,
for a gauge algebra with totally antisymmetric structure constants carrying four spacetime
derivations `∂_μ`.  This module supplies concrete instances of that data, so the nilpotency
theorem is not vacuous.

## What is proved

* `innerDeriv_leibniz` — **every family of inner derivations is admissible**: for
  `∂_μ = ad_{X_μ}`, i.e. `(D μ)_{ab} = Σ_m x_{μm} f_{mab}`, the Leibniz condition required by
  `GaugeAlgebra` follows from the Jacobi identity.  Together with `∂_μ = 0` (the constant
  gauge field of a single multiplet) this gives a family of admissible derivations for every
  gauge algebra.
* `gaugeAlgebraOfInner` — the resulting `GaugeAlgebra`, for any totally antisymmetric
  structure constants obeying Jacobi.
* `su2BookAlgebra`, `smBookAlgebra` — the `su(2)` algebra `ε_{abc}` and the Standard-Model
  algebra `su(3) ⊕ su(2) ⊕ u(1)` of `BookProof.ChapterSmBrstGhost` as instances, with
  `su2_bookOmega_nilpotent` and `sm_bookOmega_nilpotent`: the book's BRST charge of the
  Standard-Model gauge algebra squares to zero.
* `su2_gaussGenPoly_ne_zero` — the Gauss-law constraints are not the zero operator, so the
  construction is not vacuous.

* `su2_casimir_bookOmega_comm` — for `su(2)` with constant gauge fields the quadratic
  invariant `Σ_{μ,a} A_{μa}A_{μa}` commutes with the book's BRST charge, a concrete
  gauge-invariant observable acting on the BRST cohomology.

* **Accounting identity instances** — `su2_bookGfTerm_eq_zero_of_Afield0` (QYM: the Weyl
  gauge may use only the spatial field components; `{Ω, Ψ}` vanishes at `A₀ = 0`, so `h`
  and `N` gain no gauge-fixing/ghost summand) and `sm_bookGfTerm_eq_zero_of_Afield0` (the
  same for `su(3) ⊕ su(2) ⊕ u(1)`).  For quantum gravity the book's 3D reduction is
  **non-ADM** (`book.tex` ~8226–8244): ghosts constant in the timepiece, BRST charge with
  the same functional form as the 4D one — the ADM approximation is explicitly rejected.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.BookBrstInstances

open BookProof.BookBrstYangMills BookProof.BookBrstGaugeFixing BookProof.SmBrstGhost
open BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge
open MvPolynomial

noncomputable section

variable {N : ℕ} (f : Fin N → Fin N → Fin N → ℝ)

/-! ## 1. Contracted products of structure constants -/

/-- The contracted product `Σ_m f_{pqm} f_{rsm}`. -/
def sp (p q r s : Fin N) : ℝ := ∑ m, f p q m * f r s m

theorem sp_symm (p q r s : Fin N) : sp f p q r s = sp f r s p q :=
  Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem sp_swap12 (hanti : ∀ a b c, f a b c = -f b a c) (p q r s : Fin N) :
    sp f p q r s = -sp f q p r s := by
  simp only [sp, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun m _ => by rw [hanti p q m]; ring

theorem sp_swap34 (hanti : ∀ a b c, f a b c = -f b a c) (p q r s : Fin N) :
    sp f p q r s = -sp f p q s r := by
  simp only [sp, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun m _ => by rw [hanti r s m]; ring

theorem sp_jacobi (hcyc : ∀ a b c, f a b c = f b c a)
    (hjac : ∀ a b c d, ∑ e, (f a b e * f e c d + f b c e * f e a d + f c a e * f e b d) = 0)
    (x y z w : Fin N) : sp f x y z w + sp f y z x w + sp f z x y w = 0 := by
  have h := hjac x y z w
  rw [← h]
  simp only [sp]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hcyc m z w, hcyc m x w, hcyc m y w]

/-! ## 2. Inner derivations are admissible -/

/-- The inner derivation `ad_X` in the basis: `(D)_{ab} = Σ_m x_m f_{mab}`. -/
def innerDeriv (x : Fin 4 → Fin N → ℝ) (μ : Fin 4) (a b : Fin N) : ℝ :=
  ∑ m, x μ m * f m a b

/-- The pointwise form of the Leibniz condition for one inner derivation. -/
theorem innerDeriv_pointwise (hanti : ∀ a b c, f a b c = -f b a c)
    (hcyc : ∀ a b c, f a b c = f b c a)
    (hjac : ∀ a b c d, ∑ e, (f a b e * f e c d + f b c e * f e a d + f c a e * f e b d) = 0)
    (m a b c : Fin N) :
    (∑ h, f a b h * f m h c) = (∑ h, f m a h * f h b c) + ∑ h, f m b h * f a h c := by
  have t1 : (∑ h, f a b h * f m h c) = sp f a b c m := by
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [hcyc m h c, hcyc h c m]
  have t2 : (∑ h, f m a h * f h b c) = sp f m a b c := by
    exact Finset.sum_congr rfl fun h _ => by rw [hcyc h b c]
  have t3 : (∑ h, f m b h * f a h c) = sp f m b c a := by
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [hcyc a h c, hcyc h c a]
  rw [t1, t2, t3]
  have J := sp_jacobi f hcyc hjac a b c m
  have r1 : sp f m a b c = -sp f b c a m := by
    rw [sp_symm f m a b c, sp_swap34 f hanti b c m a]
  have r2 : sp f m b c a = -sp f c a b m := by
    rw [sp_symm f m b c a, sp_swap34 f hanti c a m b]
  rw [r1, r2]
  linarith [J]

/-- **Inner derivations satisfy the Leibniz condition** required by `GaugeAlgebra`. -/
theorem innerDeriv_leibniz (hanti : ∀ a b c, f a b c = -f b a c)
    (hcyc : ∀ a b c, f a b c = f b c a)
    (hjac : ∀ a b c d, ∑ e, (f a b e * f e c d + f b c e * f e a d + f c a e * f e b d) = 0)
    (x : Fin 4 → Fin N → ℝ) (μ : Fin 4) (a b c : Fin N) :
    (∑ h, f a b h * innerDeriv f x μ h c)
      = (∑ h, innerDeriv f x μ a h * f h b c) + ∑ h, innerDeriv f x μ b h * f a h c := by
  have hL : (∑ h, f a b h * innerDeriv f x μ h c)
      = ∑ m, x μ m * ∑ h, f a b h * f m h c := by
    simp only [innerDeriv, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    exact Finset.sum_congr rfl fun h _ => by ring
  have hR1 : (∑ h, innerDeriv f x μ a h * f h b c)
      = ∑ m, x μ m * ∑ h, f m a h * f h b c := by
    simp only [innerDeriv, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    exact Finset.sum_congr rfl fun h _ => by ring
  have hR2 : (∑ h, innerDeriv f x μ b h * f a h c)
      = ∑ m, x μ m * ∑ h, f m b h * f a h c := by
    simp only [innerDeriv, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    exact Finset.sum_congr rfl fun h _ => by ring
  rw [hL, hR1, hR2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← mul_add, innerDeriv_pointwise f hanti hcyc hjac m a b c]

/-- **The gauge algebra of `book.tex` built from any totally antisymmetric structure
constants and any family of inner derivations `∂_μ = ad_{X_μ}`.** -/
def gaugeAlgebraOfInner (hanti : ∀ a b c, f a b c = -f b a c)
    (hcyc : ∀ a b c, f a b c = f b c a)
    (hjac : ∀ a b c d, ∑ e, (f a b e * f e c d + f b c e * f e a d + f c a e * f e b d) = 0)
    (x : Fin 4 → Fin N → ℝ) : GaugeAlgebra N where
  f := f
  antisymm := hanti
  cyclic := hcyc
  jacobi := hjac
  D := innerDeriv f x
  leibniz := innerDeriv_leibniz f hanti hcyc hjac x

/-! ## 3. Concrete gauge algebras -/

theorem epsZ_cyclic : ∀ a b c : Fin 3, epsZ a b c = epsZ b c a := by decide

theorem su2Struct_cyclic (a b c : Fin 3) : su2Struct a b c = su2Struct b c a := by
  rw [su2Struct, su2Struct, epsZ_cyclic a b c]

theorem u1Struct_cyclic (a b c : Fin 1) : u1Struct a b c = u1Struct b c a := rfl

theorem sumStruct_cyclic {ι κ : Type*} {f1 : ι → ι → ι → ℝ} {f2 : κ → κ → κ → ℝ}
    (h1 : ∀ a b c, f1 a b c = f1 b c a) (h2 : ∀ a b c, f2 a b c = f2 b c a)
    (a b c : ι ⊕ κ) : sumStruct f1 f2 a b c = sumStruct f1 f2 b c a := by
  rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;>
    simp only [sumStruct] <;> first | rfl | exact h1 a b c | exact h2 a b c

theorem smStruct_cyclic {f3 : Fin 8 → Fin 8 → Fin 8 → ℝ}
    (h3 : ∀ a b c, f3 a b c = f3 b c a) (a b c : Fin 12) :
    smStruct f3 a b c = smStruct f3 b c a :=
  sumStruct_cyclic h3 (sumStruct_cyclic su2Struct_cyclic u1Struct_cyclic) _ _ _

/-- **The `su(2)` gauge algebra** `ε_{abc}` with the inner derivations `ad_{X_μ}`. -/
def su2BookAlgebra (x : Fin 4 → Fin 3 → ℝ) : GaugeAlgebra 3 :=
  gaugeAlgebraOfInner su2Struct su2Struct_antisymm su2Struct_cyclic su2Struct_jacobi x

/-- **The Standard-Model gauge algebra** `su(3) ⊕ su(2) ⊕ u(1)` with the inner derivations
`ad_{X_μ}`, given the `su(3)` structure constants. -/
def smBookAlgebra (f3 : Fin 8 → Fin 8 → Fin 8 → ℝ)
    (h3anti : ∀ a b c, f3 a b c = -f3 b a c) (h3cyc : ∀ a b c, f3 a b c = f3 b c a)
    (h3jac : ∀ a b c h : Fin 8, ∑ e, (f3 a b e * f3 e c h + f3 b c e * f3 e a h
      + f3 c a e * f3 e b h) = 0)
    (x : Fin 4 → Fin 12 → ℝ) : GaugeAlgebra 12 :=
  gaugeAlgebraOfInner (smStruct f3) (smStruct_antisymm h3anti) (smStruct_cyclic h3cyc)
    (smStruct_jacobi h3jac) x

/-- **The book's BRST charge of the `su(2)` gauge algebra is nilpotent.** -/
theorem su2_bookOmega_nilpotent (x : Fin 4 → Fin 3 → ℝ) :
    bookOmega (su2BookAlgebra x) * bookOmega (su2BookAlgebra x) = 0 :=
  bookOmega_nilpotent _

/-- **The book's BRST charge of the Standard-Model gauge algebra is nilpotent.** -/
theorem sm_bookOmega_nilpotent (f3 : Fin 8 → Fin 8 → Fin 8 → ℝ)
    (h3anti : ∀ a b c, f3 a b c = -f3 b a c) (h3cyc : ∀ a b c, f3 a b c = f3 b c a)
    (h3jac : ∀ a b c h : Fin 8, ∑ e, (f3 a b e * f3 e c h + f3 b c e * f3 e a h
      + f3 c a e * f3 e b h) = 0)
    (x : Fin 4 → Fin 12 → ℝ) :
    bookOmega (smBookAlgebra f3 h3anti h3cyc h3jac x)
      * bookOmega (smBookAlgebra f3 h3anti h3cyc h3jac x) = 0 :=
  bookOmega_nilpotent _

/-! ## 4. Non-vacuity: the Gauss-law constraints are non-zero -/

/-- For the `su(2)` algebra with vanishing derivations the Gauss-law constraint `𝒢_0` maps the
coordinate `A_{01}` to the coordinate `A_{02}`. -/
theorem su2_gaussVec_value :
    gaussVec (su2BookAlgebra 0) 0 (0, 1) = (X (0, 2) : FieldPoly 3) := by
  have hD : ∀ (μ : Fin 4) (a b : Fin 3), (su2BookAlgebra 0).D μ a b = 0 := by
    intro μ a b
    simp [su2BookAlgebra, gaugeAlgebraOfInner, innerDeriv]
  have hf : ∀ g : Fin 3, (su2BookAlgebra 0).f 1 g 0 = su2Struct 1 g 0 := fun _ => rfl
  have e0 : su2Struct 1 0 0 = 0 := by
    have : epsZ 1 0 0 = 0 := by decide
    rw [su2Struct, this]; norm_num
  have e1 : su2Struct 1 1 0 = 0 := by
    have : epsZ 1 1 0 = 0 := by decide
    rw [su2Struct, this]; norm_num
  have e2 : su2Struct 1 2 0 = 1 := by
    have : epsZ 1 2 0 = 1 := by decide
    rw [su2Struct, this]; norm_num
  simp only [gaussVec, vecComb, hD, hf, neg_zero]
  rw [Fin.sum_univ_three, e0, e1, e2]
  simp

/-- **The Gauss-law constraints are not the zero operator**, so the BRST construction is not
vacuous. -/
theorem su2_gaussGenPoly_ne_zero : gaussGenPoly (su2BookAlgebra 0) 0 ≠ 0 := by
  intro hzero
  have happ : gaussGenPoly (su2BookAlgebra 0) 0 (X (0, 1)) = (X (0, 2) : FieldPoly 3) := by
    have : gaussGenPoly (su2BookAlgebra 0) 0 (X (0, 1))
        = gaussDer (su2BookAlgebra 0) 0 (X (0, 1)) := rfl
    rw [this, gaussDer_X, su2_gaussVec_value]
  rw [hzero] at happ
  exact (MvPolynomial.X_ne_zero ((0 : Fin 4), (2 : Fin 3))) happ.symm

/-- For the `su(2)` algebra with constant gauge fields, the quadratic invariant
`Σ_{μ,a} A_{μa} A_{μa}` is a **BRST-invariant observable**: it commutes with the book's
charge, hence acts on the physical states and on the BRST cohomology. -/
theorem su2_casimir_bookOmega_comm :
    bookOmega (su2BookAlgebra 0) * multOp (casimirPoly (N := 3))
      = multOp (casimirPoly (N := 3)) * bookOmega (su2BookAlgebra 0) :=
  casimir_bookOmega_comm _ fun _ _ _ => by
    simp [su2BookAlgebra, gaugeAlgebraOfInner, innerDeriv]

/-! ## 5. Accounting identity instances: QYM (su(2)/su(3)) and the SM algebra -/

/-- **QYM accounting identity**: for the `su(2)` gauge algebra (pure Yang–Mills), the
BRST-exact gauge-fixing term vanishes on the Weyl-gauge slice `A₀ = 0`.  The Weyl gauge
may therefore be formulated with the spatial field components only — no extra
gauge-fixing/ghost summand is needed in `h` or `N`. -/
theorem su2_bookGfTerm_eq_zero_of_Afield0 (x : Fin 4 → Fin 3 → ℝ)
    (hA0 : ∀ a : Fin 3, Afield (N := 3) 0 a = 0) :
    bookGfTerm (su2BookAlgebra x) = 0 :=
  bookGfTerm_eq_zero_of_Afield0 (su2BookAlgebra x) hA0

/-- **SM accounting identity**: the same vanishing for the Standard-Model gauge algebra
`su(3) ⊕ su(2) ⊕ u(1)`, so the temporal-gauge record of `h` and `N` carries no separate
gauge-fixing/ghost contribution from `{Ω, Ψ}`. -/
theorem sm_bookGfTerm_eq_zero_of_Afield0 (f3 : Fin 8 → Fin 8 → Fin 8 → ℝ)
    (h3anti : ∀ a b c, f3 a b c = -f3 b a c) (h3cyc : ∀ a b c, f3 a b c = f3 b c a)
    (h3jac : ∀ a b c h : Fin 8, ∑ e, (f3 a b e * f3 e c h + f3 b c e * f3 e a h
      + f3 c a e * f3 e b h) = 0)
    (x : Fin 4 → Fin 12 → ℝ)
    (hA0 : ∀ a : Fin 12, Afield (N := 12) 0 a = 0) :
    bookGfTerm (smBookAlgebra f3 h3anti h3cyc h3jac x) = 0 :=
  bookGfTerm_eq_zero_of_Afield0 (smBookAlgebra f3 h3anti h3cyc h3jac x) hA0

end

end BookProof.BookBrstInstances


