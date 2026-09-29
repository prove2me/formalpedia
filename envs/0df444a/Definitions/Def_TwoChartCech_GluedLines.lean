-- Prove2me | Definitions.Def_TwoChartCech_GluedLines
-- name    : TwoChartCech_GluedLines
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/febb138f-e371-5f80-9451-4cc51fc2a801
-- title:
--   Two projective lines glued at s points: Čech model
-- statement:
--   Over a commutative ring $R$, with $s$ a natural number, the module sets up a two-chart Čech presentation of two projective lines glued at $s$ points, functions being Laurent polynomials in the coordinate of each line. The abbreviation `levalUnit R u` is evaluation $R[T;T^{-1}] \to R$ at a unit $u$ (the ring map $\mathrm{eval}_2$ of the identity of $R$ at $u$). The subalgebras `polyPart R` and `invPolyPart R` of $R[T;T^{-1}]$ are cut out by the support conditions that all exponents occurring in the coefficient support be $\ge 0$, respectively $\le 0$; `mem_polyPart_iff` and `mem_invPolyPart_iff` record these memberships. Given $a, b : \mathrm{Fin}\,s \to R^\times$, `gluedLinesOverlap R a b` is the $R$-subalgebra of pairs $(p,q) \in R[T;T^{-1}]^2$ with $p(a_i) = q(b_i)$ for every $i$, and `gluedLinesCover R a b` is the `Cover` with $A_{01}$ this subalgebra, $A_0$ its intersection with $\mathrm{polyPart} \times \mathrm{polyPart}$, $A_1$ its intersection with $\mathrm{invPolyPart} \times \mathrm{invPolyPart}$, and both restriction maps the subalgebra inclusions.
--
--   For a further unit vector $\lambda$, the predicate `GluedCond a b lam f` on $f = (p,q)$ asserts $p(a_i) = \lambda_i\, q(b_i)$ for all $i$; the lemmas `GluedCond.add`, `GluedCond.zero` and `GluedCond.mul` give closure under addition, vanishing, and multiplication by elements of the overlap algebra. Accordingly `gluedLinesM01` is the $A_{01}$-submodule of pairs satisfying `GluedCond`, `gluedLinesM0` its elements with both components in `polyPart`, and `gluedLinesM1 … n m` its elements with $p\,T^{-n}$ and $q\,T^{-m}$ in `invPolyPart`, i.e. exponents bounded above by $n$ and $m$. These assemble into `gluedLinesSections R a b lam n m`, a `Sections` of the above cover whose restriction maps are the inclusions into `gluedLinesM01`; its Čech $H^0$ therefore consists of pairs of polynomials of degrees at most $n$ and $m$ satisfying the $\lambda$-twisted gluing, and its $H^1$ is $M_{01}$ modulo the images of $M_0$ and $M_1$.
--
--   **Relation to Mathlib.** Laurent polynomials $R[T;T^{-1}]$, subalgebras and submodules are Mathlib's; `polyPart` and `invPolyPart` are defined here directly by support conditions rather than via Mathlib's polynomial-to-Laurent embedding. The `Cover`/`Sections` framework for two-chart Čech data is the project's own.
--
--   **Where it is used.** The construction provides an algebraic model for the special fibre of the Deligne–Rapoport model of $X_0(p)$, two rational curves meeting at the supersingular points, together with its line bundles of given multidegree and gluing data at the nodes, as needed in the analysis of the associated Picard scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_TwoChartCech_GluedLines.lean

import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Algebra.Subalgebra.Prod

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open LaurentPolynomial

universe u

namespace TwoChartCech

variable (R : Type u) [CommRing R] {s : ℕ}

abbrev levalUnit (u : Rˣ) : R[T;T⁻¹] →+* R := LaurentPolynomial.eval₂ (RingHom.id R) u

def polyPart : Subalgebra R R[T;T⁻¹] where
  carrier := {f | ∀ n ∈ f.coeff.support, 0 ≤ n}
  mul_mem' := by
    intro f g hf hg n hn
    classical
    obtain ⟨i, hi, j, hj, rfl⟩ :=
      Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset f g hn)
    exact add_nonneg (hf i hi) (hg j hj)
  add_mem' := by
    intro f g hf hg n hn
    rw [AddMonoidAlgebra.coeff_add] at hn
    rcases Finset.mem_union.mp (Finsupp.support_add hn) with h | h
    exacts [hf n h, hg n h]
  algebraMap_mem' := by
    intro r n hn
    rw [AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, AddMonoidAlgebra.coeff_single] at hn
    rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hn)]

def invPolyPart : Subalgebra R R[T;T⁻¹] where
  carrier := {f | ∀ n ∈ f.coeff.support, n ≤ 0}
  mul_mem' := by
    intro f g hf hg n hn
    classical
    obtain ⟨i, hi, j, hj, rfl⟩ :=
      Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset f g hn)
    exact add_nonpos (hf i hi) (hg j hj)
  add_mem' := by
    intro f g hf hg n hn
    rw [AddMonoidAlgebra.coeff_add] at hn
    rcases Finset.mem_union.mp (Finsupp.support_add hn) with h | h
    exacts [hf n h, hg n h]
  algebraMap_mem' := by
    intro r n hn
    rw [AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, AddMonoidAlgebra.coeff_single] at hn
    rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hn)]

theorem mem_polyPart_iff {f : R[T;T⁻¹]} : f ∈ polyPart R ↔ ∀ n ∈ f.coeff.support, 0 ≤ n := Iff.rfl

theorem mem_invPolyPart_iff {f : R[T;T⁻¹]} :
    f ∈ invPolyPart R ↔ ∀ n ∈ f.coeff.support, n ≤ 0 := Iff.rfl

def gluedLinesOverlap (a b : Fin s → Rˣ) : Subalgebra R (R[T;T⁻¹] × R[T;T⁻¹]) where
  carrier := {f | ∀ i, levalUnit R (a i) f.1 = levalUnit R (b i) f.2}
  mul_mem' := by
    intro f g hf hg i
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, hf i, hg i]
  add_mem' := by
    intro f g hf hg i
    simp only [Prod.fst_add, Prod.snd_add, map_add, hf i, hg i]
  algebraMap_mem' := by
    intro r i
    simp [Prod.algebraMap_apply, LaurentPolynomial.algebraMap_apply, LaurentPolynomial.eval₂_C]

@[reducible] def gluedLinesCover (a b : Fin s → Rˣ) : Cover.{u, u} R where
  A0 := ↥(gluedLinesOverlap R a b ⊓ (polyPart R).prod (polyPart R))
  A1 := ↥(gluedLinesOverlap R a b ⊓ (invPolyPart R).prod (invPolyPart R))
  A01 := ↥(gluedLinesOverlap R a b)
  ρ0 := Subalgebra.inclusion inf_le_left
  ρ1 := Subalgebra.inclusion inf_le_left

variable {R}

def GluedCond (a b lam : Fin s → Rˣ) (f : R[T;T⁻¹] × R[T;T⁻¹]) : Prop :=
  ∀ i, levalUnit R (a i) f.1 = lam i * levalUnit R (b i) f.2

theorem GluedCond.add {a b lam : Fin s → Rˣ} {f g : R[T;T⁻¹] × R[T;T⁻¹]} (hf : GluedCond a b lam f)
    (hg : GluedCond a b lam g) : GluedCond a b lam (f + g) := fun i => by
  simp only [Prod.fst_add, Prod.snd_add, map_add, hf i, hg i, mul_add]

theorem GluedCond.zero (a b lam : Fin s → Rˣ) : GluedCond a b lam 0 := fun i => by simp

theorem GluedCond.mul {a b lam : Fin s → Rˣ} {g f : R[T;T⁻¹] × R[T;T⁻¹]}
    (hg : g ∈ gluedLinesOverlap R a b) (hf : GluedCond a b lam f) : GluedCond a b lam (g * f) := fun i => by
  simp only [Prod.fst_mul, Prod.snd_mul, map_mul, hg i, hf i]
  ring

variable (R)

def gluedLinesM01 (a b lam : Fin s → Rˣ) :
    Submodule ↥(gluedLinesOverlap R a b) (R[T;T⁻¹] × R[T;T⁻¹]) where
  carrier := {f | GluedCond a b lam f}
  add_mem' := fun hf hg => hf.add hg
  zero_mem' := GluedCond.zero a b lam
  smul_mem' := fun g _ hf => GluedCond.mul g.2 hf

def gluedLinesM0 (a b lam : Fin s → Rˣ) :
    Submodule ↥(gluedLinesOverlap R a b ⊓ (polyPart R).prod (polyPart R)) (R[T;T⁻¹] × R[T;T⁻¹]) where
  carrier := {f | GluedCond a b lam f ∧ f ∈ (polyPart R).prod (polyPart R)}
  add_mem' := fun hf hg => ⟨hf.1.add hg.1, Subalgebra.add_mem _ hf.2 hg.2⟩
  zero_mem' := ⟨GluedCond.zero a b lam, Subalgebra.zero_mem _⟩
  smul_mem' := fun g _ hf => ⟨GluedCond.mul g.2.1 hf.1, Subalgebra.mul_mem _ g.2.2 hf.2⟩

def gluedLinesM1 (a b lam : Fin s → Rˣ) (n m : ℤ) :
    Submodule ↥(gluedLinesOverlap R a b ⊓ (invPolyPart R).prod (invPolyPart R)) (R[T;T⁻¹] × R[T;T⁻¹]) where
  carrier := {f | GluedCond a b lam f ∧ f.1 * T (-n) ∈ invPolyPart R ∧ f.2 * T (-m) ∈ invPolyPart R}
  add_mem' := fun {f g} hf hg => ⟨hf.1.add hg.1, by
    rw [Prod.fst_add, add_mul]; exact Subalgebra.add_mem _ hf.2.1 hg.2.1, by
    rw [Prod.snd_add, add_mul]; exact Subalgebra.add_mem _ hf.2.2 hg.2.2⟩
  zero_mem' := ⟨GluedCond.zero a b lam, by
    rw [Prod.fst_zero, zero_mul]; exact Subalgebra.zero_mem _, by
    rw [Prod.snd_zero, zero_mul]; exact Subalgebra.zero_mem _⟩
  smul_mem' := fun g f hf => ⟨GluedCond.mul g.2.1 hf.1, by
    rw [Subalgebra.smul_def, smul_eq_mul, Prod.fst_mul, mul_assoc]
    exact Subalgebra.mul_mem _ (Subalgebra.mem_prod.mp g.2.2).1 hf.2.1, by
    rw [Subalgebra.smul_def, smul_eq_mul, Prod.snd_mul, mul_assoc]
    exact Subalgebra.mul_mem _ (Subalgebra.mem_prod.mp g.2.2).2 hf.2.2⟩

def gluedLinesSections (a b lam : Fin s → Rˣ) (n m : ℤ) : Sections.{u, u, u} (gluedLinesCover R a b) :=
  { M0 := ↥(gluedLinesM0 R a b lam)
    M1 := ↥(gluedLinesM1 R a b lam n m)
    M01 := ↥(gluedLinesM01 R a b lam)
    M0_addCommGroup := inferInstance
    M0_moduleA := Submodule.module _
    M0_module := Submodule.module' _
    M0_tower := Submodule.isScalarTower _
    M1_addCommGroup := inferInstance
    M1_moduleA := Submodule.module _
    M1_module := Submodule.module' _
    M1_tower := Submodule.isScalarTower _
    M01_addCommGroup := inferInstance
    M01_moduleA := Submodule.module _
    M01_module := Submodule.module' _
    M01_tower := Submodule.isScalarTower _
    r0 := { toFun := fun f => ⟨f.1, f.2.1⟩, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    r1 := { toFun := fun f => ⟨f.1, f.2.1⟩, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    r0_smul := fun _ _ => rfl
    r1_smul := fun _ _ => rfl }

end TwoChartCech

end


