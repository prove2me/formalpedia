-- Prove2me | Definitions.Def_CKKSPrecision_FourierUnits_arithmetic_model
-- name    : CKKSPrecision_FourierUnits_arithmetic_model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:36:38.514344+00:00
-- url     : https://prove2.me/theorems/fbc954da-9513-47be-b1a6-d1e6f76d9594
-- title:
--   Cyclotomic rings, circular units and logarithmic lattices
-- statement:
--   Let $m>2$ be a conductor, let $\zeta$ be a primitive $m$th root, and put $K=\mathbb Q(\zeta)$ and $R=\mathbb Z[\zeta]$. The integral unit group consists of elements of $R$ whose inverse also lies in $R$. Define
--   $$
--   C_m=R^\times\cap\langle-1,\zeta,1-\zeta^a:1\le a<m\rangle\subset K^\times,
--   \qquad c_a=\frac{1-\zeta^a}{1-\zeta}.
--   $$
--   A representative set $S$ contains $1$ and exactly one representative of every pair $\{a,-a\}$ of invertible residues modulo $m$. Its elements are written as integers in $[1,m-1]$. The embedding $\sigma_a$ sends $\zeta$ to $\exp(2\pi i a/m)$. For the embeddings selected by $S$, set
--   $$
--   \operatorname{Log}(z)_a=\log_2|\sigma_a(z)|,
--   \quad \Lambda=\operatorname{Log}(R^\times),
--   \quad H=\{t:\sum_a t_a=0\}.
--   $$
--   The definitions also provide the actual subfield $K^+=\mathbb Q(\zeta+\zeta^{-1})$ and its ordinary ideal class number $h^+(m)$.
--
--   These are the arithmetic objects shared by the generation, index and construction statements. Unit membership never means merely nonvanishing in a field.
--
--   **Formalization Note** Mathlib's splitting field models $K$; the distinguished root is identified with the specified complex exponential by a fixed embedding. The additive logarithmic images use the type synonym `Multiplicative` solely to reuse subgroup-index notation. Their group law is vector addition. The logarithmic map on units includes the elementary multiplicativity verification needed to define its image subgroup. Definitions are total for positive conductors, but all arithmetic results require $m>2$.
-- source:
--   Zhaoyang Liang, Runkun Liu, Jingwei Fang, Dan Ding, A New Approach to Reducing Modulus Requirements in Homomorphic Computation: Precision Allocation in CKKS, STOC 2027 submission #148 (October 2026), pp. 4–5, Sections 2.1 and 2.3 (PDF pp. 6–7)

import Mathlib

set_option autoImplicit false

noncomputable section

namespace CKKSPrecision.FourierUnits

instance modulusNeZero (m : ℕ+) : NeZero (m : ℕ) := ⟨Nat.ne_of_gt m.pos⟩

/-- The paper's cyclotomic field, in Mathlib's splitting-field model. -/
abbrev K (m : ℕ+) := CyclotomicField (m : ℕ) ℚ

instance fieldCyclotomic (m : ℕ+) : IsCyclotomicExtension {(m : ℕ)} ℚ (K m) :=
  CyclotomicField.isCyclotomicExtension (m : ℕ) ℚ

/-- Distinguished primitive root; the base embedding below sends it to exp(2πi/m). -/
def zeta (m : ℕ+) : K m := IsCyclotomicExtension.zeta (m : ℕ) ℚ (K m)

/-- The actual integral coefficient ring Z[ζ], not the field's unit group. -/
def R (m : ℕ+) : Subalgebra ℤ (K m) := Algebra.adjoin ℤ {zeta m}

/-- Image of Rˣ in Kˣ. -/
def integralUnits (m : ℕ+) : Subgroup (K m)ˣ :=
  (Units.map (R m).val.toMonoidHom).range

/-- The full multiplicatively generated group in Kˣ from Section 2.3. -/
def circularGenerators (m : ℕ+) : Set (K m)ˣ :=
  {u | (u : K m) = -1 ∨ (u : K m) = zeta m ∨
    ∃ a : ℕ, 1 ≤ a ∧ a < (m : ℕ) ∧ (u : K m) = 1 - zeta m ^ a}

/-- C_m is an intersection, so nonintegral inverses of 1-ζ^a do not become ring units. -/
def cyclotomicUnits (m : ℕ+) : Subgroup (K m)ˣ :=
  integralUnits m ⊓ Subgroup.closure (circularGenerators m)

/-- c_a, with the exponent inside the subscript. -/
def c (m : ℕ+) (a : ℕ) : K m := (1 - zeta m ^ a) / (1 - zeta m)

/-- A choice of representatives of (Z/mZ)ˣ/{±1}, containing 1. -/
def IsRepresentatives (m : ℕ+) (S : Finset ℕ) : Prop :=
  1 ∈ S ∧ (∀ a ∈ S, 1 ≤ a ∧ a < (m : ℕ) ∧ Nat.Coprime a (m : ℕ)) ∧
    (∀ a : ℕ, 1 ≤ a → a < (m : ℕ) → Nat.Coprime a (m : ℕ) →
      ∃! b, b ∈ S ∧ (a % (m : ℕ) = b % (m : ℕ) ∨
        a % (m : ℕ) = ((m : ℕ) - b) % (m : ℕ)))

/-- Automorphism ζ ↦ ζ^a. The identity branch is only for noncoprime, unused indices. -/
def powerAut (m : ℕ+) (a : ℕ) : K m ≃ₐ[ℚ] K m :=
  if h : Nat.Coprime a (m : ℕ) then
    (IsCyclotomicExtension.autEquivPow (K m)
      (Polynomial.cyclotomic.irreducible_rat m.pos)).symm (ZMod.unitOfCoprime a h)
  else 1

/-- The embedding fixing the analytic convention ζ = exp(2πi/m). -/
def baseEmbedding (m : ℕ+) : K m →ₐ[ℚ] ℂ :=
  ((IsCyclotomicExtension.zeta_spec (m : ℕ) ℚ (K m)).embeddingsEquivPrimitiveRoots
    ℂ (Polynomial.cyclotomic.irreducible_rat m.pos)).symm
      ⟨Complex.exp (2 * Real.pi * Complex.I / (m : ℕ)),
        ((mem_primitiveRoots m.pos).mpr
          (Complex.isPrimitiveRoot_exp (m : ℕ) (Nat.ne_of_gt m.pos)))⟩

/-- Embedding σ_a(ζ)=exp(2πi a/m), for coprime a. -/
def embedding (m : ℕ+) (a : ℕ) : K m →ₐ[ℚ] ℂ :=
  (baseEmbedding m).comp (powerAut m a).toAlgHom

/-- Full selected-coordinate, base-two logarithm; only nonzero inputs are used in results. -/
def Log {m : ℕ+} {ι : Type*} (σ : ι → K m →ₐ[ℚ] ℂ) (z : K m) : ι → ℝ :=
  fun j => Real.log ‖σ j z‖ / Real.log 2

/-- The structural homomorphism underlying the logarithmic unit lattice. -/
def unitLog {m : ℕ+} {ι : Type*} (σ : ι → K m →ₐ[ℚ] ℂ) :
    (K m)ˣ →* Multiplicative (ι → ℝ) where
  toFun u := Multiplicative.ofAdd (Log σ (u : K m))
  map_one' := by
    funext j
    change Real.log ‖σ j 1‖ / Real.log 2 = 0
    simp
  map_mul' u v := by
    funext j
    change Real.log ‖σ j ((u : K m) * (v : K m))‖ / Real.log 2 =
      Real.log ‖σ j (u : K m)‖ / Real.log 2 + Real.log ‖σ j (v : K m)‖ / Real.log 2
    rw [map_mul, norm_mul, Real.log_mul
      (norm_ne_zero_iff.mpr ((map_ne_zero (σ j)).mpr u.ne_zero))
      (norm_ne_zero_iff.mpr ((map_ne_zero (σ j)).mpr v.ne_zero)), add_div]

/-- Λ and Log(C_m), using multiplicative notation for the additive vector group. -/
def unitLattice (m : ℕ+) (S : Finset ℕ) : Subgroup (Multiplicative (S → ℝ)) :=
  (integralUnits m).map (unitLog (fun a : S => embedding m a.val))

def circularLattice (m : ℕ+) (S : Finset ℕ) : Subgroup (Multiplicative (S → ℝ)) :=
  (cyclotomicUnits m).map (unitLog (fun a : S => embedding m a.val))

/-- The actual maximal real subfield Q(ζ+ζ⁻¹). -/
def realSubfield (m : ℕ+) : IntermediateField ℚ (K m) :=
  IntermediateField.adjoin ℚ {zeta m + (zeta m)⁻¹}

/-- Ordinary ideal class number of the maximal real subfield. -/
def realClassNumber (m : ℕ+) : ℕ := NumberField.classNumber (realSubfield m)

/-- The real zero-coordinate-sum hyperplane. -/
def H (ι : Type*) [Fintype ι] : Submodule ℝ (ι → ℝ) where
  carrier := {t | ∑ j, t j = 0}
  zero_mem' := by simp
  add_mem' := by intros a b ha hb; simp_all [Finset.sum_add_distrib]
  smul_mem' := by intros a b hb; simp_all [← Finset.mul_sum]

end CKKSPrecision.FourierUnits


