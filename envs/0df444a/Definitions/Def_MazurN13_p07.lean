-- Prove2me | Definitions.Def_MazurN13_p07
-- name    : MazurN13_p07
-- status  : Definition
-- author  : @xuanji
-- created : 2026-10-08T00:27:05.181953+00:00
-- url     : https://prove2.me/theorems/87631537-f7aa-4595-ac51-decc1e126b83
-- title:
--   Mazur order 13 (Huang FLT port), part 7/33
-- statement:
--   Part 7 of 33 of a machine-checked Lean proof that no elliptic curve over $\mathbb{Q}$ has a rational point of exact order $13$ (the case $N=13$ of Mazur's torsion theorem). The chain as a whole proves that the only rational affine points of the genus-two curve $Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$ (a model of $X_1(13)$) have $X\in\{0,-1\}$ (cusps); the final result is `MazurProof.N13ConstructedRationalPointTheorem.affine_x_is_cuspidal` in part {N}.
--
--   This part is not a single definition: it is a verbatim, sorry-free slice of Xiang Huang's Lean development, ported to this Mathlib and split into compile-sized pieces, each importing the previous part. It contains the modules:
--
--   - `FLT.PortCompat`
--   - `FLT.Assumptions.MazurProof.N13GaussianGlobalArithmetic`
--   - `FLT.Assumptions.MazurProof.PowerBasisDiscriminant`
--   - `FLT.Assumptions.MazurProof.N13GaussianCubicField`
--   - `FLT.Assumptions.MazurProof.N13GaussianFractionField`
--   - `FLT.Assumptions.MazurProof.N13GaussianFactorization`
--   - `FLT.Assumptions.MazurProof.N13SexticSquareclass`
--   - `FLT.Assumptions.MazurProof.N13GaussianCubic`
--   - `FLT.Assumptions.MazurProof.N13SexticIrreducible`
--   - `FLT.Assumptions.MazurProof.N13GaussianFieldEquiv`
--   - `FLT.Assumptions.MazurProof.N13MumfordKummerValue`
--   - `FLT.Assumptions.MazurProof.SexticMumfordFixedUnit`
--
--   Port notes: API drift fixes only (transparency options, renamed lemmas, explicit instances); local notations expanded, `private` removed.
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT commit 51bbb4f, directory FLT/Assumptions/MazurProof (N13* and SexticMumford* modules and their dependencies)

import Mathlib
import Definitions.Def_MazurN13_p06
set_option maxHeartbeats 1000000

-- module FLT.PortCompat
section

/-! Compatibility shims for porting to the platform Mathlib pin. -/

/-- The former hypothesis-taking form of `padicValRat.pow`. -/
theorem padicValRat.pow_of_ne_zero {p : ℕ} [Fact p.Prime] {q : ℚ} (_hq : q ≠ 0) {k : ℕ} :
    padicValRat p (q ^ k) = k * padicValRat p q :=
  padicValRat.pow q
end

-- module FLT.Assumptions.MazurProof.N13GaussianGlobalArithmetic
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GaussianGlobalArithmetic =====
section

/-!
# The Gaussian cubic at the ramified prime over 13

This file freezes the global Gaussian arithmetic attached to the actual N13
sextic

`X⁶ + 4X⁵ + 6X⁴ + 2X³ + X² + 2X + 1`.

Over `ℤ[i]` it is the product of a cubic and its conjugate.  The cubic has
discriminant `(3-2i)²`; after translating its root by `9`, it is Eisenstein at
the prime element `3-2i`.  Primality is proved from the Gaussian norm `13`,
and the Eisenstein constant-term test is the single norm nondivisibility
`13 ∤ 62197`.  No class-group computation or factor table is used.
-/

open Polynomial

namespace MazurProof.N13GaussianGlobalArithmetic

noncomputable section

abbrev GI := GaussianInt

/-- The standard Gaussian generator. -/
def i : GI := Zsqrtd.sqrtd

/-- The Gaussian prime above `13` at which the cubic is ramified. -/
def pi : GI := 3 - 2 * i

/-- The cubic Gaussian factor of the actual N13 sextic. -/
def g : GI[X] :=
  X ^ 3 + C (2 - 2 * i) * X ^ 2 +
    C (-1 - 2 * i) * X - 1

/-- The conjugate Gaussian cubic. -/
def gConj : GI[X] :=
  X ^ 3 + C (2 + 2 * i) * X ^ 2 +
    C (-1 + 2 * i) * X - 1

/-- Coefficient guard for the only N13 sextic used in this development. -/
def n13F : GI[X] :=
  X ^ 6 + 4 * X ^ 5 + 6 * X ^ 4 + 2 * X ^ 3 +
    X ^ 2 + 2 * X + 1

/-- The translate for which the ramified cubic is Eisenstein. -/
def h : GI[X] :=
  g.comp (X + C 9)

@[simp] theorem i_sq : i ^ 2 = -1 := by
  rfl

/-- The displayed cubic and its conjugate recover the exact N13 sextic. -/
theorem g_mul_conj :
    g * gConj = n13F := by
  have hCi : (C i : GI[X]) ^ 2 = -1 := by
    rw [← map_pow, i_sq, map_neg, map_one]
  simp only [g, gConj, n13F, map_add, map_sub, map_mul,
    map_ofNat, map_neg, map_one]
  ring_nf
  rw [hCi]
  ring

@[simp] theorem pi_norm : Zsqrtd.norm pi = 13 := by
  norm_num [pi, i, Zsqrtd.norm]

theorem pi_ne_zero : pi ≠ 0 := by
  intro hp
  have hnorm := congrArg Zsqrtd.norm hp
  rw [pi_norm] at hnorm
  norm_num at hnorm

/-- An element of Gaussian prime norm is irreducible.  Here the only fixed
arithmetic input is primality of `13`. -/
theorem pi_irreducible : Irreducible pi := by
  rw [irreducible_iff]
  constructor
  · intro hunit
    have hnorm : (Zsqrtd.norm pi).natAbs = 1 :=
      Zsqrtd.norm_eq_one_iff.mpr hunit
    rw [pi_norm] at hnorm
    norm_num at hnorm
  · intro a b hab
    have hnorm :
        (Zsqrtd.norm pi).natAbs =
          (Zsqrtd.norm a).natAbs * (Zsqrtd.norm b).natAbs := by
      simpa [Zsqrtd.norm_mul, Int.natAbs_mul] using
        congrArg (fun z : GI => (Zsqrtd.norm z).natAbs) hab
    rw [pi_norm] at hnorm
    have hp13 : Nat.Prime 13 := by
      decide
    rcases hp13.eq_one_or_self_of_dvd
        (Zsqrtd.norm a).natAbs
        ⟨(Zsqrtd.norm b).natAbs, hnorm⟩ with ha | ha
    · exact Or.inl (Zsqrtd.norm_eq_one_iff.mp ha)
    · right
      apply Zsqrtd.norm_eq_one_iff.mp
      norm_num at hnorm
      rw [ha] at hnorm
      omega

theorem pi_prime : Prime pi :=
  irreducible_iff_prime.mp pi_irreducible

theorem g_natDegree : g.natDegree = 3 := by
  unfold g
  compute_degree!

@[simp] theorem g_coeff_zero : g.coeff 0 = -1 := by
  simp only [g, coeff_add, coeff_sub, coeff_X_pow,
    coeff_C_mul_X_pow, coeff_one]
  norm_num [Polynomial.coeff_one]

@[simp] theorem g_coeff_one : g.coeff 1 = -1 - 2 * i := by
  simp only [g, coeff_add, coeff_sub, coeff_X_pow,
    coeff_C_mul_X_pow, coeff_one]
  norm_num [Polynomial.coeff_one]

@[simp] theorem g_coeff_two : g.coeff 2 = 2 - 2 * i := by
  simp only [g, coeff_add, coeff_sub, coeff_X_pow,
    coeff_C_mul_X_pow, coeff_one]
  norm_num [Polynomial.coeff_one]

@[simp] theorem g_coeff_three : g.coeff 3 = 1 := by
  simp only [g, coeff_add, coeff_sub, coeff_X_pow,
    coeff_C_mul_X_pow, coeff_one]
  norm_num [Polynomial.coeff_one]

theorem g_monic : g.Monic := by
  rw [Polynomial.Monic.def, Polynomial.leadingCoeff,
    g_natDegree, g_coeff_three]

/-- Exact factored coefficient form of the translated cubic. -/
theorem h_explicit :
    h =
      X ^ 3 +
        C (pi ^ 2 * (1 + 2 * i)) * X ^ 2 +
        C (pi * (70 + 34 * i)) * X +
        C (pi * (231 + 94 * i)) := by
  have h2 :
      (27 : GI) + (2 - 2 * i) =
        pi ^ 2 * (1 + 2 * i) := by
    ext <;> norm_num [pi, i, pow_two]
  have h1 :
      (243 : GI) + 18 * (2 - 2 * i) + (-1 - 2 * i) =
        pi * (70 + 34 * i) := by
    ext <;> norm_num [pi, i]
  have h0 :
      (729 : GI) + 81 * (2 - 2 * i) +
          9 * (-1 - 2 * i) - 1 =
        pi * (231 + 94 * i) := by
    ext <;> norm_num [pi, i]
  calc
    h =
        (X + C 9) ^ 3 +
          C (2 - 2 * i) * (X + C 9) ^ 2 +
          C (-1 - 2 * i) * (X + C 9) - 1 := by
      simp [h, g]
    _ =
        X ^ 3 +
          C ((27 : GI) + (2 - 2 * i)) * X ^ 2 +
          C ((243 : GI) + 18 * (2 - 2 * i) +
            (-1 - 2 * i)) * X +
          C ((729 : GI) + 81 * (2 - 2 * i) +
            9 * (-1 - 2 * i) - 1) := by
      simp only [map_add, map_sub, map_mul, map_ofNat,
        map_neg, map_one]
      ring
    _ = _ := by rw [h2, h1, h0]

theorem h_monic : h.Monic :=
  g_monic.comp_X_add_C 9

theorem h_natDegree : h.natDegree = 3 := by
  simp [h, Polynomial.natDegree_comp, g_natDegree]

theorem h_degree : h.degree = 3 :=
  (degree_eq_iff_natDegree_eq h_monic.ne_zero).mpr h_natDegree

@[simp] theorem h_coeff_zero :
    h.coeff 0 = pi * (231 + 94 * i) := by
  rw [h_explicit]
  simp

@[simp] theorem h_coeff_one :
    h.coeff 1 = pi * (70 + 34 * i) := by
  rw [h_explicit]
  simp only [coeff_add, coeff_X_pow, coeff_C_mul_X_pow, coeff_C]
  norm_num

@[simp] theorem h_coeff_two :
    h.coeff 2 = pi ^ 2 * (1 + 2 * i) := by
  rw [h_explicit]
  simp only [coeff_add, coeff_X_pow, coeff_C_mul_X_pow, coeff_C]
  norm_num

@[simp] theorem h_coeff_three :
    h.coeff 3 = 1 := by
  simpa [h_natDegree] using h_monic.coeff_natDegree

/-- Translation preserves the computed discriminant; here this is verified
directly from the cubic formula. -/
theorem h_discr : h.discr = pi ^ 2 := by
  rw [Polynomial.discr_of_degree_eq_three h_degree]
  rw [h_coeff_zero, h_coeff_one, h_coeff_two, h_coeff_three]
  ext <;> norm_num [pi, i, pow_two, pow_succ]

theorem pi_not_dvd_constantQuotient :
    ¬ pi ∣ (231 + 94 * i) := by
  rintro ⟨d, hd⟩
  have hnorm := congrArg Zsqrtd.norm hd
  rw [Zsqrtd.norm_mul, pi_norm] at hnorm
  have hc : Zsqrtd.norm (231 + 94 * i : GI) = 62197 := by
    norm_num [i, Zsqrtd.norm]
  rw [hc] at hnorm
  omega

theorem pi_span_prime :
    (Ideal.span ({pi} : Set GI)).IsPrime :=
  (Ideal.span_singleton_prime pi_ne_zero).mpr pi_prime

/-- The translated cubic is Eisenstein at the unique displayed ramified
Gaussian prime. -/
theorem h_eisenstein :
    h.IsEisensteinAt (Ideal.span ({pi} : Set GI)) := by
  apply h_monic.isEisensteinAt_of_mem_of_notMem pi_span_prime.ne_top
  · intro n hn
    rw [h_natDegree] at hn
    interval_cases n
    · rw [h_coeff_zero, Ideal.mem_span_singleton]
      exact dvd_mul_right pi _
    · rw [h_coeff_one, Ideal.mem_span_singleton]
      exact dvd_mul_right pi _
    · rw [h_coeff_two, Ideal.mem_span_singleton]
      exact ⟨pi * (1 + 2 * i), by ring⟩
  · intro hmem
    rw [h_coeff_zero, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at hmem
    rcases hmem with ⟨d, hd⟩
    apply pi_not_dvd_constantQuotient
    refine ⟨d, ?_⟩
    apply mul_left_cancel₀ pi_ne_zero
    calc
      pi * (231 + 94 * i) = pi ^ 2 * d := hd
      _ = pi * (pi * d) := by ring

end

end MazurProof.N13GaussianGlobalArithmetic

end
end

-- module FLT.Assumptions.MazurProof.PowerBasisDiscriminant
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.PowerBasisDiscriminant =====
section

/-!
# Structural discriminant identities for power bases

This file supplies two small bridges missing from Mathlib's public API:

* the norm of `q(θ)` is the resultant of the minimal polynomial of `θ`
  with `q`;
* the trace discriminant of a power basis is the polynomial discriminant
  of its minimal polynomial.

The norm proof reindexes the canonical product over embeddings by the
canonical multiset of roots.  It does not choose or enumerate roots and it
does not expand a multiplication matrix.
-/

open Polynomial
open scoped Polynomial BigOperators

namespace MazurProof.PowerBasisDiscriminant

noncomputable section

/-- The norm of a polynomial in a power-basis generator is the resultant
with the generator's minimal polynomial. -/
theorem norm_aeval_eq_resultant
    {K L : Type*}
    [Field K] [Field L]
    [Algebra K L]
    [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (B : PowerBasis K L)
    (q : K[X]) :
    Algebra.norm K (Polynomial.aeval B.gen q) =
      (minpoly K B.gen).resultant q := by
  let E := AlgebraicClosure L
  letI := Classical.decEq E

  have hres :
      algebraMap K E ((minpoly K B.gen).resultant q) =
        (((minpoly K B.gen).aroots E).map
          (fun y => Polynomial.aeval y q)).prod := by
    rw [← Polynomial.resultant_map_map
      (f := minpoly K B.gen)
      (g := q)
      (m := (minpoly K B.gen).natDegree)
      (n := q.natDegree)
      (algebraMap K E)]
    have hr :=
      Polynomial.resultant_eq_prod_eval
        ((minpoly K B.gen).map (algebraMap K E))
        (q.map (algebraMap K E))
        q.natDegree
        Polynomial.natDegree_map_le
        (IsAlgClosed.splits _)
    rw [((minpoly.monic B.isIntegral_gen).map
      (algebraMap K E)).leadingCoeff, one_pow, one_mul] at hr
    simpa only [Polynomial.aroots_def,
      Polynomial.eval_map_algebraMap,
      (minpoly.monic B.isIntegral_gen).natDegree_map] using hr

  apply (algebraMap K E).injective
  rw [Algebra.norm_eq_prod_embeddings K E]
  rw [hres]
  calc
    (∏ σ : L →ₐ[K] E, σ (Polynomial.aeval B.gen q)) =
        ∏ y : {y // y ∈ (minpoly K B.gen).aroots E},
          Polynomial.aeval y.1 q := by
      apply Fintype.prod_equiv B.liftEquiv'
      intro σ
      simp only [PowerBasis.liftEquiv'_apply_coe]
      exact (Polynomial.aeval_algHom_apply σ B.gen q).symm
    _ = (((minpoly K B.gen).aroots E).map
          (fun y => Polynomial.aeval y q)).prod := by
      rw [Finset.prod_mem_multiset,
      Finset.prod_eq_multiset_prod,
      Multiset.toFinset_val,
      Multiset.dedup_eq_self.mpr]
      · exact nodup_roots
          (Separable.map
            (Algebra.IsSeparable.isSeparable K B.gen))
      · intro y
        rfl

/-- The trace discriminant of a power basis is the polynomial discriminant
of its minimal polynomial. -/
theorem discr_basis_eq_minpoly_discr
    {K L : Type*}
    [Field K] [Field L]
    [Algebra K L]
    [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (B : PowerBasis K L) :
    Algebra.discr K B.basis =
      (minpoly K B.gen).discr := by
  rw [Algebra.discr_powerBasis_eq_norm K B]
  rw [norm_aeval_eq_resultant B]
  let f := minpoly K B.gen
  have hfmonic : f.Monic :=
    minpoly.monic B.isIntegral_gen
  have hderiv :
      f.derivative.natDegree ≤ f.natDegree - 1 :=
    Polynomial.natDegree_derivative_le f
  have hpad :
      f.resultant f.derivative =
        f.resultant f.derivative f.natDegree (f.natDegree - 1) := by
    symm
    calc
      f.resultant f.derivative f.natDegree (f.natDegree - 1) =
          f.resultant f.derivative f.natDegree
            (f.derivative.natDegree +
              ((f.natDegree - 1) - f.derivative.natDegree)) := by
        rw [Nat.add_sub_of_le hderiv]
      _ = f.coeff f.natDegree ^
            ((f.natDegree - 1) - f.derivative.natDegree) *
          f.resultant f.derivative f.natDegree
            f.derivative.natDegree := by
        rw [Polynomial.resultant_add_right_deg
          f f.derivative f.natDegree f.derivative.natDegree
          ((f.natDegree - 1) - f.derivative.natDegree) le_rfl]
      _ = f.resultant f.derivative := by
        rw [Polynomial.coeff_natDegree, hfmonic.leadingCoeff]
        simp
  rw [hpad]
  have hdeg : 0 < (minpoly K B.gen).degree := by
    rw [B.degree_minpoly]
    simpa using B.dim_pos
  rw [Polynomial.resultant_deriv hdeg]
  rw [(minpoly.monic B.isIntegral_gen).leadingCoeff, mul_one]
  rw [B.natDegree_minpoly, ← B.finrank]
  rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp

/-- Polynomial discriminant commutes with a coefficient map for a
positive-degree monic polynomial. -/
theorem discr_map_of_monic_of_degree_pos
    {R S : Type*}
    [CommRing R] [Field S]
    (φ : R →+* S)
    {f : R[X]}
    (hf : f.Monic)
    (hdeg : 0 < f.degree) :
    (f.map φ).discr = φ f.discr := by
  have hdeg' : 0 < (f.map φ).degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos,
      hf.natDegree_map φ,
      Polynomial.natDegree_pos_iff_degree_pos]
    exact hdeg
  have hbase := Polynomial.resultant_deriv hdeg
  have hmap := congrArg φ hbase
  have htarget := Polynomial.resultant_deriv hdeg'
  rw [Polynomial.derivative_map, hf.natDegree_map φ] at htarget
  rw [← Polynomial.resultant_map_map
      (f := f)
      (g := f.derivative)
      (m := f.natDegree)
      (n := f.natDegree - 1)
      φ] at hmap
  have heq :
      (-1 : S) ^
          (f.natDegree * (f.natDegree - 1) / 2) *
        (f.map φ).discr =
      (-1 : S) ^
          (f.natDegree * (f.natDegree - 1) / 2) *
        φ f.discr := by
    simpa [hf.leadingCoeff, (hf.map φ).leadingCoeff]
      using htarget.symm.trans hmap
  exact mul_left_cancel₀
    (pow_ne_zero _
      (neg_ne_zero.mpr one_ne_zero : (-1 : S) ≠ 0))
    heq

/-- For an integral power-basis generator over an integrally closed base,
the basis discriminant is the image of its integral minimal-polynomial
discriminant. -/
theorem powerBasis_discr_eq_map_discr
    {R K L : Type*}
    [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R]
    [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K]
    [Algebra K L] [Algebra R L]
    [IsScalarTower R K L]
    [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (B : PowerBasis K L)
    (hBint : IsIntegral R B.gen)
    (h : R[X])
    (hmin : minpoly R B.gen = h) :
    Algebra.discr K B.basis =
      algebraMap R K h.discr := by
  rw [discr_basis_eq_minpoly_discr B]
  have hminK :
      minpoly K B.gen =
        h.map (algebraMap R K) := by
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hBint, hmin]
  have hhmonic : h.Monic := by
    rw [← hmin]
    exact minpoly.monic hBint
  have hnat : h.natDegree = B.dim := by
    rw [← hhmonic.natDegree_map (algebraMap R K)]
    rw [← hminK]
    exact B.natDegree_minpoly
  have hdeg : 0 < h.degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos, hnat]
    exact B.dim_pos
  rw [hminK]
  exact discr_map_of_monic_of_degree_pos
    (algebraMap R K) hhmonic hdeg

/-- Literal rational `AdjoinRoot` specialization of the norm--resultant
identity. -/
theorem norm_aeval_adjoinRoot_eq_resultant
    {f : ℚ[X]}
    (hf : f.Monic)
    (hirr : Irreducible f)
    (q : ℚ[X]) :
    Algebra.norm ℚ
        (Polynomial.aeval (AdjoinRoot.root f) q) =
      f.resultant q := by
  letI : Fact (Irreducible f) := ⟨hirr⟩
  let B : PowerBasis ℚ (AdjoinRoot f) :=
    AdjoinRoot.powerBasis hf.ne_zero
  letI : Module.Finite ℚ (AdjoinRoot f) :=
    B.finite
  have h := norm_aeval_eq_resultant B q
  have hmin : minpoly ℚ B.gen = f := by
    exact AdjoinRoot.minpoly_powerBasis_gen_of_monic hf
  rw [hmin] at h
  exact h

end

end MazurProof.PowerBasisDiscriminant

end
end

-- module FLT.Assumptions.MazurProof.N13GaussianCubicField
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GaussianCubicField =====
section

/-!
# The global N13 Gaussian cubic field

We form the fraction field `K = Frac(ℤ[i])` and adjoin a root of the
translated Gaussian cubic.  Its Eisenstein property proves irreducibility,
while the discriminant--Eisenstein criterion identifies the monogenic
Gaussian order with the full relative integral closure.

This file contains no class-group computation and no integral-basis search.
-/

open Algebra Module Polynomial
open scoped nonZeroDivisors

namespace MazurProof.N13GaussianCubicField

noncomputable section

open N13GaussianGlobalArithmetic

/-- The Gaussian rational field, kept as the literal fraction field of
`GaussianInt` so the integral-closure API applies definitionally. -/
abbrev K := FractionRing GI

/-- The translated cubic over the Gaussian rational field. -/
def hK : K[X] :=
  h.map (algebraMap GI K)

theorem hK_monic : hK.Monic :=
  h_monic.map (algebraMap GI K)

/-- Eisenstein gives irreducibility already over `ℤ[i]`. -/
theorem h_irreducible : Irreducible h :=
  h_eisenstein.irreducible pi_span_prime h_monic.isPrimitive
    (by rw [h_natDegree]; norm_num)

/-- Gauss's lemma transports the structural Eisenstein proof to the
Gaussian fraction field. -/
theorem hK_irreducible : Irreducible hK := by
  exact
    h_monic.isPrimitive.irreducible_iff_irreducible_map_fraction_map.mp
      h_irreducible

@[reducible] def hKIrreducibleFact :
    Fact (Irreducible hK) :=
  ⟨hK_irreducible⟩

/-- The relative cubic field. -/
abbrev L := AdjoinRoot hK

/-- Exported opt-in field structure for downstream arithmetic files. -/
@[reducible] noncomputable def cubicField : Field L := by
  letI := hKIrreducibleFact
  infer_instance

local instance : Fact (Irreducible hK) :=
  hKIrreducibleFact

local instance fieldL : Field L :=
  AdjoinRoot.instField

/-- The shifted cubic generator. -/
def alpha : L :=
  AdjoinRoot.root hK

/-- The relative power basis `1, α, α²`. -/
def powerBasis : PowerBasis K L :=
  AdjoinRoot.powerBasis hK_monic.ne_zero

local instance finiteKL : Module.Finite K L :=
  powerBasis.finite

local instance separableKL : Algebra.IsSeparable K L :=
  inferInstance

@[simp] theorem powerBasis_gen :
    powerBasis.gen = alpha := by
  rfl

theorem powerBasis_dim :
    powerBasis.dim = 3 := by
  rw [powerBasis, AdjoinRoot.powerBasis_dim]
  rw [hK, h_monic.natDegree_map]
  exact h_natDegree

/-- The relative field basis `(1, α, α²)` with fixed index `Fin 3`. -/
def relativeFieldBasis : Basis (Fin 3) K L :=
  powerBasis.basis.reindex (finCongr powerBasis_dim)

@[simp] theorem relativeFieldBasis_apply (j : Fin 3) :
    relativeFieldBasis j = alpha ^ (j : ℕ) := by
  rw [relativeFieldBasis, Basis.reindex_apply,
    powerBasis.basis_eq_pow]
  have hindex :
      (((finCongr powerBasis_dim).symm j) : ℕ) =
        (j : ℕ) := rfl
  rw [hindex, powerBasis_gen]

/-- The shifted generator is integral over the Gaussian integers. -/
theorem alpha_integral : IsIntegral GI alpha := by
  refine ⟨h, h_monic, ?_⟩
  have hmap :
      algebraMap GI L =
        (algebraMap K L).comp (algebraMap GI K) :=
    IsScalarTower.algebraMap_eq GI K L
  change h.eval₂ (algebraMap GI L) alpha = 0
  rw [hmap]
  rw [← Polynomial.eval₂_map]
  exact AdjoinRoot.eval₂_root hK

/-- The integral minimal polynomial is exactly the translated cubic. -/
theorem minpoly_alpha :
    minpoly GI alpha = h := by
  apply Polynomial.map_injective
    (f := algebraMap GI K)
    (FaithfulSMul.algebraMap_injective GI K)
  calc
    (minpoly GI alpha).map (algebraMap GI K) =
        minpoly K alpha :=
      (minpoly.isIntegrallyClosed_eq_field_fractions'
        K alpha_integral).symm
    _ = hK := by
      change minpoly K (AdjoinRoot.root hK) = hK
      exact AdjoinRoot.minpoly_powerBasis_gen_of_monic hK_monic
    _ = h.map (algebraMap GI K) := rfl

/-- Relative trace discriminant of the shifted power basis. -/
theorem powerBasis_discr :
    Algebra.discr K powerBasis.basis =
      algebraMap GI K (pi ^ 2) := by
  exact
    PowerBasisDiscriminant.powerBasis_discr_eq_map_discr
      powerBasis alpha_integral h minpoly_alpha
      |>.trans (congrArg (algebraMap GI K) h_discr)

/-- The monogenic Gaussian order is the full relative integral closure. -/
theorem integralClosure_eq_adjoin :
    integralClosure GI L =
      Algebra.adjoin GI ({alpha} : Set L) := by
  apply integralClosure_eq_adjoin_of_discr_eq_prime_pow
    (B := powerBasis) (p := pi) (n := 2)
  · exact pi_prime
  · simpa [powerBasis_gen] using alpha_integral
  · exact powerBasis_discr
  · simpa [powerBasis_gen, minpoly_alpha] using h_eisenstein

/-! ## The relative integral basis -/

local instance faithfulGIL : FaithfulSMul GI L := by
  rw [faithfulSMul_iff_algebraMap_injective]
  intro x y hxy
  apply IsFractionRing.injective GI K
  apply (algebraMap K L).injective
  have hmap :
      algebraMap GI L =
        (algebraMap K L).comp (algebraMap GI K) :=
    IsScalarTower.algebraMap_eq GI K L
  rw [hmap] at hxy
  exact hxy

/-- The power basis on the generated Gaussian order, transported to the
proved relative integral closure. -/
def relativeIntegralPowerBasis :
    PowerBasis GI (integralClosure GI L) :=
  (Algebra.adjoin.powerBasis' (R := GI) alpha_integral).map
    (Subalgebra.equivOfEq _ _
      integralClosure_eq_adjoin.symm)

@[simp] theorem relativeIntegralPowerBasis_dim :
    relativeIntegralPowerBasis.dim = 3 := by
  simp [relativeIntegralPowerBasis, minpoly_alpha,
    h_natDegree]

@[simp] theorem coe_relativeIntegralPowerBasis_gen :
    ((relativeIntegralPowerBasis.gen :
        integralClosure GI L) : L) = alpha := by
  simp [relativeIntegralPowerBasis]

/-- The literal relative integral basis `(1, α, α²)`. -/
def relativeIntegralBasis :
    Basis (Fin 3) GI (integralClosure GI L) :=
  relativeIntegralPowerBasis.basis.reindex
    (finCongr relativeIntegralPowerBasis_dim)

@[simp] theorem coe_relativeIntegralBasis_apply
    (j : Fin 3) :
    ((relativeIntegralBasis j :
        integralClosure GI L) : L) =
      alpha ^ (j : ℕ) := by
  rw [relativeIntegralBasis, Basis.reindex_apply,
    relativeIntegralPowerBasis.basis_eq_pow]
  have hindex :
      (((finCongr relativeIntegralPowerBasis_dim).symm j) :
        ℕ) = (j : ℕ) := rfl
  change
    ((relativeIntegralPowerBasis.gen :
      integralClosure GI L) : L) ^
        (((finCongr relativeIntegralPowerBasis_dim).symm j) :
          ℕ) =
      alpha ^ (j : ℕ)
  rw [coe_relativeIntegralPowerBasis_gen]
  rw [hindex]

@[simp] theorem coe_relativeIntegralBasis_zero :
    ((relativeIntegralBasis 0 :
        integralClosure GI L) : L) = 1 := by
  simp

@[simp] theorem coe_relativeIntegralBasis_one :
    ((relativeIntegralBasis 1 :
        integralClosure GI L) : L) = alpha := by
  simp

@[simp] theorem coe_relativeIntegralBasis_two :
    ((relativeIntegralBasis 2 :
        integralClosure GI L) : L) = alpha ^ 2 := by
  simp

/-! ## Discriminant of the relative integral basis -/

local instance integralClosureLocalization :
    IsLocalization
      (Algebra.algebraMapSubmonoid
        (integralClosure GI L) (nonZeroDivisors GI)) L :=
  IsIntegralClosure.isLocalization
    GI K L (integralClosure GI L)

/-- Localizing the relative integral basis gives the literal relative field
basis. -/
def localizedRelativeIntegralBasis :
    Basis (Fin 3) K L :=
  Basis.localizationLocalization
    K (nonZeroDivisors GI) L relativeIntegralBasis

theorem localizedRelativeIntegralBasis_eq :
    localizedRelativeIntegralBasis = relativeFieldBasis := by
  ext j
  simp [localizedRelativeIntegralBasis]

theorem relativeFieldBasis_discr :
    Algebra.discr K relativeFieldBasis =
      algebraMap GI K (pi ^ 2) := by
  calc
    Algebra.discr K relativeFieldBasis =
        Algebra.discr K powerBasis.basis := by
      simpa [relativeFieldBasis] using
        (Algebra.discr_reindex K powerBasis.basis
          (finCongr powerBasis_dim))
    _ = algebraMap GI K (pi ^ 2) :=
      powerBasis_discr

/-- The relative integral basis has discriminant `π²`. -/
theorem relativeIntegralBasis_discr :
    Algebra.discr GI relativeIntegralBasis = pi ^ 2 := by
  apply IsFractionRing.injective GI K
  calc
    algebraMap GI K
        (Algebra.discr GI relativeIntegralBasis) =
        Algebra.discr K localizedRelativeIntegralBasis :=
      (Algebra.discr_localizationLocalization
        GI (nonZeroDivisors GI) L
        relativeIntegralBasis).symm
    _ = Algebra.discr K relativeFieldBasis := by
      rw [localizedRelativeIntegralBasis_eq]
    _ = algebraMap GI K (pi ^ 2) :=
      relativeFieldBasis_discr

end

end MazurProof.N13GaussianCubicField

end
end

-- module FLT.Assumptions.MazurProof.N13GaussianFractionField
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GaussianFractionField =====
section

/-!
# The Gaussian fraction field as a quadratic number field

The fraction field of `ℤ[i]` has the structural rational basis `(1,i)`.
The only localization point to check is that inverting nonzero ordinary
integers already inverts every nonzero Gaussian integer: `z` divides its
nonzero integer norm `z * star z`.

No embeddings or Gaussian elements are enumerated.
-/

open Module
open Polynomial
open scoped nonZeroDivisors
open scoped Matrix

namespace MazurProof.N13GaussianFractionField

noncomputable section

open N13GaussianGlobalArithmetic

/-- The Gaussian rational field. -/
abbrev K := FractionRing GI

@[simp] theorem i_mul_self :
    i * i = -1 := by
  simp [i, Zsqrtd.dmuld]

/-- The Gaussian generator is integral over the integers. -/
theorem i_integral : IsIntegral ℤ i := by
  refine ⟨X ^ 2 + C (1 : ℤ), ?_, ?_⟩
  · exact Polynomial.monic_X_pow_add_C (1 : ℤ)
      (by norm_num)
  · simp [i, pow_two, Zsqrtd.dmuld]

/-- Every Gaussian integer is integral over `ℤ`, structurally from its
decomposition `a + i b`. -/
instance gaussianIntIntegral :
    Algebra.IsIntegral ℤ GI where
  isIntegral := by
    rintro ⟨a, b⟩
    rw [Zsqrtd.decompose]
    exact
      (isIntegral_intCast a).add
        (i_integral.mul (isIntegral_intCast b))

/-! ## The integral basis `(1,i)` -/

/-- Gaussian real and imaginary coordinates as an additive equivalence. -/
def gaussianIntAddEquiv : GI ≃+ (Fin 2 → ℤ) where
  toFun := fun z j => Fin.cases z.re (fun _ => z.im) j
  invFun := fun v => ⟨v 0, v 1⟩
  left_inv := by
    intro z
    ext <;> rfl
  right_inv := by
    intro v
    funext j
    fin_cases j <;> rfl
  map_add' := by
    intro x y
    funext j
    fin_cases j <;> rfl

/-- The coordinate equivalence as an integer-linear equivalence. -/
def gaussianIntLinearEquiv : GI ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  gaussianIntAddEquiv.toIntLinearEquiv

/-- The structural integral basis `(1,i)` of the Gaussian integers. -/
def gaussianIntBasis : Basis (Fin 2) ℤ GI :=
  Basis.ofEquivFun gaussianIntLinearEquiv

instance gaussianIntFree : Module.Free ℤ GI :=
  Module.Free.of_basis gaussianIntBasis

instance gaussianIntFinite : Module.Finite ℤ GI :=
  Module.Finite.of_basis gaussianIntBasis

@[simp] theorem gaussianIntBasis_repr_apply
    (z : GI) (j : Fin 2) :
    gaussianIntBasis.repr z j =
      Fin.cases z.re (fun _ => z.im) j := by
  rfl

@[simp] theorem gaussianIntBasis_zero :
    gaussianIntBasis (0 : Fin 2) = 1 := by
  apply gaussianIntBasis.ext_elem
  intro j
  rw [gaussianIntBasis.repr_self_apply]
  fin_cases j <;> rfl

@[simp] theorem gaussianIntBasis_one :
    gaussianIntBasis (1 : Fin 2) = i := by
  apply gaussianIntBasis.ext_elem
  intro j
  rw [gaussianIntBasis.repr_self_apply]
  fin_cases j <;> rfl

/-! ## Cofinality of ordinary integer denominators -/

/-- Images of nonzero ordinary integers in `ℤ[i]`. -/
abbrev intDenoms : Submonoid GI :=
  Algebra.algebraMapSubmonoid GI (nonZeroDivisors ℤ)

theorem intDenoms_le_nonZeroDivisors :
    intDenoms ≤ nonZeroDivisors GI := by
  rintro _ ⟨n, hn, rfl⟩
  rw [mem_nonZeroDivisors_iff_ne_zero]
  exact
    (RingHom.injective_int (algebraMap ℤ GI)).ne
      (nonZeroDivisors.ne_zero hn)

/-- Every nonzero Gaussian denominator divides a nonzero ordinary integer:
choose its norm. -/
theorem nonZeroGaussian_dvd_intDenom
    (z : GI) (hz : z ∈ nonZeroDivisors GI) :
    ∃ m ∈ intDenoms, z ∣ m := by
  have hz0 : z ≠ 0 :=
    nonZeroDivisors.ne_zero hz
  have hnorm0 : Zsqrtd.norm z ≠ 0 := by
    simpa using hz0
  refine ⟨(Zsqrtd.norm z : GI), ?_, ?_⟩
  · have hm : Zsqrtd.norm z ∈ nonZeroDivisors ℤ :=
      mem_nonZeroDivisors_iff_ne_zero.mpr hnorm0
    simpa [intDenoms] using
      (Algebra.mem_algebraMapSubmonoid_of_mem
        (S := GI)
        (⟨Zsqrtd.norm z, hm⟩ : nonZeroDivisors ℤ))
  · exact ⟨star z, Zsqrtd.norm_eq_mul_conj z⟩

/-- The Gaussian fraction field is also the localization obtained by
inverting only the nonzero ordinary integers. -/
instance intDenomLocalization :
    IsLocalization intDenoms K := by
  refine
    (IsLocalization.iff_of_le_of_exists_dvd
      (S := K)
      (M := intDenoms)
      (nonZeroDivisors GI)
      intDenoms_le_nonZeroDivisors
      ?_).2 inferInstance
  intro z hz
  exact nonZeroGaussian_dvd_intDenom z hz

/-! ## The localized rational basis -/

instance intRatAlgebraScalarTower :
    @IsScalarTower ℤ ℚ K
      (@Algebra.toSMul ℤ ℚ _ _ inferInstance)
      (@Algebra.toSMul ℚ K _ _ inferInstance)
      (@Algebra.toSMul ℤ K _ _ inferInstance) :=
  IsScalarTower.of_algebraMap_eq fun z => by
    have hmaps :
        algebraMap ℤ K =
          (algebraMap ℚ K).comp (algebraMap ℤ ℚ) :=
      RingHom.ext_int _ _
    exact DFunLike.congr_fun hmaps z

/-- The rational basis `(1,i)` of `Frac(ℤ[i])`. -/
def gaussianBasis : Basis (Fin 2) ℚ K :=
  Basis.localizationLocalization
    ℚ (nonZeroDivisors ℤ) K gaussianIntBasis

@[simp] theorem gaussianBasis_apply (j : Fin 2) :
    gaussianBasis j =
      algebraMap GI K (gaussianIntBasis j) :=
  Basis.localizationLocalization_apply
    ℚ (nonZeroDivisors ℤ) K gaussianIntBasis j

/-- The Gaussian generator in its fraction field. -/
def iK : K :=
  algebraMap GI K i

@[simp] theorem gaussianBasis_zero :
    gaussianBasis (0 : Fin 2) = 1 := by
  simp [gaussianBasis]

@[simp] theorem gaussianBasis_one :
    gaussianBasis (1 : Fin 2) = iK := by
  simp [gaussianBasis, iK]

@[simp] theorem iK_mul_self :
    iK * iK = -1 := by
  change algebraMap GI K i * algebraMap GI K i = -1
  rw [← map_mul, i_mul_self, map_neg, map_one]

@[simp] theorem gaussianBasis_repr_algebraMap
    (z : GI) (j : Fin 2) :
    gaussianBasis.repr (algebraMap GI K z) j =
      algebraMap ℤ ℚ (gaussianIntBasis.repr z j) :=
  Basis.localizationLocalization_repr_algebraMap
    ℚ (nonZeroDivisors ℤ) K gaussianIntBasis z j

instance gaussianFiniteDimensional :
    FiniteDimensional ℚ K :=
  Module.Finite.of_basis gaussianBasis

theorem finrank_K :
    Module.finrank ℚ K = 2 := by
  rw [Module.finrank_eq_card_basis gaussianBasis]
  simp

instance gaussianNumberField : NumberField K where
  to_charZero := inferInstance
  to_finiteDimensional := gaussianFiniteDimensional

/-! ## Power basis, minimal polynomial, and discriminant -/

/-- The quadratic polynomial of the Gaussian generator. -/
def gaussianMinpoly : ℚ[X] :=
  X ^ 2 + 1

/-- The rational basis `(1,i)` is the power basis generated by `i`. -/
def gaussianPowerBasis : PowerBasis ℚ K where
  gen := iK
  dim := 2
  basis := gaussianBasis
  basis_eq_pow := by
    intro j
    fin_cases j
    · simp
    · simpa using gaussianBasis_one

@[simp] theorem gaussianPowerBasis_gen :
    gaussianPowerBasis.gen = iK := rfl

@[simp] theorem gaussianPowerBasis_dim :
    gaussianPowerBasis.dim = 2 := rfl

@[simp] theorem gaussianPowerBasis_basis :
    gaussianPowerBasis.basis = gaussianBasis := rfl

theorem gaussianMinpoly_monic :
    gaussianMinpoly.Monic := by
  simpa [gaussianMinpoly] using
    (Polynomial.monic_X_pow_add_C (1 : ℚ)
      (show (2 : ℕ) ≠ 0 by decide))

@[simp] theorem aeval_gaussianMinpoly :
    Polynomial.aeval iK gaussianMinpoly = 0 := by
  simp [gaussianMinpoly, pow_two, iK_mul_self]

theorem gaussianMinpoly_degree :
    gaussianMinpoly.degree = ((2 : ℕ) : WithBot ℕ) := by
  change Polynomial.degree ((X : ℚ[X]) ^ 2 + C 1) =
    ((2 : ℕ) : WithBot ℕ)
  rw [Polynomial.degree_add_C (by simp)]
  simp

theorem minpoly_iK :
    minpoly ℚ iK = gaussianMinpoly := by
  symm
  apply minpoly.unique_of_degree_le_degree_minpoly ℚ iK
  · exact gaussianMinpoly_monic
  · exact aeval_gaussianMinpoly
  · have hdeg :
        (minpoly ℚ iK).degree =
          ((2 : ℕ) : WithBot ℕ) := by
      simpa only [gaussianPowerBasis_gen,
        gaussianPowerBasis_dim] using
        (PowerBasis.degree_minpoly gaussianPowerBasis)
    rw [gaussianMinpoly_degree, hdeg]

@[simp] theorem gaussianMinpoly_nextCoeff :
    gaussianMinpoly.nextCoeff = 0 := by
  have hnat : gaussianMinpoly.natDegree = 2 := by
    unfold gaussianMinpoly
    compute_degree!
  rw [Polynomial.nextCoeff_of_natDegree_pos (by omega), hnat]
  simp [gaussianMinpoly, Polynomial.coeff_one]

@[simp] theorem trace_iK :
    Algebra.trace ℚ K iK = 0 := by
  have h :=
    PowerBasis.trace_gen_eq_nextCoeff_minpoly gaussianPowerBasis
  simpa only [gaussianPowerBasis_gen, minpoly_iK,
    gaussianMinpoly_nextCoeff, neg_zero] using h

@[simp] theorem trace_one_gaussian :
    Algebra.trace ℚ K (1 : K) = 2 := by
  simpa using
    (Algebra.trace_algebraMap_of_basis gaussianBasis (1 : ℚ))

@[simp] theorem trace_neg_one_gaussian :
    Algebra.trace ℚ K (-1 : K) = -2 := by
  simp

/-- The discriminant of the structural Gaussian basis `(1,i)`. -/
theorem discr_gaussianBasis :
    Algebra.discr ℚ gaussianBasis = -4 := by
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply,
    Algebra.traceForm_apply, gaussianBasis_zero,
    gaussianBasis_one, one_mul, mul_one, iK_mul_self,
    trace_one_gaussian, trace_iK, trace_neg_one_gaussian]
  norm_num

/-- The integral Gaussian basis has the same discriminant `-4`.
This follows by localizing the basis, not by recomputing its trace matrix. -/
theorem discr_gaussianIntBasis :
    Algebra.discr ℤ gaussianIntBasis = -4 := by
  apply RingHom.injective_int (algebraMap ℤ ℚ)
  rw [← Algebra.discr_localizationLocalization
    ℤ (nonZeroDivisors ℤ) K gaussianIntBasis]
  exact discr_gaussianBasis

/-- The algebra norm in the integral basis `(1,i)` is the usual Gaussian
norm.  The proof is the symbolic determinant of multiplication by
`a + bi`, not a computation on Gaussian elements. -/
theorem algebraNorm_eq_gaussianNorm (z : GI) :
    Algebra.norm ℤ z = Zsqrtd.norm z := by
  rw [Algebra.norm_eq_matrix_det gaussianIntBasis,
    Matrix.det_fin_two]
  simp [Algebra.leftMulMatrix_eq_repr_mul,
    gaussianIntBasis_zero, gaussianIntBasis_one,
    gaussianIntBasis_repr_apply, i]
  change z.re * z.re + z.im * z.im = Zsqrtd.norm z
  simp [Zsqrtd.norm]

@[simp] theorem algebraNorm_pi :
    Algebra.norm ℤ pi = 13 := by
  rw [algebraNorm_eq_gaussianNorm, pi_norm]

@[simp] theorem algebraNorm_pi_sq :
    Algebra.norm ℤ (pi ^ 2) = 13 ^ 2 := by
  rw [map_pow, algebraNorm_pi]

/-- Localization identifies the field norm on `K/ℚ` with the same Gaussian
norm. -/
theorem fieldNorm_algebraMap (z : GI) :
    Algebra.norm ℚ (algebraMap GI K z) =
      algebraMap ℤ ℚ (Zsqrtd.norm z) := by
  rw [Algebra.norm_localization
    ℤ (nonZeroDivisors ℤ) z,
    algebraNorm_eq_gaussianNorm]

@[simp] theorem fieldNorm_pi :
    Algebra.norm ℚ (algebraMap GI K pi) = 13 := by
  rw [fieldNorm_algebraMap, pi_norm]
  norm_num

@[simp] theorem fieldNorm_pi_sq :
    Algebra.norm ℚ (algebraMap GI K (pi ^ 2)) =
      13 ^ 2 := by
  rw [map_pow (algebraMap GI K),
    map_pow (Algebra.norm ℚ), fieldNorm_pi]

end

end MazurProof.N13GaussianFractionField

end
end

-- module FLT.Assumptions.MazurProof.N13GaussianFactorization
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GaussianFactorization =====
section

/-!
# Gaussian factorization of the N13 sextic

The N13 sextic is the norm of a cubic over the Gaussian rationals.  This is
the structural input for a Gaussian two-descent.
-/

open Polynomial

namespace MazurProof.N13GaussianFactorization

noncomputable section

/-- The Gaussian rational algebra `ℚ[i]`, with `i² = -1`. -/
abbrev GaussianQ := QuadraticAlgebra ℚ (-1) 0

/-- The Gaussian unit `i`. -/
def gaussianI : GaussianQ := ⟨0, 1⟩

@[simp] theorem gaussianI_sq : gaussianI * gaussianI = -1 := by
  ext <;> simp [gaussianI, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

/-- The real cubic in the Gaussian factor. -/
def A : ℚ[X] := X ^ 3 + 2 * X ^ 2 - X - 1

/-- The imaginary quadratic part in the Gaussian factor. -/
def B : ℚ[X] := 2 * X * (X + 1)

/-- The N13 sextic is the sum of the two displayed squares. -/
theorem f_eq_sum_squares : N13Mumford.f ℚ = A ^ 2 + B ^ 2 := by
  simp only [N13Mumford.f, A, B]
  ring

end

end MazurProof.N13GaussianFactorization

end
end

-- module FLT.Assumptions.MazurProof.N13SexticSquareclass
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SexticSquareclass =====
section

/-!
# The rational-scalar survivor in the N13 fake square-class target

The apparent second local survivor in the weak two-descent is not a second
geometric class.  In the sextic algebra it differs from `13` by an explicit
square.  The proof first compresses the five power-basis expressions to two
degree-five polynomials `B` and `C`; it never expands the final product to
degree thirty-three.
-/

open Polynomial

namespace MazurProof.N13SexticSquareclass

noncomputable section

def f : ℚ[X] :=
  N13Mumford.f ℚ

/-- Twice the order-four torsion unit. -/
def Z : ℚ[X] := 2 * X ^ 5 + 7 * X ^ 4 + 9 * X ^ 3 + X ^ 2 + 4 * X + 3

/-- Twice the first fundamental unit. -/
def E₁ : ℚ[X] := -X ^ 5 - 3 * X ^ 4 - 3 * X ^ 3 - 3 * X

/-- Twice the second fundamental unit. -/
def E₂ : ℚ[X] := -X ^ 5 - 3 * X ^ 4 - 2 * X ^ 3 + 4 * X ^ 2 - 1

/-- Twice a generator of the ramification-three prime above 13. -/
def A : ℚ[X] := -X ^ 3 - 2 * X ^ 2 - X + 3

/-- Twice a generator of the residue-degree-three prime above 13. -/
def Q : ℚ[X] :=
  -6 * X ^ 5 - 21 * X ^ 4 - 27 * X ^ 3 - 3 * X ^ 2 - 12 * X - 5

/-- `ζ e₁ a = B / 2` in `ℚ[T]/(f)`. -/
def B : ℚ[X] := 3 * X ^ 5 + 10 * X ^ 4 + 11 * X ^ 3 - 3 * X ^ 2 + 4 * X + 6

/-- `e₂ a q = -C` in `ℚ[T]/(f)`. -/
def C : ℚ[X] := 5 * X ^ 5 + 18 * X ^ 4 + 23 * X ^ 3 - X + 4

def rB : ℚ[X] :=
  2 * X ^ 7 + 9 * X ^ 6 + 16 * X ^ 5 + 6 * X ^ 4 - 5 * X ^ 3 - X ^ 2 + 5 * X - 24

def rC : ℚ[X] :=
  -6 * X ^ 7 - 27 * X ^ 6 - 42 * X ^ 5 + 15 * X ^ 4 + 72 * X ^ 3 + 22 * X ^ 2 - 71 * X + 47

def r13 : ℚ[X] :=
  45 * X ^ 9 + 282 * X ^ 8 + 719 * X ^ 7 + 720 * X ^ 6 + 67 * X ^ 5 + 4 * X ^ 4 +
    828 * X ^ 3 + 148 * X ^ 2 - 236 * X + 196

theorem zeta_e1_a_reduction : Z * E₁ * A - 4 * B = f * rB := by
  simp [f, N13Mumford.f, Z, E₁, A, B, rB]
  ring

theorem e2_a_q_reduction : E₂ * A * Q + 8 * C = f * rC := by
  simp [f, N13Mumford.f, E₂, A, Q, C, rC]
  ring

/-- The compressed squareclass identity: in `ℚ[T]/(f)`,
`(-C) * (B / 2)^2 = 13`. -/
theorem compressed_squareclass_identity : C * B ^ 2 + 52 = f * r13 := by
  simp [f, N13Mumford.f, B, C, r13]
  ring

theorem zeta_e1_a_scaled_reduction :
    (Polynomial.C (1 / 2 : ℚ) * Z) *
          (Polynomial.C (1 / 2 : ℚ) * E₁) *
          (Polynomial.C (1 / 2 : ℚ) * A) -
        Polynomial.C (1 / 2 : ℚ) * B =
      f * (Polynomial.C (1 / 8 : ℚ) * rB) := by
  calc
    _ = Polynomial.C (1 / 8 : ℚ) * (Z * E₁ * A - 4 * B) := by
      have hcube :
          (Polynomial.C (1 / 2 : ℚ) : ℚ[X]) ^ 3 =
            Polynomial.C (1 / 8 : ℚ) := by
        rw [← map_pow]
        norm_num
      have hfour :
          (Polynomial.C (1 / 8 : ℚ) : ℚ[X]) * 4 =
            Polynomial.C (1 / 2 : ℚ) := by
        rw [show (4 : ℚ[X]) = Polynomial.C (4 : ℚ) by
              exact (map_natCast (Polynomial.C : ℚ →+* ℚ[X]) 4).symm,
          ← map_mul]
        norm_num
      calc
        _ = (Polynomial.C (1 / 2 : ℚ) : ℚ[X]) ^ 3 *
              (Z * E₁ * A) -
            Polynomial.C (1 / 2 : ℚ) * B := by ring
        _ = Polynomial.C (1 / 8 : ℚ) * (Z * E₁ * A) -
            (Polynomial.C (1 / 8 : ℚ) * 4) * B := by
              rw [hcube, hfour]
        _ = _ := by ring
    _ = Polynomial.C (1 / 8 : ℚ) * (f * rB) := by
      rw [zeta_e1_a_reduction]
    _ = _ := by ring

theorem e2_a_q_scaled_reduction :
    (Polynomial.C (1 / 2 : ℚ) * E₂) *
          (Polynomial.C (1 / 2 : ℚ) * A) *
          (Polynomial.C (1 / 2 : ℚ) * Q) -
        (-C) =
      f * (Polynomial.C (1 / 8 : ℚ) * rC) := by
  calc
    _ = Polynomial.C (1 / 8 : ℚ) * (E₂ * A * Q + 8 * C) := by
      have hcube :
          (Polynomial.C (1 / 2 : ℚ) : ℚ[X]) ^ 3 =
            Polynomial.C (1 / 8 : ℚ) := by
        rw [← map_pow]
        norm_num
      have height :
          (Polynomial.C (1 / 8 : ℚ) : ℚ[X]) * 8 = 1 := by
        rw [show (8 : ℚ[X]) = Polynomial.C (8 : ℚ) by
              exact (map_natCast (Polynomial.C : ℚ →+* ℚ[X]) 8).symm,
          ← map_mul]
        norm_num
      calc
        _ = (Polynomial.C (1 / 2 : ℚ) : ℚ[X]) ^ 3 *
              (E₂ * A * Q) + C := by ring
        _ = Polynomial.C (1 / 8 : ℚ) * (E₂ * A * Q) + 1 * C := by
              rw [hcube]
              simp
        _ = Polynomial.C (1 / 8 : ℚ) * (E₂ * A * Q) +
              (Polynomial.C (1 / 8 : ℚ) * 8) * C := by
                rw [height]
        _ = _ := by ring
    _ = Polynomial.C (1 / 8 : ℚ) * (f * rC) := by
      rw [e2_a_q_reduction]
    _ = _ := by ring

theorem compressed_scaled_reduction :
    (-C) * (Polynomial.C (1 / 2 : ℚ) * B) ^ 2 -
        Polynomial.C (13 : ℚ) =
      f * (Polynomial.C (-1 / 4 : ℚ) * r13) := by
  calc
    _ = Polynomial.C (-1 / 4 : ℚ) * (C * B ^ 2 + 52) := by
      have hnegQuarter :
          -((Polynomial.C (1 / 2 : ℚ) : ℚ[X]) ^ 2) =
            Polynomial.C (-1 / 4 : ℚ) := by
        rw [← map_pow, ← map_neg]
        norm_num
      have hthirteen :
          (Polynomial.C (-1 / 4 : ℚ) : ℚ[X]) * 52 =
            -(Polynomial.C (13 : ℚ)) := by
        rw [show (52 : ℚ[X]) = Polynomial.C (52 : ℚ) by
              exact (map_natCast (Polynomial.C : ℚ →+* ℚ[X]) 52).symm,
          ← map_mul, ← map_neg]
        norm_num
      calc
        _ = -((Polynomial.C (1 / 2 : ℚ) : ℚ[X]) ^ 2) *
              (C * B ^ 2) - Polynomial.C (13 : ℚ) := by ring
        _ = Polynomial.C (-1 / 4 : ℚ) * (C * B ^ 2) +
              Polynomial.C (-1 / 4 : ℚ) * 52 := by
                rw [hnegQuarter, hthirteen]
                ring
        _ = _ := by ring
    _ = Polynomial.C (-1 / 4 : ℚ) * (f * r13) := by
      rw [compressed_squareclass_identity]
    _ = _ := by ring

abbrev SexticAlgebra : Type :=
  AdjoinRoot f

def ofPoly (p : ℚ[X]) : SexticAlgebra :=
  AdjoinRoot.mk f p

def halfOfPoly (p : ℚ[X]) : SexticAlgebra :=
  ofPoly (Polynomial.C (1 / 2 : ℚ) * p)

def zeta : SexticAlgebra := halfOfPoly Z
def e1 : SexticAlgebra := halfOfPoly E₁
def e2 : SexticAlgebra := halfOfPoly E₂
def primeA : SexticAlgebra := halfOfPoly A
def primeQ : SexticAlgebra := halfOfPoly Q

theorem ofPoly_eq_of_sub_eq_mul
    (p q r : ℚ[X]) (h : p - q = f * r) :
    ofPoly p = ofPoly q := by
  have hm := congrArg (AdjoinRoot.mk f) h
  rw [map_sub, map_mul, AdjoinRoot.mk_self, zero_mul] at hm
  exact sub_eq_zero.mp hm

theorem zeta_mul_e1_mul_primeA :
    zeta * e1 * primeA = halfOfPoly B := by
  have hm := ofPoly_eq_of_sub_eq_mul
    ((Polynomial.C (1 / 2 : ℚ) * Z) *
      (Polynomial.C (1 / 2 : ℚ) * E₁) *
      (Polynomial.C (1 / 2 : ℚ) * A))
    (Polynomial.C (1 / 2 : ℚ) * B)
    (Polynomial.C (1 / 8 : ℚ) * rB)
    zeta_e1_a_scaled_reduction
  simpa [zeta, e1, primeA, halfOfPoly, ofPoly, map_mul] using hm

theorem e2_mul_primeA_mul_primeQ :
    e2 * primeA * primeQ = -(ofPoly C) := by
  have hm := ofPoly_eq_of_sub_eq_mul
    ((Polynomial.C (1 / 2 : ℚ) * E₂) *
      (Polynomial.C (1 / 2 : ℚ) * A) *
      (Polynomial.C (1 / 2 : ℚ) * Q))
    (-C)
    (Polynomial.C (1 / 8 : ℚ) * rC)
    e2_a_q_scaled_reduction
  simpa [e2, primeA, primeQ, halfOfPoly, ofPoly, map_mul] using hm

theorem compressed_scaled_identity_in_algebra :
    (-(ofPoly C)) * (halfOfPoly B) ^ 2 =
      algebraMap ℚ SexticAlgebra 13 := by
  have hm := ofPoly_eq_of_sub_eq_mul
    ((-C) * (Polynomial.C (1 / 2 : ℚ) * B) ^ 2)
    (Polynomial.C (13 : ℚ))
    (Polynomial.C (-1 / 4 : ℚ) * r13)
    compressed_scaled_reduction
  simpa [halfOfPoly, ofPoly, map_mul, map_pow] using hm

def survivor : SexticAlgebra :=
  e2 * primeA * primeQ

def squareFactor : SexticAlgebra :=
  zeta * e1 * primeA

/-- The two local representatives differ by a rational scalar and a square. -/
theorem survivor_mul_square :
    survivor * squareFactor ^ 2 =
      algebraMap ℚ SexticAlgebra 13 := by
  rw [survivor, squareFactor, e2_mul_primeA_mul_primeQ,
    zeta_mul_e1_mul_primeA]
  exact compressed_scaled_identity_in_algebra

end

end MazurProof.N13SexticSquareclass

end
end

-- module FLT.Assumptions.MazurProof.N13GaussianCubic
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GaussianCubic =====
section

/-!
# The Gaussian cubic presentation of the N13 sextic algebra

The sextic algebra becomes cubic after adjoining its intrinsic order-four
unit `i`.  More importantly for the local descent, all long power-basis
generators have short expressions in `i` and the sextic root `θ`.

Every identity below has a constant or linear quotient by the defining
sextic.  Thus this file records the structural change of presentation rather
than a high-degree certificate.
-/

open Polynomial

namespace MazurProof.N13GaussianCubic

noncomputable section

open N13SexticSquareclass

abbrev L : Type := SexticAlgebra

/-- The sextic root. -/
def theta : L :=
  AdjoinRoot.root f

/-- The real and imaginary parts of the Gaussian cubic factor. -/
def cubicA : ℚ[X] :=
  X ^ 3 + 2 * X ^ 2 - X - 1

def cubicB : ℚ[X] :=
  2 * X * (X + 1)

theorem gaussian_cubic_reduction :
    2 * cubicA - Z * cubicB = f * (-4 * X - 2) := by
  simp [cubicA, cubicB, f, N13Mumford.f, Z]
  ring

theorem e1_short_reduction :
    E₁ - (2 * (1 - X ^ 2) + (Z - 2) * X) =
      f * (-2) := by
  simp [f, N13Mumford.f, Z, E₁]
  ring

theorem e2_short_reduction :
    E₂ -
        (2 + Z * X ^ 2 + (2 + 2 * Z) * X) =
      f * (-(2 * X + 3)) := by
  simp [f, N13Mumford.f, Z, E₂]
  ring

theorem primeA_short_reduction :
    A -
        (2 - Z * X ^ 2 - (2 + Z) * X) =
      f * (2 * X + 1) := by
  simp [f, N13Mumford.f, Z, A]
  ring

theorem primeQ_short_polynomial :
    Q = 4 - 3 * Z := by
  simp [Z, Q]
  ring

theorem ofPoly_eq_of_sub_eq_mul
    (p q r : ℚ[X]) (h : p - q = f * r) :
    ofPoly p = ofPoly q := by
  have hm := congrArg (AdjoinRoot.mk f) h
  rw [map_sub, map_mul, AdjoinRoot.mk_self, zero_mul] at hm
  exact sub_eq_zero.mp hm

@[simp] theorem ofPoly_X :
    ofPoly X = theta := rfl

theorem halfOfPoly_eq (p : ℚ[X]) :
    halfOfPoly p =
      AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly p := by
  simp [halfOfPoly, ofPoly, map_mul]

theorem zeta_eq_half_mul_Z :
    zeta = AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly Z := by
  exact halfOfPoly_eq Z

theorem of_two :
    AdjoinRoot.of f (2 : ℚ) = (2 : L) :=
  map_ofNat (AdjoinRoot.of f) 2

theorem of_half_mul_two :
    AdjoinRoot.of f (1 / 2 : ℚ) * (2 : L) = 1 := by
  rw [← of_two, ← map_mul]
  norm_num

/-- The sextic root satisfies a cubic equation over `ℚ(i)`. -/
theorem gaussian_cubic :
    theta ^ 3 + 2 * theta ^ 2 - theta - 1 -
        zeta * (2 * theta * (theta + 1)) = 0 := by
  have h := ofPoly_eq_of_sub_eq_mul
    (2 * cubicA - Z * cubicB) 0 (-4 * X - 2)
    (by simpa using gaussian_cubic_reduction)
  have h' :
      2 * (theta ^ 3 + 2 * theta ^ 2 - theta - 1) -
          ofPoly Z * (2 * theta * (theta + 1)) = 0 := by
    simpa [theta, cubicA, cubicB, ofPoly, map_sub, map_mul, map_add,
      map_pow, map_ofNat] using h
  rw [zeta_eq_half_mul_Z]
  let Aθ := theta ^ 3 + 2 * theta ^ 2 - theta - 1
  let Bθ := 2 * theta * (theta + 1)
  calc
    Aθ - (AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly Z) * Bθ =
        (AdjoinRoot.of f (1 / 2 : ℚ) * 2) * Aθ -
          AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly Z * Bθ := by
            rw [of_half_mul_two]
            ring
    _ = AdjoinRoot.of f (1 / 2 : ℚ) *
          (2 * Aθ - ofPoly Z * Bθ) := by ring
    _ = 0 := by rw [show 2 * Aθ - ofPoly Z * Bθ = 0 from h']; ring

/-- The first fundamental unit in the Gaussian cubic basis. -/
theorem e1_short :
    e1 = 1 - theta ^ 2 + (zeta - 1) * theta := by
  have h := ofPoly_eq_of_sub_eq_mul
    E₁ (2 * (1 - X ^ 2) + (Z - 2) * X) (-2)
    e1_short_reduction
  have h' :
      ofPoly E₁ =
        2 * (1 - theta ^ 2) + (ofPoly Z - 2) * theta := by
    simpa [theta, ofPoly, map_sub, map_mul, map_add, map_pow,
      map_ofNat] using h
  rw [show e1 = halfOfPoly E₁ from rfl, halfOfPoly_eq,
    zeta_eq_half_mul_Z]
  calc
    AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly E₁ =
        AdjoinRoot.of f (1 / 2 : ℚ) *
          (2 * (1 - theta ^ 2) + (ofPoly Z - 2) * theta) := by
            rw [h']
    _ = (AdjoinRoot.of f (1 / 2 : ℚ) * 2) *
          (1 - theta ^ 2) +
        (AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly Z -
          AdjoinRoot.of f (1 / 2 : ℚ) * 2) * theta := by ring
    _ = 1 - theta ^ 2 +
        (AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly Z - 1) * theta := by
          simp only [of_half_mul_two, one_mul]

/-- The second fundamental unit in the Gaussian cubic basis. -/
theorem e2_short :
    e2 = 1 + zeta * theta ^ 2 + (1 + 2 * zeta) * theta := by
  have h := ofPoly_eq_of_sub_eq_mul
    E₂ (2 + Z * X ^ 2 + (2 + 2 * Z) * X)
    (-(2 * X + 3))
    e2_short_reduction
  have h' :
      ofPoly E₂ =
        2 + ofPoly Z * theta ^ 2 +
          (2 + 2 * ofPoly Z) * theta := by
    simpa [theta, ofPoly, map_sub, map_mul, map_add, map_pow,
      map_ofNat] using h
  rw [show e2 = halfOfPoly E₂ from rfl, halfOfPoly_eq,
    zeta_eq_half_mul_Z]
  calc
    AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly E₂ =
        AdjoinRoot.of f (1 / 2 : ℚ) *
          (2 + ofPoly Z * theta ^ 2 +
            (2 + 2 * ofPoly Z) * theta) := by rw [h']
    _ = (AdjoinRoot.of f (1 / 2 : ℚ) * 2) +
        (AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly Z) * theta ^ 2 +
        ((AdjoinRoot.of f (1 / 2 : ℚ) * 2) +
          2 * (AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly Z)) * theta := by
            ring
    _ = 1 + (AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly Z) * theta ^ 2 +
        (1 + 2 * (AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly Z)) * theta := by
          rw [of_half_mul_two]

/-- The ramified prime generator over `13` in the Gaussian cubic basis. -/
theorem primeA_short :
    primeA = 1 - zeta * theta ^ 2 - (1 + zeta) * theta := by
  have h := ofPoly_eq_of_sub_eq_mul
    A (2 - Z * X ^ 2 - (2 + Z) * X)
    (2 * X + 1)
    primeA_short_reduction
  have h' :
      ofPoly A =
        2 - ofPoly Z * theta ^ 2 - (2 + ofPoly Z) * theta := by
    simpa [theta, ofPoly, map_sub, map_mul, map_add, map_pow,
      map_ofNat] using h
  rw [show primeA = halfOfPoly A from rfl, halfOfPoly_eq,
    zeta_eq_half_mul_Z]
  calc
    AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly A =
        AdjoinRoot.of f (1 / 2 : ℚ) *
          (2 - ofPoly Z * theta ^ 2 - (2 + ofPoly Z) * theta) := by
            rw [h']
    _ = (AdjoinRoot.of f (1 / 2 : ℚ) * 2) -
        (AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly Z) * theta ^ 2 -
        ((AdjoinRoot.of f (1 / 2 : ℚ) * 2) +
          AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly Z) * theta := by ring
    _ = 1 - (AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly Z) * theta ^ 2 -
        (1 + AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly Z) * theta := by
          rw [of_half_mul_two]

/-- The residue-degree-three prime generator over `13` is already linear
in the Gaussian unit. -/
theorem primeQ_short :
    primeQ = 2 - 3 * zeta := by
  have h := congrArg ofPoly primeQ_short_polynomial
  have h' : ofPoly Q = 4 - 3 * ofPoly Z := by
    simpa [ofPoly, map_sub, map_mul, map_ofNat] using h
  rw [show primeQ = halfOfPoly Q from rfl, halfOfPoly_eq,
    zeta_eq_half_mul_Z]
  calc
    AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly Q =
        AdjoinRoot.of f (1 / 2 : ℚ) * (4 - 3 * ofPoly Z) := by
          rw [h']
    _ = (AdjoinRoot.of f (1 / 2 : ℚ) * 2) * 2 -
        3 * (AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly Z) := by ring
    _ = 2 - 3 * (AdjoinRoot.of f (1 / 2 : ℚ) * ofPoly Z) := by
      simp only [of_half_mul_two, one_mul]

end

end MazurProof.N13GaussianCubic

end
end

-- module FLT.Assumptions.MazurProof.N13SexticIrreducible
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SexticIrreducible =====
section

/-!
# Irreducibility of the N13 sextic

The sextic defining the fake two-descent algebra is irreducible over `ℚ`.
We prove this structurally by reduction modulo three.  An irreducible
degree-`d` factor over `𝔽₃` divides `X ^ (3 ^ d) - X`, by applying finite-field
Frobenius in its adjoin-root field.  Three short Bézout identities exclude
degrees one through three, which is the full Rabin test for a sextic.  No
finite-field polynomials are enumerated.
-/

open Polynomial

namespace MazurProof.N13SexticIrreducible

noncomputable section

def fInt : ℤ[X] :=
  X ^ 6 + 4 * X ^ 5 + 6 * X ^ 4 + 2 * X ^ 3 + X ^ 2 + 2 * X + 1

def fModThree : (ZMod 3)[X] :=
  fInt.map (Int.castRingHom (ZMod 3))

theorem fInt_monic : fInt.Monic := by
  unfold fInt
  monicity!

theorem fModThree_eq :
    fModThree = X ^ 6 + X ^ 5 - X ^ 3 + X ^ 2 - X + 1 := by
  simp [fModThree, fInt]
  have hthree : (3 : (ZMod 3)[X]) = 0 :=
    CharP.cast_eq_zero ((ZMod 3)[X]) 3
  linear_combination (X ^ 5 + 2 * X ^ 4 + X ^ 3 + X) * hthree

theorem fModThree_monic : fModThree.Monic := by
  rw [fModThree_eq]
  monicity!

theorem fModThree_natDegree : fModThree.natDegree = 6 := by
  rw [fModThree_eq]
  compute_degree!

theorem irreducible_dvd_own_frobenius
    {p : (ZMod 3)[X]} (hp : Irreducible p) :
    p ∣ X ^ (3 ^ p.natDegree) - X := by
  letI : Fact (Irreducible p) := ⟨hp⟩
  letI : Module.Finite (ZMod 3) (AdjoinRoot p) :=
    (AdjoinRoot.powerBasis hp.ne_zero).finite
  letI : Finite (AdjoinRoot p) :=
    Module.finite_of_finite (ZMod 3)
  letI : Fintype (AdjoinRoot p) :=
    Fintype.ofFinite (AdjoinRoot p)
  have hcard :
      Fintype.card (AdjoinRoot p) = 3 ^ p.natDegree := by
    rw [Module.card_eq_pow_finrank (K := ZMod 3) (V := AdjoinRoot p),
      (AdjoinRoot.powerBasis hp.ne_zero).finrank, ZMod.card,
      AdjoinRoot.powerBasis_dim]
  have hroot :
      (AdjoinRoot.root p) ^ (3 ^ p.natDegree) =
        AdjoinRoot.root p := by
    rw [← hcard]
    exact FiniteField.pow_card _
  rw [← AdjoinRoot.mk_eq_zero, map_sub, map_pow, AdjoinRoot.mk_X]
  exact sub_eq_zero.mpr hroot

def bezoutOneA : (ZMod 3)[X] :=
  -X ^ 2 - X + 1

def bezoutOneB : (ZMod 3)[X] :=
  X ^ 5 - X ^ 4 + X ^ 3 + X + 1

theorem bezout_one :
    bezoutOneA * fModThree + bezoutOneB * (X ^ 3 - X) = 1 := by
  rw [fModThree_eq]
  simp [bezoutOneA, bezoutOneB]
  have hthree : (3 : (ZMod 3)[X]) = 0 :=
    CharP.cast_eq_zero ((ZMod 3)[X]) 3
  linear_combination
    (-X ^ 7 + X ^ 5 - X) * hthree

def bezoutTwoA : (ZMod 3)[X] :=
  X ^ 8 - X ^ 6 + X ^ 5 - X ^ 3 - X ^ 2 - X + 1

def bezoutTwoB : (ZMod 3)[X] :=
  -X ^ 5 - X ^ 4 + X ^ 3 + X ^ 2 + X + 1

theorem bezout_two :
    bezoutTwoA * fModThree + bezoutTwoB * (X ^ 9 - X) = 1 := by
  rw [fModThree_eq]
  simp [bezoutTwoA, bezoutTwoB]
  have hthree : (3 : (ZMod 3)[X]) = 0 :=
    CharP.cast_eq_zero ((ZMod 3)[X]) 3
  linear_combination
    (X * (X ^ 9 - X ^ 7 + X ^ 4 - X ^ 2 - 1)) * hthree

def bezoutThreeA : (ZMod 3)[X] :=
  -X ^ 25 + X ^ 22 + X ^ 21 + X ^ 20 + X ^ 19 - X ^ 18 - X ^ 17 +
    X ^ 16 - X ^ 12 - X ^ 10 + X ^ 8 - X ^ 6 + X ^ 5 - X ^ 4 + X ^ 3 + 1

def bezoutThreeB : (ZMod 3)[X] :=
  X ^ 4 + X ^ 3 + X - 1

theorem bezout_three :
    bezoutThreeA * fModThree + bezoutThreeB * (X ^ 27 - X) = 1 := by
  rw [fModThree_eq]
  simp [bezoutThreeA, bezoutThreeB]
  have hthree : (3 : (ZMod 3)[X]) = 0 :=
    CharP.cast_eq_zero ((ZMod 3)[X]) 3
  linear_combination
    (X ^ 4 * (X ^ 24 + X ^ 22 - X ^ 19 + X ^ 17 - X ^ 13 +
      X ^ 9 - X ^ 8 + X ^ 3 - X ^ 2 + X - 1)) * hthree

theorem coprime_frobenius_one :
    IsCoprime fModThree (X ^ 3 - X) :=
  ⟨bezoutOneA, bezoutOneB, bezout_one⟩

theorem coprime_frobenius_two :
    IsCoprime fModThree (X ^ 9 - X) :=
  ⟨bezoutTwoA, bezoutTwoB, bezout_two⟩

theorem coprime_frobenius_three :
    IsCoprime fModThree (X ^ 27 - X) :=
  ⟨bezoutThreeA, bezoutThreeB, bezout_three⟩

/-- The reduction of the N13 sextic modulo three is irreducible. -/
theorem fModThree_irreducible : Irreducible fModThree := by
  have hf1 : fModThree ≠ 1 := by
    intro h
    have := fModThree_natDegree
    rw [h] at this
    norm_num at this
  rw [fModThree_monic.irreducible_iff_lt_natDegree_lt hf1]
  intro q hq hdeg hqf
  rw [fModThree_natDegree] at hdeg
  have hdeg' : 0 < q.natDegree ∧ q.natDegree ≤ 3 := by
    simpa using (Finset.mem_Ioc.mp hdeg)
  obtain ⟨r, _hrm, hri, hrq⟩ :=
    Polynomial.exists_monic_irreducible_factor q
      (not_isUnit_of_natDegree_pos q hdeg'.1)
  have hrf : r ∣ fModThree :=
    dvd_trans hrq hqf
  have hrle : r.natDegree ≤ 3 :=
    (natDegree_le_of_dvd hrq hq.ne_zero).trans hdeg'.2
  have hrpos : 0 < r.natDegree :=
    hri.natDegree_pos
  have hcases :
      r.natDegree = 1 ∨ r.natDegree = 2 ∨ r.natDegree = 3 := by
    omega
  rcases hcases with hdegree | hdegree | hdegree
  · have hrfrob := irreducible_dvd_own_frobenius hri
    rw [hdegree] at hrfrob
    norm_num at hrfrob
    exact hri.not_isUnit
      (coprime_frobenius_one.isUnit_of_dvd' hrf hrfrob)
  · have hrfrob := irreducible_dvd_own_frobenius hri
    rw [hdegree] at hrfrob
    norm_num at hrfrob
    exact hri.not_isUnit
      (coprime_frobenius_two.isUnit_of_dvd' hrf hrfrob)
  · have hrfrob := irreducible_dvd_own_frobenius hri
    rw [hdegree] at hrfrob
    norm_num at hrfrob
    exact hri.not_isUnit
      (coprime_frobenius_three.isUnit_of_dvd' hrf hrfrob)

/-- The integral N13 sextic is irreducible by its irreducible reduction
modulo three. -/
theorem fInt_irreducible : Irreducible fInt := by
  apply fInt_monic.irreducible_of_irreducible_map
    (Int.castRingHom (ZMod 3)) fInt
  simpa [fModThree] using fModThree_irreducible

theorem fInt_map_rat :
    fInt.map (algebraMap ℤ ℚ) = N13Mumford.f ℚ := by
  simp [fInt, N13Mumford.f]

/-- The sextic defining the N13 Mumford model is irreducible over `ℚ`. -/
theorem n13Mumford_f_irreducible :
    Irreducible (N13Mumford.f ℚ) := by
  rw [← fInt_map_rat]
  exact
    fInt_monic.isPrimitive.irreducible_iff_irreducible_map_fraction_map.mp
      fInt_irreducible

/-- The same irreducibility statement in the notation used by the fake
square-class target. -/
theorem squareclass_f_irreducible :
    Irreducible N13SexticSquareclass.f := by
  simpa [N13SexticSquareclass.f] using n13Mumford_f_irreducible

/-- An explicit, opt-in `Fact` for clients that need the field structure on
the sextic algebra.  Use `letI := sexticIrreducibleFact`; it is deliberately
not a global instance. -/
@[reducible] def sexticIrreducibleFact :
    Fact (Irreducible N13SexticSquareclass.f) :=
  ⟨squareclass_f_irreducible⟩

/-- The field structure on the sextic algebra, exported without installing a
global instance. -/
@[reducible] noncomputable def sexticAlgebraField :
    Field N13SexticSquareclass.SexticAlgebra := by
  letI := sexticIrreducibleFact
  infer_instance

end

end MazurProof.N13SexticIrreducible

end
end

-- module FLT.Assumptions.MazurProof.N13GaussianFieldEquiv
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GaussianFieldEquiv =====
section

/-!
# Equivalence of the sextic and Gaussian-cubic N13 fields

The root `α` of the translated Gaussian cubic gives

`θ = α + 9`.

This file proves that sending the sextic generator to this element is an
isomorphism from the original degree-six algebra to the Gaussian cubic
number field.  Equal absolute dimensions make the injective field map
surjective; no inverse polynomial is searched for.

The intrinsic order-four element of the sextic field maps to the Gaussian
unit `i`.  Consequently the short formulas for the descent generators show
directly that all of them are algebraic integers in the structural absolute
ring of integers.
-/

open Algebra Module Polynomial

namespace MazurProof.N13GaussianFieldEquiv

noncomputable section

open N13GaussianGlobalArithmetic

abbrev K := N13GaussianCubicField.K
abbrev Lg := N13GaussianCubicField.L
abbrev Ls := N13SexticSquareclass.SexticAlgebra

local instance fieldLg : Field Lg :=
  N13GaussianCubicField.cubicField

local instance fieldLs : Field Ls :=
  N13SexticIrreducible.sexticAlgebraField

local instance finiteKL : Module.Finite K Lg :=
  N13GaussianCubicField.powerBasis.finite

local instance finiteQL : Module.Finite ℚ Lg :=
  Module.Finite.trans K Lg

def gaussianI : Lg :=
  algebraMap K Lg
    (algebraMap GI K N13GaussianGlobalArithmetic.i)

def gaussianTheta : Lg :=
  N13GaussianCubicField.alpha + 9

@[simp] theorem gaussianI_sq :
    gaussianI ^ 2 = -1 := by
  change
    (algebraMap K Lg
      (algebraMap GI K N13GaussianGlobalArithmetic.i)) ^ 2 = -1
  rw [← map_pow, ← map_pow,
    N13GaussianGlobalArithmetic.i_sq, map_neg, map_one,
    map_neg, map_one]

theorem alpha_root_h :
    eval₂ (algebraMap GI Lg)
      N13GaussianCubicField.alpha
      N13GaussianGlobalArithmetic.h = 0 := by
  have hmap :
      algebraMap GI Lg =
        (algebraMap K Lg).comp (algebraMap GI K) :=
    IsScalarTower.algebraMap_eq GI K Lg
  rw [hmap, ← Polynomial.eval₂_map]
  exact AdjoinRoot.eval₂_root N13GaussianCubicField.hK

theorem gaussianTheta_root_g :
    eval₂ (algebraMap GI Lg) gaussianTheta
      N13GaussianGlobalArithmetic.g = 0 := by
  have h := alpha_root_h
  rw [N13GaussianGlobalArithmetic.h,
    Polynomial.eval₂_comp] at h
  simpa only [gaussianTheta, eval₂_add, eval₂_X,
    eval₂_ofNat, map_ofNat] using h

theorem gaussianTheta_root_n13F :
    eval₂ (algebraMap GI Lg) gaussianTheta
      N13GaussianGlobalArithmetic.n13F = 0 := by
  rw [← N13GaussianGlobalArithmetic.g_mul_conj,
    Polynomial.eval₂_mul, gaussianTheta_root_g, zero_mul]

theorem gaussianTheta_root_sextic :
    eval₂ (algebraMap ℚ Lg) gaussianTheta
      N13SexticSquareclass.f = 0 := by
  simpa [N13SexticSquareclass.f, N13Mumford.f,
    N13GaussianGlobalArithmetic.n13F] using
    gaussianTheta_root_n13F

def sexticToGaussian : Ls →ₐ[ℚ] Lg :=
  AdjoinRoot.liftAlgHom
    N13SexticSquareclass.f
    (Algebra.ofId ℚ Lg)
    gaussianTheta
    gaussianTheta_root_sextic

@[simp] theorem sexticToGaussian_theta :
    sexticToGaussian N13GaussianCubic.theta =
      gaussianTheta :=
  AdjoinRoot.liftAlgHom_root
    N13SexticSquareclass.f
    (Algebra.ofId ℚ Lg)
    gaussianTheta
    gaussianTheta_root_sextic

theorem finrank_Ls :
    Module.finrank ℚ Ls = 6 := by
  change
    Module.finrank ℚ
      (AdjoinRoot N13SexticSquareclass.f) = 6
  rw [(AdjoinRoot.powerBasis
    (by
      simpa [N13SexticSquareclass.f] using
        (N13Mumford.f_monic (K := ℚ)).ne_zero)).finrank]
  simpa [N13SexticSquareclass.f] using
    (N13Mumford.f_natDegree (K := ℚ))

theorem finrank_Lg :
    Module.finrank ℚ Lg = 6 := by
  calc
    Module.finrank ℚ Lg =
        Module.finrank ℚ K * Module.finrank K Lg :=
      (Module.finrank_mul_finrank ℚ K Lg).symm
    _ = 2 * 3 := by
      rw [N13GaussianFractionField.finrank_K]
      congr 1
      rw [Module.finrank_eq_card_basis
        N13GaussianCubicField.powerBasis.basis]
      simp [N13GaussianCubicField.powerBasis_dim]
    _ = 6 := by norm_num

theorem sexticToGaussian_bijective :
    Function.Bijective sexticToGaussian := by
  constructor
  · exact sexticToGaussian.injective
  · apply
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (f := sexticToGaussian.toLinearMap) ?_).mp
    · exact sexticToGaussian.injective
    · rw [finrank_Ls, finrank_Lg]

def sexticEquivGaussian : Ls ≃ₐ[ℚ] Lg :=
  AlgEquiv.ofBijective sexticToGaussian
    sexticToGaussian_bijective

@[simp] theorem sexticEquivGaussian_theta :
    sexticEquivGaussian N13GaussianCubic.theta =
      gaussianTheta :=
  sexticToGaussian_theta

@[simp] theorem sexticEquivGaussian_ofPoly
    (p : ℚ[X]) :
    sexticEquivGaussian
        (N13SexticSquareclass.ofPoly p) =
      eval₂ (algebraMap ℚ Lg) gaussianTheta p := by
  change
    sexticToGaussian
        (AdjoinRoot.mk N13SexticSquareclass.f p) =
      eval₂ (algebraMap ℚ Lg) gaussianTheta p
  exact AdjoinRoot.liftAlgHom_mk
    N13SexticSquareclass.f
    (Algebra.ofId ℚ Lg)
    gaussianTheta
    gaussianTheta_root_sextic p

theorem gaussianTheta_gaussian_cubic :
    gaussianTheta ^ 3 + 2 * gaussianTheta ^ 2 -
        gaussianTheta - 1 -
      gaussianI * (2 * gaussianTheta * (gaussianTheta + 1)) = 0 := by
  have hi :
      algebraMap GI Lg N13GaussianGlobalArithmetic.i =
        gaussianI := by
    rw [gaussianI,
      IsScalarTower.algebraMap_apply GI K Lg]
  have hg :
      gaussianTheta ^ 3 +
          (2 - 2 * gaussianI) * gaussianTheta ^ 2 +
          (-1 - 2 * gaussianI) * gaussianTheta - 1 = 0 := by
    simpa [N13GaussianGlobalArithmetic.g, hi,
      map_add, map_sub, map_mul, map_neg, map_one,
      map_ofNat] using gaussianTheta_root_g
  linear_combination hg

theorem gaussianTheta_mul_inverse :
    gaussianTheta *
        (gaussianTheta ^ 2 +
          (2 - 2 * gaussianI) * gaussianTheta +
          (-1 - 2 * gaussianI)) = 1 := by
  linear_combination gaussianTheta_gaussian_cubic

theorem gaussianTheta_isUnit :
    IsUnit gaussianTheta :=
  isUnit_iff_exists_inv.mpr
    ⟨gaussianTheta ^ 2 +
      (2 - 2 * gaussianI) * gaussianTheta +
      (-1 - 2 * gaussianI),
      gaussianTheta_mul_inverse⟩

theorem gaussianTheta_add_one_mul_inverse :
    (gaussianTheta + 1) *
        (-(gaussianTheta ^ 2 +
          (1 - 2 * gaussianI) * gaussianTheta - 2)) = 1 := by
  linear_combination -gaussianTheta_gaussian_cubic

theorem gaussianTheta_add_one_isUnit :
    IsUnit (gaussianTheta + 1) :=
  isUnit_iff_exists_inv.mpr
    ⟨-(gaussianTheta ^ 2 +
        (1 - 2 * gaussianI) * gaussianTheta - 2),
      gaussianTheta_add_one_mul_inverse⟩

theorem gaussianCubicImaginaryFactor_isUnit :
    IsUnit (2 * gaussianTheta * (gaussianTheta + 1)) :=
  ((isUnit_iff_ne_zero.mpr
      (by
        intro htwo
        have htwoK : (2 : K) = 0 :=
          (algebraMap K Lg).injective (by
            simpa only [map_ofNat, map_zero] using htwo)
        norm_num at htwoK)).mul
    gaussianTheta_isUnit).mul gaussianTheta_add_one_isUnit

@[simp] theorem sexticEquivGaussian_zeta :
    sexticEquivGaussian N13SexticSquareclass.zeta =
      gaussianI := by
  let zI : Lg :=
    sexticEquivGaussian N13SexticSquareclass.zeta
  let Bθ : Lg :=
    2 * gaussianTheta * (gaussianTheta + 1)
  have hz :
      gaussianTheta ^ 3 + 2 * gaussianTheta ^ 2 -
          gaussianTheta - 1 - zI * Bθ = 0 := by
    simpa only [map_add, map_sub, map_mul, map_pow,
      map_ofNat, map_one, map_zero, sexticEquivGaussian_theta]
      using
        congrArg sexticEquivGaussian
          N13GaussianCubic.gaussian_cubic
  have hi :
      gaussianTheta ^ 3 + 2 * gaussianTheta ^ 2 -
          gaussianTheta - 1 - gaussianI * Bθ = 0 := by
    simpa only [Bθ] using gaussianTheta_gaussian_cubic
  apply gaussianCubicImaginaryFactor_isUnit.mul_right_cancel
  calc
    zI * Bθ =
        gaussianTheta ^ 3 + 2 * gaussianTheta ^ 2 -
          gaussianTheta - 1 :=
      (sub_eq_zero.mp hz).symm
    _ = gaussianI * Bθ :=
      sub_eq_zero.mp hi

@[simp] theorem sexticEquivGaussian_e1 :
    sexticEquivGaussian N13SexticSquareclass.e1 =
      1 - gaussianTheta ^ 2 +
        (gaussianI - 1) * gaussianTheta := by
  simpa only [map_add, map_sub, map_mul, map_pow,
    map_one, sexticEquivGaussian_theta,
    sexticEquivGaussian_zeta] using
    congrArg sexticEquivGaussian
      N13GaussianCubic.e1_short

@[simp] theorem sexticEquivGaussian_e2 :
    sexticEquivGaussian N13SexticSquareclass.e2 =
      1 + gaussianI * gaussianTheta ^ 2 +
        (1 + 2 * gaussianI) * gaussianTheta := by
  simpa only [map_add, map_mul, map_pow, map_ofNat,
    map_one, sexticEquivGaussian_theta,
    sexticEquivGaussian_zeta] using
    congrArg sexticEquivGaussian
      N13GaussianCubic.e2_short

@[simp] theorem sexticEquivGaussian_primeA :
    sexticEquivGaussian N13SexticSquareclass.primeA =
      1 - gaussianI * gaussianTheta ^ 2 -
        (1 + gaussianI) * gaussianTheta := by
  simpa only [map_add, map_sub, map_mul, map_pow,
    map_one, sexticEquivGaussian_theta,
    sexticEquivGaussian_zeta] using
    congrArg sexticEquivGaussian
      N13GaussianCubic.primeA_short

@[simp] theorem sexticEquivGaussian_primeQ :
    sexticEquivGaussian N13SexticSquareclass.primeQ =
      2 - 3 * gaussianI := by
  simpa only [map_sub, map_mul, map_ofNat,
    sexticEquivGaussian_zeta] using
    congrArg sexticEquivGaussian
      N13GaussianCubic.primeQ_short

/-! ## Integrality of the structural generators -/

theorem gaussianI_integral :
    IsIntegral ℤ gaussianI := by
  have hi :
      IsIntegral ℤ
        (algebraMap GI Lg
          N13GaussianGlobalArithmetic.i) :=
    N13GaussianFractionField.i_integral.algebraMap
  simpa only [gaussianI,
    IsScalarTower.algebraMap_apply GI K Lg] using hi

theorem lg_natCast_integral (n : ℕ) :
    IsIntegral ℤ (n : Lg) := by
  have h :
      IsIntegral ℤ
        (algebraMap ℤ Lg (n : ℤ)) :=
    isIntegral_algebraMap
  rw [map_natCast (algebraMap ℤ Lg) n] at h
  exact h

theorem gaussianTheta_integral :
    IsIntegral ℤ gaussianTheta := by
  have ha :
      IsIntegral ℤ N13GaussianCubicField.alpha :=
    isIntegral_trans
      N13GaussianCubicField.alpha
      N13GaussianCubicField.alpha_integral
  exact ha.add (lg_natCast_integral 9)

end

end MazurProof.N13GaussianFieldEquiv

end
end

-- module FLT.Assumptions.MazurProof.N13MumfordKummerValue
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13MumfordKummerValue =====
section

/-!
# The N13 Mumford fake-Kummer value

Let `θ` be the sextic root.  The branch specialization

`ℚ[X,Y]/(Y²-f(X)) → ℚ(θ),  X ↦ θ,  Y ↦ 0`

turns the quadratic norm of an affine function into a square.  For a
balanced Mumford representative `(u,v,n∞)`, its raw fake-Kummer value is
the unit `u(θ)`, modulo squares and rational scalars.

Irreducibility of the sextic is used only to install the field structure
locally and hence turn the nonzero element `u(θ)` into a unit.  This file
does not yet assert that the value is independent of the chosen Mumford
representative; that is the next principal-ideal relation theorem.
-/

open Polynomial

namespace MazurProof.N13MumfordKummerValue

noncomputable section

open SexticMumford

abbrev f : ℚ[X] :=
  N13SexticSquareclass.f

abbrev L : Type :=
  N13SexticSquareclass.SexticAlgebra

abbrev M : SexticMumford.Model ℚ :=
  N13Mumford.model ℚ

local instance sexticAlgebraField : Field L :=
  N13SexticIrreducible.sexticAlgebraField

theorem thetaBranch_root :
    (curvePoly M).eval₂ (AdjoinRoot.mk f) (0 : L) = 0 := by
  simp only [curvePoly, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C,
    OfNat.ofNat]
  rw [show M.f = f by rfl, AdjoinRoot.mk_self]
  change (0 : L) ^ 2 - 0 = 0
  norm_num

/-- Specialization to the branch `X=θ`, `Y=0`. -/
def thetaBranch : N13Mumford.CoordinateRing ℚ →+* L :=
  AdjoinRoot.lift (AdjoinRoot.mk f) 0 thetaBranch_root

@[simp] theorem thetaBranch_xClass (p : ℚ[X]) :
    thetaBranch (xClass M p) = AdjoinRoot.mk f p := by
  change
    AdjoinRoot.lift (AdjoinRoot.mk f) 0 thetaBranch_root
        (AdjoinRoot.of (curvePoly M) p) =
      AdjoinRoot.mk f p
  rw [AdjoinRoot.lift_of]

@[simp] theorem thetaBranch_yClass :
    thetaBranch (yClass M) = 0 := by
  exact AdjoinRoot.lift_root thetaBranch_root

theorem thetaBranch_conjugate
    (z : N13Mumford.CoordinateRing ℚ) :
    thetaBranch (conjugate M z) = thetaBranch z := by
  conv_lhs =>
    rw [← recompose M z]
  conv_rhs =>
    rw [← recompose M z]
  simp

/-- Evaluation `u(θ)` for a balanced Mumford representative. -/
def uTheta (D : N13Mumford.Mumford ℚ) : L :=
  thetaBranch (xClass M D.u)

@[simp] theorem uTheta_eq_mk (D : N13Mumford.Mumford ℚ) :
    uTheta D = AdjoinRoot.mk f D.u := by
  simp [uTheta]

theorem uTheta_ne_zero (D : N13Mumford.Mumford ℚ) :
    uTheta D ≠ 0 := by
  rw [uTheta_eq_mk]
  apply AdjoinRoot.mk_ne_zero_of_natDegree_lt
    (N13Mumford.f_monic ℚ) D.u_monic.ne_zero
  change D.u.natDegree < (N13Mumford.f ℚ).natDegree
  rw [N13Mumford.f_natDegree]
  have hdeg : D.u.natDegree ≤ 2 := D.deg_u
  omega

/-- The nonzero field element `u(θ)`, packaged as a unit. -/
def uThetaUnit (D : N13Mumford.Mumford ℚ) : Lˣ :=
  Units.mk0 (uTheta D) (uTheta_ne_zero D)

@[simp] theorem uThetaUnit_val (D : N13Mumford.Mumford ℚ) :
    (uThetaUnit D : L) = uTheta D := rfl

abbrev FakeTarget : Type :=
  Additive (FakeSquareClass.Target (algebraMap ℚ L))

/-- The raw fake-Kummer value of a balanced Mumford representative. -/
def mumfordFakeClass (D : N13Mumford.Mumford ℚ) : FakeTarget :=
  Additive.ofMul
    (((uThetaUnit D : Lˣ)) :
      FakeSquareClass.Target (algebraMap ℚ L))

@[simp] theorem uTheta_zero :
    uTheta (SexticMumford.zero M) = 1 := by
  simp [uTheta]

@[simp] theorem uThetaUnit_zero :
    uThetaUnit (SexticMumford.zero M) = 1 := by
  apply Units.ext
  exact uTheta_zero

@[simp] theorem mumfordFakeClass_zero :
    mumfordFakeClass (SexticMumford.zero M) = 0 := by
  change
    Additive.ofMul
        (((uThetaUnit (SexticMumford.zero M) : Lˣ)) :
          FakeSquareClass.Target (algebraMap ℚ L)) =
      0
  rw [uThetaUnit_zero]
  rfl

end

end MazurProof.N13MumfordKummerValue

end
end

-- module FLT.Assumptions.MazurProof.SexticMumfordFixedUnit
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordFixedUnit =====
section

/-!
# Units fixed by hyperelliptic conjugation

In the affine coordinate ring of a smooth monic sextic, a unit fixed by
hyperelliptic conjugation is a scalar.  This is the structural unit lemma
needed to make the fake Mumford--Kummer value independent of principal
ideal representatives.

The proof uses the rank-two basis `p(X) + q(X)Y`.  Conjugation changes the
sign of `q`, so characteristic zero forces `q = 0`.  Applying the same
basis to the inverse of the unit then shows that `p` is already a unit of
the polynomial ring, hence a nonzero constant.
-/

open Polynomial

namespace MazurProof.SexticMumford

noncomputable section

universe u

variable {K : Type u} [Field K]

variable (M : Model K)

theorem conjugate_eq_coeffs (z : CoordinateRing M) :
    conjugate M z =
      xClass M (coeff0 M z) -
        xClass M (coeffY M z) * yClass M := by
  conv_lhs =>
    rw [← recompose M z]
  simp only [map_add, map_mul, conjugate_xClass, conjugate_yClass]
  ring

@[simp] theorem coeffY_conjugate (z : CoordinateRing M) :
    coeffY M (conjugate M z) = -(coeffY M z) := by
  rw [conjugate_eq_coeffs]
  simp

variable [CharZero K]

/-- A coordinate-ring unit fixed by hyperelliptic conjugation is induced
by a unique nonzero scalar of the ground field. -/
theorem fixed_coordinate_unit_is_scalar
    (epsilon : (CoordinateRing M)ˣ)
    (hfix : conjugate M (epsilon : CoordinateRing M) = epsilon) :
    ∃ q : Kˣ,
      epsilon =
        Units.map
          (algebraMap K (CoordinateRing M)).toMonoidHom q := by
  let p : K[X] := coeff0 M (epsilon : CoordinateRing M)
  have hYeq := congrArg (coeffY M) hfix
  rw [coeffY_conjugate] at hYeq
  have hY : coeffY M (epsilon : CoordinateRing M) = 0 :=
    CharZero.neg_eq_self_iff.mp hYeq
  have hepsilon :
      (epsilon : CoordinateRing M) = xClass M p := by
    calc
      (epsilon : CoordinateRing M) =
          xClass M (coeff0 M (epsilon : CoordinateRing M)) +
            xClass M (coeffY M (epsilon : CoordinateRing M)) *
              yClass M :=
        (recompose M (epsilon : CoordinateRing M)).symm
      _ = xClass M p := by simp [p, hY]
  let epsilonInv : CoordinateRing M :=
    (epsilon⁻¹ : (CoordinateRing M)ˣ)
  let r : K[X] := coeff0 M epsilonInv
  have hprod :
      (epsilon : CoordinateRing M) * epsilonInv = 1 := by
    simp [epsilonInv]
  have hp : p ≠ 0 := by
    intro hp0
    exact epsilon.ne_zero (by
      rw [hepsilon, hp0, xClass_zero])
  have hinvY : coeffY M epsilonInv = 0 := by
    have hc := congrArg (coeffY M) hprod
    rw [hepsilon, coeffY_xClass_mul] at hc
    have hone :
        coeffY M (1 : CoordinateRing M) = 0 := by
      rw [← xClass_one M, coeffY_xClass]
    rw [hone] at hc
    exact (mul_eq_zero.mp hc).resolve_left hp
  have hepsilonInv :
      epsilonInv = xClass M r := by
    calc
      epsilonInv =
          xClass M (coeff0 M epsilonInv) +
            xClass M (coeffY M epsilonInv) * yClass M :=
        (recompose M epsilonInv).symm
      _ = xClass M r := by simp [r, hinvY]
  have hpr : p * r = 1 := by
    apply xClass_injective M
    calc
      xClass M (p * r) = xClass M p * xClass M r :=
        xClass_mul M p r
      _ = (epsilon : CoordinateRing M) * epsilonInv := by
        rw [hepsilon, hepsilonInv]
      _ = 1 := hprod
      _ = xClass M 1 := (xClass_one M).symm
  have hpunit : IsUnit p := by
    rw [isUnit_iff_exists]
    exact ⟨r, hpr, by simpa [mul_comm] using hpr⟩
  obtain ⟨a, ha, hCa⟩ := Polynomial.isUnit_iff.mp hpunit
  refine ⟨ha.unit, ?_⟩
  apply Units.ext
  change
    (epsilon : CoordinateRing M) =
      algebraMap K (CoordinateRing M) (ha.unit : K)
  rw [hepsilon, ← hCa]
  rw [IsUnit.unit_spec]
  rfl

end

end MazurProof.SexticMumford

end
end


