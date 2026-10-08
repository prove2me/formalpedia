-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoFiberNoEscape_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13TwoFiberNoEscape_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T21:44:32.10823+00:00
-- url     : https://prove2.me/theorems/822dbae0-b68a-4d13-a4be-1d64166fee8d
-- title:
--   FLT.Assumptions.MazurProof.N13TwoFiberNoEscape source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13TwoFiberNoEscape

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13TwoFiberNoEscape
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TensorSpecialFiber_p0
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing

set_option autoImplicit false




/-!
# Excluding denominator escape from two literal fibres

Let `B` be a torsion-free algebra over a domain `R`, with uniformizer
`π`.  Suppose two elements `e₀,e₁` reduce to a basis of a quotient over
`k = R/(π)`.  If every element of `B` can be brought into the span of
`e₀,e₁` after multiplication by some power of `π`, then it was already
in that span.

The proof removes one factor of `π` at a time.  Reduction modulo `π`
forces both coefficients to be divisible by `π`, and torsion-freeness
cancels the common factor.  This is the algebraic two-fibre no-escape
argument; it uses neither a finite presentation nor a valuation table.
-/

open Module

namespace MazurProof.N13TwoFiberNoEscape

noncomputable section

universe uR uk uB uC

variable {R : Type uR} {k : Type uk}
variable {B : Type uB} {C : Type uC}
variable [CommRing R] [IsDomain R]
variable [Field k]
variable [CommRing B] [CommRing C]
variable [Algebra R k] [Algebra R B] [Algebra R C]
variable [Algebra k C] [IsScalarTower R k C]
variable [Module.IsTorsionFree R B]

/-- The literal ordered pair used on both fibres. -/
def pairFamily (e₀ e₁ : B) : Fin 2 → B :=
  ![e₀, e₁]

@[simp] theorem pairFamily_zero (e₀ e₁ : B) :
    pairFamily e₀ e₁ (0 : Fin 2) = e₀ := by
  simp [pairFamily]

@[simp] theorem pairFamily_one (e₀ e₁ : B) :
    pairFamily e₀ e₁ (1 : Fin 2) = e₁ := by
  simp [pairFamily]

theorem range_pairFamily (e₀ e₁ : B) :
    Set.range (pairFamily e₀ e₁) = {e₀, e₁} := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

/--
One factor of the uniformizer can be removed from a two-generator
relation whose reductions form a basis.
-/
theorem cancel_uniformizer_of_reduced_basis
    (g : B →+* C)
    (hfactor :
      g.comp (algebraMap R B) =
        (algebraMap k C).comp (algebraMap R k))
    (π : R)
    (hπ_ne : π ≠ 0)
    (hπ_zero : algebraMap R k π = 0)
    (hker :
      RingHom.ker (algebraMap R k) =
        Ideal.span ({π} : Set R))
    (e₀ e₁ : B)
    (bC : Basis (Fin 2) k C)
    (he₀ : g e₀ = bC 0)
    (he₁ : g e₁ = bC 1)
    (z : B) (a₀ a₁ : R)
    (hz :
      π • z = a₀ • e₀ + a₁ • e₁) :
    ∃ c₀ c₁ : R,
      z = c₀ • e₀ + c₁ • e₁ := by
  have hgscalar (a : R) :
      g (algebraMap R B a) = algebraMap R C a := by
    calc
      g (algebraMap R B a) =
          algebraMap k C (algebraMap R k a) := by
        simpa only [RingHom.comp_apply] using
          DFunLike.congr_fun hfactor a
      _ = algebraMap R C a :=
        (IsScalarTower.algebraMap_apply R k C a).symm
  have hred :
      algebraMap R k a₀ • bC 0 +
          algebraMap R k a₁ • bC 1 = 0 := by
    calc
      algebraMap R k a₀ • bC 0 +
            algebraMap R k a₁ • bC 1 =
          g (a₀ • e₀ + a₁ • e₁) := by
            simp only [Algebra.smul_def, map_add, map_mul,
              he₀, he₁]
            rw [hgscalar a₀, hgscalar a₁]
            simp only [← IsScalarTower.algebraMap_apply R k C]
      _ = g (π • z) := congrArg g hz.symm
      _ = 0 := by
        simp only [Algebra.smul_def, map_mul]
        have hscalar :
            g (algebraMap R B π) =
              algebraMap k C (algebraMap R k π) := by
          simpa only [RingHom.comp_apply] using
            DFunLike.congr_fun hfactor π
        rw [hscalar, hπ_zero, map_zero, zero_mul]
  have ha₀ : algebraMap R k a₀ = 0 := by
    have hcoord :=
      congrArg (bC.coord (0 : Fin 2)) hred
    simp only [map_add, map_smul, map_zero,
      Basis.coord_apply, Basis.repr_self_apply] at hcoord
    simpa using hcoord
  have ha₁ : algebraMap R k a₁ = 0 := by
    have hcoord :=
      congrArg (bC.coord (1 : Fin 2)) hred
    simp only [map_add, map_smul, map_zero,
      Basis.coord_apply, Basis.repr_self_apply] at hcoord
    simpa using hcoord
  have ha₀_mem : a₀ ∈ Ideal.span ({π} : Set R) := by
    rw [← hker]
    exact RingHom.mem_ker.mpr ha₀
  have ha₁_mem : a₁ ∈ Ideal.span ({π} : Set R) := by
    rw [← hker]
    exact RingHom.mem_ker.mpr ha₁
  obtain ⟨c₀, hc₀⟩ := Ideal.mem_span_singleton.mp ha₀_mem
  obtain ⟨c₁, hc₁⟩ := Ideal.mem_span_singleton.mp ha₁_mem
  refine ⟨c₀, c₁, ?_⟩
  apply (smul_right_injective (M := B) hπ_ne)
  change π • z = π • (c₀ • e₀ + c₁ • e₁)
  rw [hz, hc₀, hc₁]
  simp only [mul_smul, smul_add]

/--
Iterating the one-step cancellation removes every power of `π`.
-/
theorem exists_pair_of_power_relation
    (g : B →+* C)
    (hfactor :
      g.comp (algebraMap R B) =
        (algebraMap k C).comp (algebraMap R k))
    (π : R)
    (hπ_ne : π ≠ 0)
    (hπ_zero : algebraMap R k π = 0)
    (hker :
      RingHom.ker (algebraMap R k) =
        Ideal.span ({π} : Set R))
    (e₀ e₁ : B)
    (bC : Basis (Fin 2) k C)
    (he₀ : g e₀ = bC 0)
    (he₁ : g e₁ = bC 1)
    (z : B)
    (hclear :
      ∃ n : ℕ, ∃ a₀ a₁ : R,
        (π ^ n) • z = a₀ • e₀ + a₁ • e₁) :
    ∃ a₀ a₁ : R,
      z = a₀ • e₀ + a₁ • e₁ := by
  obtain ⟨n, a₀, a₁, hz⟩ := hclear
  induction n generalizing z a₀ a₁ with
  | zero =>
      exact ⟨a₀, a₁, by simpa using hz⟩
  | succ n ih =>
      have hstep :
          π • ((π ^ n) • z) =
            a₀ • e₀ + a₁ • e₁ := by
        simpa only [pow_succ', mul_smul] using hz
      obtain ⟨c₀, c₁, hc⟩ :=
        cancel_uniformizer_of_reduced_basis
          g hfactor π hπ_ne hπ_zero hker
          e₀ e₁ bC he₀ he₁
          ((π ^ n) • z) a₀ a₁ hstep
      exact ih (z := z) (a₀ := c₀) (a₁ := c₁) hc

/--
The power-clearing hypothesis and a basis on the reduced fibre force the
two elements to span the entire integral algebra.
-/
theorem span_pair_eq_top
    (g : B →+* C)
    (hfactor :
      g.comp (algebraMap R B) =
        (algebraMap k C).comp (algebraMap R k))
    (π : R)
    (hπ_ne : π ≠ 0)
    (hπ_zero : algebraMap R k π = 0)
    (hker :
      RingHom.ker (algebraMap R k) =
        Ideal.span ({π} : Set R))
    (e₀ e₁ : B)
    (bC : Basis (Fin 2) k C)
    (he₀ : g e₀ = bC 0)
    (he₁ : g e₁ = bC 1)
    (hclear :
      ∀ z : B, ∃ n : ℕ, ∃ a₀ a₁ : R,
        (π ^ n) • z = a₀ • e₀ + a₁ • e₁) :
    Submodule.span R ({e₀, e₁} : Set B) = ⊤ := by
  rw [eq_top_iff]
  intro z
  intro _
  obtain ⟨a₀, a₁, hz⟩ :=
    exists_pair_of_power_relation
      g hfactor π hπ_ne hπ_zero hker
      e₀ e₁ bC he₀ he₁ z (hclear z)
  rw [hz]
  exact Submodule.add_mem _
    (Submodule.smul_mem _
      a₀ (Submodule.subset_span (Set.mem_insert e₀ {e₁})))
    (Submodule.smul_mem _
      a₁ (Submodule.subset_span
        (Set.mem_insert_iff.mpr
          (Or.inr (Set.mem_singleton e₁)))))

section FractionFieldClearing

universe uK uG

variable {K : Type uK} {G : Type uG}
variable [Field K] [CommRing G]
variable [Algebra R K] [IsFractionRing R K]
variable [Algebra R G] [Algebra K G]
variable [IsScalarTower R K G]

/--
Two coefficients in the fraction field admit one common nonzero
denominator.
-/
theorem exists_common_denominator
    (α₀ α₁ : K) :
    ∃ r : R, r ≠ 0 ∧
      ∃ a₀ a₁ : R,
        algebraMap R K r * α₀ = algebraMap R K a₀ ∧
        algebraMap R K r * α₁ = algebraMap R K a₁ := by
  obtain ⟨b₀, d₀, hd₀, hα₀⟩ :=
    IsFractionRing.div_surjective R α₀
  obtain ⟨b₁, d₁, hd₁, hα₁⟩ :=
    IsFractionRing.div_surjective R α₁
  have hd₀_ne : d₀ ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp hd₀
  have hd₁_ne : d₁ ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp hd₁
  have hmapd₀ : algebraMap R K d₀ ≠ 0 :=
    by simpa using (IsFractionRing.injective R K).ne hd₀_ne
  have hmapd₁ : algebraMap R K d₁ ≠ 0 :=
    by simpa using (IsFractionRing.injective R K).ne hd₁_ne
  refine ⟨d₀ * d₁, mul_ne_zero hd₀_ne hd₁_ne,
    b₀ * d₁, b₁ * d₀, ?_, ?_⟩
  · rw [← hα₀]
    push_cast
    field_simp
  · rw [← hα₁]
    push_cast
    field_simp

/--
A two-generator generic-fibre presentation clears to one integral
relation with an arbitrary nonzero scalar denominator.
-/
theorem exists_scalar_relation_of_fraction_pair
    (q : B →+* G)
    (hfactor :
      q.comp (algebraMap R B) = algebraMap R G)
    (hq : Function.Injective q)
    (e₀ e₁ z : B)
    (hgeneric :
      ∃ α₀ α₁ : K,
        q z = α₀ • q e₀ + α₁ • q e₁) :
    ∃ r : R, r ≠ 0 ∧
      ∃ a₀ a₁ : R,
        r • z = a₀ • e₀ + a₁ • e₁ := by
  obtain ⟨α₀, α₁, hz⟩ := hgeneric
  obtain ⟨r, hr, a₀, a₁, ha₀, ha₁⟩ :=
    exists_common_denominator (R := R) α₀ α₁
  refine ⟨r, hr, a₀, a₁, hq ?_⟩
  have hqscalar (a : R) :
      q (algebraMap R B a) = algebraMap R G a := by
    simpa only [RingHom.comp_apply] using
      DFunLike.congr_fun hfactor a
  calc
    q (r • z) =
        algebraMap R G r * q z := by
      simp only [Algebra.smul_def, map_mul, hqscalar]
    _ =
        algebraMap K G (algebraMap R K r) *
          (α₀ • q e₀ + α₁ • q e₁) := by
      rw [hz, IsScalarTower.algebraMap_apply R K G]
    _ =
        (algebraMap R K r * α₀) • q e₀ +
          (algebraMap R K r * α₁) • q e₁ := by
      simp only [Algebra.smul_def, mul_add, map_mul]
      ring
    _ =
        algebraMap R K a₀ • q e₀ +
          algebraMap R K a₁ • q e₁ := by
      rw [ha₀, ha₁]
    _ =
        q (a₀ • e₀ + a₁ • e₁) := by
      simp only [Algebra.smul_def, map_add, map_mul, hqscalar,
        IsScalarTower.algebraMap_apply R K G]

/--
Over a discrete valuation ring, the arbitrary denominator can be replaced
by a power of any chosen uniformizer.
-/
theorem exists_power_relation_of_fraction_pair
    [IsDiscreteValuationRing R]
    (π : R)
    (hπ : Irreducible π)
    (q : B →+* G)
    (hfactor :
      q.comp (algebraMap R B) = algebraMap R G)
    (hq : Function.Injective q)
    (e₀ e₁ z : B)
    (hgeneric :
      ∃ α₀ α₁ : K,
        q z = α₀ • q e₀ + α₁ • q e₁) :
    ∃ n : ℕ, ∃ a₀ a₁ : R,
      (π ^ n) • z = a₀ • e₀ + a₁ • e₁ := by
  obtain ⟨r, hr, a₀, a₁, hz⟩ :=
    exists_scalar_relation_of_fraction_pair
      (R := R) (K := K) q hfactor hq e₀ e₁ z hgeneric
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      hr hπ
  refine
    ⟨n, (↑(u⁻¹) : R) * a₀, (↑(u⁻¹) : R) * a₁, ?_⟩
  apply (smul_right_injective (M := B) u.ne_zero)
  change
    (u : R) • ((π ^ n) • z) =
      (u : R) •
        (((↑(u⁻¹) : R) * a₀) • e₀ +
          ((↑(u⁻¹) : R) * a₁) • e₁)
  rw [← mul_smul, ← hu, hz]
  simp only [smul_add, ← mul_smul]
  norm_num

/--
The generic basis gives the required two-coefficient presentation of every
generic image.
-/
theorem exists_generic_pair_of_basis
    (q : B →+* G)
    (e₀ e₁ z : B)
    (bG : Basis (Fin 2) K G)
    (he₀ : q e₀ = bG 0)
    (he₁ : q e₁ = bG 1) :
    ∃ α₀ α₁ : K,
      q z = α₀ • q e₀ + α₁ • q e₁ := by
  refine
    ⟨bG.repr (q z) 0, bG.repr (q z) 1, ?_⟩
  have hsum := bG.sum_repr (q z)
  rw [Fin.sum_univ_two] at hsum
  rw [he₀, he₁]
  exact hsum.symm

/--
An injective generic-fibre map carrying the pair to a basis proves
integral linear independence of the same pair.
-/
theorem pair_linearIndependent_of_fraction_basis
    (q : B →+* G)
    (hfactor :
      q.comp (algebraMap R B) = algebraMap R G)
    (hq : Function.Injective q)
    (e₀ e₁ : B)
    (bG : Basis (Fin 2) K G)
    (he₀ : q e₀ = bG 0)
    (he₁ : q e₁ = bG 1) :
    LinearIndependent R (pairFamily e₀ e₁) := by
  let qAlg : B →ₐ[R] G :=
    { toRingHom := q
      commutes' := fun a => by
        change q (algebraMap R B a) = algebraMap R G a
        simpa only [RingHom.comp_apply] using
          DFunLike.congr_fun hfactor a }
  have hmap :
      qAlg.toLinearMap ∘ pairFamily e₀ e₁ =
        (bG : Fin 2 → G) := by
    funext i
    fin_cases i
    · exact he₀
    · exact he₁
  have hliMap :
      LinearIndependent R
        (qAlg.toLinearMap ∘ pairFamily e₀ e₁) := by
    rw [hmap]
    exact bG.linearIndependent.restrict_scalars' R
  exact
    (qAlg.toLinearMap.linearIndependent_iff
      (LinearMap.ker_eq_bot.mpr hq)).mp hliMap

/--
The two-fibre argument in one statement: a generic basis clears
denominators, the reduced basis removes them, and generic injectivity gives
linear independence.  Hence the same literal pair is an integral basis.
-/
theorem exists_basis_of_two_fibres
    [IsDiscreteValuationRing R]
    (π : R)
    (hπ : Irreducible π)
    (g : B →+* C)
    (hfactorSpecial :
      g.comp (algebraMap R B) =
        (algebraMap k C).comp (algebraMap R k))
    (hπ_zero : algebraMap R k π = 0)
    (hkerSpecial :
      RingHom.ker (algebraMap R k) =
        Ideal.span ({π} : Set R))
    (q : B →+* G)
    (hfactorGeneric :
      q.comp (algebraMap R B) = algebraMap R G)
    (hq : Function.Injective q)
    (e₀ e₁ : B)
    (bC : Basis (Fin 2) k C)
    (hg₀ : g e₀ = bC 0)
    (hg₁ : g e₁ = bC 1)
    (bG : Basis (Fin 2) K G)
    (hq₀ : q e₀ = bG 0)
    (hq₁ : q e₁ = bG 1) :
    ∃ b : Basis (Fin 2) R B,
      (b : Fin 2 → B) = pairFamily e₀ e₁ := by
  have hπ_ne : π ≠ 0 := hπ.ne_zero
  have hclear :
      ∀ z : B, ∃ n : ℕ, ∃ a₀ a₁ : R,
        (π ^ n) • z = a₀ • e₀ + a₁ • e₁ := by
    intro z
    exact
      exists_power_relation_of_fraction_pair
        (R := R) (K := K) π hπ q hfactorGeneric hq
        e₀ e₁ z
        (exists_generic_pair_of_basis q e₀ e₁ z
          bG hq₀ hq₁)
  have hspanPair :
      Submodule.span R ({e₀, e₁} : Set B) = ⊤ :=
    span_pair_eq_top
      g hfactorSpecial π hπ_ne hπ_zero hkerSpecial
      e₀ e₁ bC hg₀ hg₁ hclear
  have hspan :
      Submodule.span R
          (Set.range (pairFamily e₀ e₁)) = ⊤ := by
    rw [range_pairFamily]
    exact hspanPair
  have hli :
      LinearIndependent R (pairFamily e₀ e₁) :=
    pair_linearIndependent_of_fraction_basis
      (R := R) (K := K)
      q hfactorGeneric hq e₀ e₁ bG hq₀ hq₁
  exact
    ⟨Basis.mk hli hspan.ge, Basis.coe_mk hli hspan.ge⟩

end FractionFieldClearing

end

end MazurProof.N13TwoFiberNoEscape


