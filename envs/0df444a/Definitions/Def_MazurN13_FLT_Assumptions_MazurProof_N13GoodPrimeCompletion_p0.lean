-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GoodPrimeCompletion_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13GoodPrimeCompletion_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:16:19.666992+00:00
-- url     : https://prove2.me/theorems/d8d0f08a-dcf0-4a49-b4aa-703d6d180390
-- title:
--   FLT.Assumptions.MazurProof.N13GoodPrimeCompletion source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13GoodPrimeCompletion

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13GoodPrimeCompletion
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_DedekindDomain_AdicValuation_p0
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.Henselian

set_option autoImplicit false




/-!
# Completion and Hensel interfaces for the N13 good-prime argument

The denominator-prime analysis needs only two local mechanisms.

First, the integer ring inside the adic completion is complete for the
powers of its maximal ideal, hence Henselian.  Mathlib already supplies
the valued-field completion and FLT supplies the exact description of
the maximal-ideal powers; the only missing bridge is the equality
between the inherited valuation topology and the adic topology.

Second, a global integer which becomes a valuation-one factor times a
square in the completion has even multiplicity at the original height-one
prime.  This follows directly from the compatibility of the completion
valuation with the global adic valuation.

For the mixed quadratic regime we also give a non-monic Hensel interface.
It is proved structurally by replacing

`a X² + b X + c`

near an approximate root by the monic polynomial

`Y² + B Y + a C`,

where `B` is the derivative and `C` is the value at the approximate root.
No root enumeration or finite residue-field search is used.
-/

open Filter Polynomial Topology WithZero Multiplicative IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped Ring algebraMap

namespace MazurProof.N13GoodPrimeCompletion

noncomputable section

/-- A simple approximate root of a quadratic lifts in any Henselian pair,
even when the quadratic is not monic. -/
theorem exists_quadratic_root_sub_mem_of_henselian
    {R : Type*} [CommRing R] [Nontrivial R]
    (I : Ideal R) [HenselianRing R I]
    (a b c x₀ : R)
    (hroot : a * x₀ ^ 2 + b * x₀ + c ∈ I)
    (hderiv : IsUnit (2 * a * x₀ + b)) :
    ∃ x : R,
      a * x ^ 2 + b * x + c = 0 ∧
        x - x₀ ∈ I := by
  let B := 2 * a * x₀ + b
  let C₀ := a * x₀ ^ 2 + b * x₀ + c
  let g : R[X] :=
    X ^ 2 + Polynomial.C B * X +
      Polynomial.C (a * C₀)
  have hg_monic : g.Monic := by
    dsimp [g]
    exact
      (isMonicOfDegree_add_add_two B
        (a * C₀)).monic
  have hg_zero : g.eval 0 ∈ I := by
    simpa [g, C₀] using
      I.mul_mem_left a hroot
  have hg_deriv :
      IsUnit
        (Ideal.Quotient.mk I
          (g.derivative.eval 0)) := by
    simpa [g, B] using
      hderiv.map (Ideal.Quotient.mk I)
  obtain ⟨y, hyroot, hyI⟩ :=
    HenselianRing.is_henselian
      g hg_monic 0 hg_zero hg_deriv
  have hyI' : y ∈ I := by
    simpa using hyI
  have hyroot' :
      y ^ 2 + B * y + a * C₀ = 0 := by
    simpa [g] using hyroot
  have hBy : IsUnit (B + y) := by
    have hB : IsUnit B := by
      simpa [B] using hderiv
    rcases hB with ⟨u, hu⟩
    have hyJ :
        y ∈ Ideal.jacobson (⊥ : Ideal R) :=
      HenselianRing.jac hyI'
    have hpert :
        IsUnit (y * (↑(u⁻¹) : R) + 1) :=
      (Ideal.mem_jacobson_bot.mp hyJ) _
    have hmul := u.isUnit.mul hpert
    rw [← hu]
    have heq :
        (u : R) *
            (y * (↑(u⁻¹) : R) + 1) =
          y + (u : R) := by
      calc
        (u : R) *
              (y * (↑(u⁻¹) : R) + 1) =
            ((u : R) * (↑(u⁻¹) : R)) * y +
              (u : R) := by
                ring
        _ = y + (u : R) := by
          simp
    rw [heq] at hmul
    simpa [add_comm] using hmul
  let z := -C₀ * (B + y)⁻¹ʳ
  have hyBy :
      y * (B + y) = -(a * C₀) := by
    linear_combination hyroot'
  have haz : a * z = y := by
    calc
      a * z =
          (-(a * C₀)) * (B + y)⁻¹ʳ := by
            simp [z]
            ring
      _ =
          (y * (B + y)) *
            (B + y)⁻¹ʳ := by
              rw [hyBy]
      _ = y := by
        rw [mul_assoc,
          Ring.mul_inverse_cancel _ hBy, mul_one]
  have hzBy : z * (B + y) = -C₀ := by
    calc
      z * (B + y) =
          -C₀ * ((B + y) *
            (B + y)⁻¹ʳ) := by
              simp [z]
              ring
      _ = -C₀ := by
        rw [Ring.mul_inverse_cancel _ hBy,
          mul_one]
  refine ⟨x₀ + z, ?_, ?_⟩
  · calc
      a * (x₀ + z) ^ 2 +
            b * (x₀ + z) + c =
          z * (a * z + B) + C₀ := by
            simp [B, C₀]
            ring
      _ = z * (B + y) + C₀ := by
        rw [haz]
        ring
      _ = 0 := by
        rw [hzBy]
        ring
  · have hzI : z ∈ I :=
      I.mul_mem_right _ (I.neg_mem hroot)
    simpa using hzI

variable {A K : Type*}
    [CommRing A] [Field K] [Algebra A K]
    [IsFractionRing A K] [IsDedekindDomain A]
    (v : HeightOneSpectrum A)

/-- The inherited valuation topology on the integer ring of the adic
completion is the topology defined by powers of its maximal ideal. -/
theorem completionIntegers_isAdic :
    IsAdic (v.completionIdeal K) := by
  letI :
      IsTopologicalRing
        (v.adicCompletionIntegers K) :=
    Subring.instIsTopologicalRing
      (v.adicCompletionIntegers K).toSubring
  rw [isAdic_iff]
  constructor
  · intro n
    obtain ⟨π, hπ⟩ :=
      adicCompletion.exists_uniformizer K v
    have hπ0 :
        (π : v.adicCompletion K) ≠ 0 := by
      exact_mod_cast
        adicCompletion.uniformizer_ne_zero hπ
    have hr :
        Valued.v.restrict
            ((π : v.adicCompletion K) ^ n) ≠
          0 := by
      rw [Valuation.ne_zero_iff]
      exact pow_ne_zero n hπ0
    have hvalπ_pow :
        Valued.v
            ((π : v.adicCompletion K) ^ n) =
          (↑(Multiplicative.ofAdd
            (-(n : ℤ))) : ℤᵐ⁰) := by
      rw [map_pow]
      change Valued.v π.val ^ n = _
      rw [hπ]
      norm_num
      norm_cast
      rw [← ofAdd_nsmul,
        Nat.smul_one_eq_cast]
    have hcont :
        Continuous
          (fun x : v.adicCompletionIntegers K =>
            (x : v.adicCompletion K)) :=
      continuous_subtype_val
    have hopen :=
      (Valued.isOpen_closedBall
        (v.adicCompletion K) hr).preimage hcont
    convert hopen using 1
    ext x
    simp only [Set.mem_preimage,
      Set.mem_setOf_eq]
    change
      (x ∈ (v.completionIdeal K) ^ n) ↔ _
    rw [adicCompletion.mem_completionIdeal_pow]
    rw [Valuation.restrict_le_iff, hvalπ_pow]
    rfl
  · intro s hs
    obtain ⟨u, hu, hus⟩ :=
      (mem_nhds_subtype
        (v.adicCompletionIntegers K :
          Set (v.adicCompletion K))
        (0 : v.adicCompletionIntegers K) s).mp hs
    have hu0 :
        u ∈ 𝓝 (0 : v.adicCompletion K) := by
      simpa using hu
    rw [Valued.mem_nhds_zero] at hu0
    obtain ⟨γ, hγ⟩ := hu0
    have hγ0 :
        MonoidWithZeroHom.ValueGroup₀.embedding
            γ.val ≠
          (0 : ℤᵐ⁰) := by
      intro h
      apply γ.ne_zero
      exact
        MonoidWithZeroHom.ValueGroup₀.embedding_injective
          (h.trans (map_zero _).symm)
    obtain ⟨n, hn⟩ :=
      exists_ofAdd_natCast_lt
        (x :=
          MonoidWithZeroHom.ValueGroup₀.embedding
            γ.val)
        hγ0
    refine ⟨n, fun x hx => hus (hγ ?_)⟩
    change
      Valued.v.restrict
          (x : v.adicCompletion K) <
        γ.val
    rw [Valuation.restrict_lt_iff_lt_embedding]
    exact
      (adicCompletion.mem_completionIdeal_pow
          K v x).mp hx
        |>.trans_lt hn

/-- The integer ring in the adic completion is complete for its maximal
ideal topology. -/
theorem completionIntegers_isAdicComplete :
    IsAdicComplete
      (v.completionIdeal K)
      (v.adicCompletionIntegers K) := by
  letI :
      IsUniformAddGroup
        (v.adicCompletionIntegers K) :=
    AddSubgroup.isUniformAddGroup
      (v.adicCompletionIntegers K).toSubring.toAddSubgroup
  apply (completionIntegers_isAdic v).isAdicComplete_iff.mpr
  constructor
  · exact
      @IsClosed.completeSpace_coe _ _
        (inferInstance :
          CompleteSpace (v.adicCompletion K))
        _
        (Valued.isClosed_valuationSubring _)
  · infer_instance

/-- The local integer ring attached to a height-one prime is a Henselian
pair with its maximal ideal. -/
theorem completionIntegers_henselianRing :
    HenselianRing
      (v.adicCompletionIntegers K)
      (v.completionIdeal K) := by
  letI :
      IsAdicComplete
        (v.completionIdeal K)
        (v.adicCompletionIntegers K) :=
    completionIntegers_isAdicComplete v
  infer_instance

/-- Completion-specialized non-monic quadratic Hensel lifting. -/
theorem exists_completion_quadratic_root_sub_mem
    (a b c x₀ : v.adicCompletionIntegers K)
    (hroot :
      a * x₀ ^ 2 + b * x₀ + c ∈
        v.completionIdeal K)
    (hderiv :
      IsUnit (2 * a * x₀ + b)) :
    ∃ x : v.adicCompletionIntegers K,
      a * x ^ 2 + b * x + c = 0 ∧
        x - x₀ ∈ v.completionIdeal K := by
  letI :
      HenselianRing
        (v.adicCompletionIntegers K)
        (v.completionIdeal K) :=
    completionIntegers_henselianRing v
  exact
    exists_quadratic_root_sub_mem_of_henselian
      (v.completionIdeal K)
      a b c x₀ hroot hderiv

/-- If a nonzero global integer becomes a valuation-one factor times a
square in the completion, its multiplicity at the original prime is
even. -/
theorem multiplicity_even_of_completion_eq_val_one_mul_sq
    {a : A} (ha : a ≠ 0)
    (ε z : v.adicCompletion K)
    (hε : Valued.v ε = (1 : ℤᵐ⁰))
    (h :
      (a : v.adicCompletion K) =
        ε * z ^ 2) :
    Even
      (multiplicity v.asIdeal
        (Ideal.span {a})) := by
  have hz : z ≠ 0 := by
    rintro rfl
    have hzero :
        (a : v.adicCompletion K) = 0 := by
      simpa using h
    have haC :
        (a : v.adicCompletion K) ≠ 0 := by
      have haK : (algebraMap A K) a ≠ 0 := by
        simpa only [map_zero] using (IsFractionRing.injective A K).ne ha
      have haKC :
          (algebraMap K (v.adicCompletion K)) ((algebraMap A K) a) ≠ 0 :=
        by simpa only [map_zero] using
          (FaithfulSMul.algebraMap_injective K (v.adicCompletion K)).ne haK
      change (algebraMap K (v.adicCompletion K)) ((algebraMap A K) a) ≠ 0
      exact haKC
    exact haC hzero
  have hvz :
      Valued.v z ≠ (0 : ℤᵐ⁰) := by
    simp [hz]
  have hva :
      Valued.v (a : v.adicCompletion K) =
        WithZero.exp
          (-(multiplicity v.asIdeal
            (Ideal.span {a}) : ℤ)) := by
    rw [v.valuedAdicCompletion_eq_valuation,
      v.valuation_of_algebraMap,
      v.intValuation_eq_exp_neg_multiplicity ha]
  have hvh := congrArg Valued.v h
  rw [map_mul, map_pow, hva, hε, one_mul] at hvh
  rw [← WithZero.exp_log hvz, pow_two,
    ← WithZero.exp_add] at hvh
  have hlog :
      -(multiplicity v.asIdeal
          (Ideal.span {a}) : ℤ) =
        WithZero.log (Valued.v z) +
          WithZero.log (Valued.v z) :=
    WithZero.exp_injective hvh
  apply (Int.even_coe_nat _).mp
  rw [← even_neg]
  exact
    ⟨WithZero.log (Valued.v z), hlog⟩

/-- Unit-times-square form of
`multiplicity_even_of_completion_eq_val_one_mul_sq`. -/
theorem multiplicity_even_of_completion_eq_unit_mul_sq
    {a : A} (ha : a ≠ 0)
    (u : (v.adicCompletionIntegers K)ˣ)
    (z : v.adicCompletion K)
    (h :
      (a : v.adicCompletion K) =
        ((u : v.adicCompletionIntegers K) :
          v.adicCompletion K) * z ^ 2) :
    Even
      (multiplicity v.asIdeal
        (Ideal.span {a})) := by
  apply
    multiplicity_even_of_completion_eq_val_one_mul_sq
      v ha
      ((u : v.adicCompletionIntegers K) :
        v.adicCompletion K)
      z
  · exact
      adicCompletionIntegers.isUnit_iff_valued_eq_one.mp
        u.isUnit
  · exact h

end

end MazurProof.N13GoodPrimeCompletion


