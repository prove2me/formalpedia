-- Prove2me | Definitions.Def_LanglandsTunnell_CubicInduction_AdditiveJacquet
-- name    : LanglandsTunnell_CubicInduction_AdditiveJacquet
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/4d29d6b4-5b06-5bc2-94f1-8892b8c52823
-- title:
--   Translation action and counting functional on p-adic step functions
-- statement:
--   Throughout, $v$ is a height-one prime of $\mathcal{O}_{\mathbb{Q}}$ and $K_v$ denotes `v.adicCompletion ℚ`, with its valuation taking values in $\mathbb{Z}^{\mathrm{mult}}\cup\{0\}$ written multiplicatively via `WithZero.exp`. The module sets up translation and an algebraic integration theory on complex-valued functions on $K_v$. For $y \in K_v$, `translateFn` is the $\mathbb{C}$-linear endomorphism $\varphi \mapsto (x \mapsto \varphi(x+y))$ of $K_v \to \mathbb{C}$, and `translateRep` packages these into a representation of the additive group of $K_v$, regarded multiplicatively. `stepFunctions` is the $\mathbb{C}$-submodule of those $\varphi$ that are locally constant with compact support; it is stable under translation, giving the subrepresentation `translateRepStep`, and `translationKer` is the span of all differences $\varphi(\cdot + y) - \varphi$, i.e. the submodule defining the coinvariants of this action. `ballIndicator v y k` is the indicator of the ball $\{x : |x-y| \le q_v^{-k}\}$ (written $\mathrm{v}(x-y) \le \exp(-k)$), a step function; these indicators span `stepFunctions`, and every step function is supported in a large ball and constant on the cosets of some small ball, with a finite set of coset representatives whose cardinality is a power of $N := \#(\mathcal{O}_{\mathbb{Q}}/v)$.
--
--   Supporting results identify the residue field of the valuation ring of $K_v$ with $\mathcal{O}_{\mathbb{Q}}/v$ up to a bijection, show it is finite with $N > 1$ elements, $N =$ `Ideal.absNorm v.asIdeal`, deduce that $K_v$ is a proper space and that balls are compact open, and construct finite systems of ball representatives at arbitrary levels, multiplicatively and additively.
--
--   `IsCountingFunctional` is the predicate on a linear functional $\Lambda$ on `stepFunctions` that $\Lambda(\mathbf{1}_{y+\mathfrak{p}^k}) = N^{-k}$ for all $y$ and all $k \in \mathbb{Z}$. Such a functional exists — a normalised sum over ball representatives, shown independent of all choices — and is unique; `countingFunctional` is a chosen one. It takes the value $1$ on the valuation ring, is invariant under every translation, and satisfies $\Lambda(\varphi(t\,\cdot)) = \|t\|^{-1}\Lambda(\varphi)$ for $t \ne 0$, where $\|\cdot\|$ is the normalised finite place norm.
--
--   **Relation to Mathlib.** Built on Mathlib's `IsLocallyConstant`, `HasCompactSupport`, `Representation` and adic completions of a number field; the counting functional is the project's own algebraic substitute for additive Haar measure on a $p$-adic field, Mathlib's measure-theoretic Haar machinery not being used here.
--
--   **Where it is used.** These are the local additive ingredients of the cubic-induction analysis entering the Langlands–Tunnell step, which supplies modularity of the mod $3$ representation attached to a Frey curve. The translation-invariant functional plays the role of additive Haar integration on $K_v$ when local additive characters and Jacquet-style functionals are manipulated.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_CubicInduction_AdditiveJacquet.lean

import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RepresentationTheory.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Algebra.Valued.LocallyCompact

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

noncomputable section

namespace LanglandsTunnell.CubicInduction

section AdditiveJacquet

variable (v : HeightOneSpectrum (𝓞 ℚ))

def translateFn (y : v.adicCompletion ℚ) : Module.End ℂ (v.adicCompletion ℚ → ℂ) where
  toFun φ := fun x => φ (x + y)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem translateFn_apply (y : v.adicCompletion ℚ) (φ : v.adicCompletion ℚ → ℂ)
    (x : v.adicCompletion ℚ) : translateFn v y φ x = φ (x + y) := rfl

def translateRep :
    Representation ℂ (Multiplicative (v.adicCompletion ℚ)) (v.adicCompletion ℚ → ℂ) where
  toFun y := translateFn v (Multiplicative.toAdd y)
  map_one' := by
    refine LinearMap.ext fun φ => funext fun x => ?_
    simp
  map_mul' y z := by
    refine LinearMap.ext fun φ => funext fun x => ?_
    simp [add_assoc]

def stepFunctions : Submodule ℂ (v.adicCompletion ℚ → ℂ) where
  carrier := {φ | IsLocallyConstant φ ∧ HasCompactSupport φ}
  add_mem' := fun {φ ψ} hφ hψ => ⟨hφ.1.add hψ.1, hφ.2.add hψ.2⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, by
    rw [HasCompactSupport, tsupport, Function.support_zero, closure_empty]
    exact isCompact_empty⟩
  smul_mem' := by
    intro c φ hφ
    obtain ⟨hlc, hcs⟩ := hφ
    exact ⟨hlc.comp (c * ·), hcs.comp_left (g := (c * ·)) (mul_zero c)⟩

theorem mem_stepFunctions_iff (φ : v.adicCompletion ℚ → ℂ) :
    φ ∈ stepFunctions v ↔ IsLocallyConstant φ ∧ HasCompactSupport φ := Iff.rfl

theorem translateFn_mem_stepFunctions (y : v.adicCompletion ℚ) {φ : v.adicCompletion ℚ → ℂ}
    (hφ : φ ∈ stepFunctions v) : translateFn v y φ ∈ stepFunctions v :=
  ⟨hφ.1.comp_continuous (continuous_add_const y), hφ.2.comp_homeomorph (Homeomorph.addRight y)⟩

def translateRepStep :
    Representation ℂ (Multiplicative (v.adicCompletion ℚ)) ↥(stepFunctions v) where
  toFun y := (translateFn v (Multiplicative.toAdd y)).restrict
    fun φ hφ => translateFn_mem_stepFunctions v (Multiplicative.toAdd y) hφ
  map_one' := by
    refine LinearMap.ext fun φ => Subtype.ext (funext fun x => ?_)
    simp [LinearMap.restrict_apply]
  map_mul' y z := by
    refine LinearMap.ext fun φ => Subtype.ext (funext fun x => ?_)
    simp [LinearMap.restrict_apply, add_assoc]

@[simp] theorem translateRepStep_apply_coe (y : Multiplicative (v.adicCompletion ℚ))
    (φ : ↥(stepFunctions v)) (x : v.adicCompletion ℚ) :
    (translateRepStep v y φ : v.adicCompletion ℚ → ℂ) x = (φ : v.adicCompletion ℚ → ℂ)
      (x + Multiplicative.toAdd y) := rfl

def translationKer : Submodule ℂ ↥(stepFunctions v) :=
  Submodule.span ℂ (Set.range fun p : Multiplicative (v.adicCompletion ℚ) × ↥(stepFunctions v) =>
    translateRepStep v p.1 p.2 - p.2)

theorem sub_mem_translationKer (y : Multiplicative (v.adicCompletion ℚ)) (φ : ↥(stepFunctions v)) :
    translateRepStep v y φ - φ ∈ translationKer v :=
  Submodule.subset_span ⟨(y, φ), rfl⟩

def ballIndicator (y : v.adicCompletion ℚ) (k : ℤ) : v.adicCompletion ℚ → ℂ :=
  fun x => if Valued.v (x - y) ≤ WithZero.exp (-k) then 1 else 0

theorem exists_valued_eq_exp (n : ℤ) :
    ∃ t : v.adicCompletion ℚ, t ≠ 0 ∧ Valued.v t = WithZero.exp n := by
  obtain ⟨t, ht⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective ℚ v (WithZero.exp n)
  refine ⟨t, ?_, ht⟩
  rintro rfl
  rw [map_zero] at ht
  exact WithZero.exp_ne_zero ht.symm

theorem setOf_valued_sub_le_eq_image (y : v.adicCompletion ℚ) {t : v.adicCompletion ℚ} (ht : t ≠ 0)
    {k : ℤ} (htk : Valued.v t = WithZero.exp (-k)) :
    {x : v.adicCompletion ℚ | Valued.v (x - y) ≤ WithZero.exp (-k)} =
      (fun z : v.adicCompletion ℚ => y + t * z) '' {z : v.adicCompletion ℚ | Valued.v z ≤ 1} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro hx
    refine ⟨t⁻¹ * (x - y), ?_, by rw [mul_inv_cancel_left₀ ht, add_sub_cancel]⟩
    rw [map_mul, map_inv₀, htk]
    calc (WithZero.exp (-k))⁻¹ * Valued.v (x - y)
        ≤ (WithZero.exp (-k))⁻¹ * WithZero.exp (-k) := mul_le_mul_right hx _
      _ = 1 := inv_mul_cancel₀ WithZero.exp_ne_zero
  · rintro ⟨z, hz, rfl⟩
    rw [add_sub_cancel_left, map_mul, htk]
    calc WithZero.exp (-k) * Valued.v z ≤ WithZero.exp (-k) * 1 := mul_le_mul_right hz _
      _ = WithZero.exp (-k) := mul_one _

theorem exists_integer_valued_sub_lt_one (x : v.adicCompletionIntegers ℚ) :
    ∃ a : 𝓞 ℚ, Valued.v (algebraMap (𝓞 ℚ) (v.adicCompletion ℚ) a - (x : v.adicCompletion ℚ)) < 1 := by
  have hbridge : ∀ z : ℚ, Valued.v (algebraMap ℚ (v.adicCompletion ℚ) z) = v.valuation ℚ z := fun z =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v z
  have hn : {z : v.adicCompletion ℚ | Valued.v (z - (x : v.adicCompletion ℚ)) < 1} ∈
      nhds (x : v.adicCompletion ℚ) := by
    refine Valued.mem_nhds.mpr ⟨1, fun z hz => ?_⟩
    have hz' : Valued.v.restrict (z - (x : v.adicCompletion ℚ)) < 1 := by
      rw [← Units.val_one]; exact hz
    exact (Valuation.restrict_lt_one_iff _).mp hz'
  obtain ⟨_, hz, y, rfl⟩ := mem_closure_iff_nhds.mp
    (HeightOneSpectrum.denseRange_algebraMap (K := ℚ) (v := v) (x : v.adicCompletion ℚ)) _ hn
  have hy1 : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) y - (x : v.adicCompletion ℚ)) < 1 := hz
  have hyint : v.valuation ℚ y ≤ 1 := by
    have hx1 : Valued.v (x : v.adicCompletion ℚ) ≤ 1 := x.2
    have h : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) y) ≤ 1 := by
      have := Valuation.map_add (Valued.v : Valuation (v.adicCompletion ℚ) _)
        (algebraMap ℚ (v.adicCompletion ℚ) y - (x : v.adicCompletion ℚ)) (x : v.adicCompletion ℚ)
      rw [sub_add_cancel] at this
      exact this.trans (max_le hy1.le hx1)
    rwa [hbridge] at h
  obtain ⟨a, ha⟩ := HeightOneSpectrum.exists_valuation_sub_lt_of_integer v hyint 1
  refine ⟨a, ?_⟩
  have ha' : Valued.v (algebraMap (𝓞 ℚ) (v.adicCompletion ℚ) a - algebraMap ℚ (v.adicCompletion ℚ) y) < 1 := by
    rw [IsScalarTower.algebraMap_apply (𝓞 ℚ) ℚ (v.adicCompletion ℚ) a, ← map_sub, hbridge]
    exact ha.trans_eq Units.val_one
  have := Valuation.map_add (Valued.v : Valuation (v.adicCompletion ℚ) _)
    (algebraMap (𝓞 ℚ) (v.adicCompletion ℚ) a - algebraMap ℚ (v.adicCompletion ℚ) y)
    (algebraMap ℚ (v.adicCompletion ℚ) y - (x : v.adicCompletion ℚ))
  rw [sub_add_sub_cancel] at this
  exact lt_of_le_of_lt this (max_lt ha' hy1)

theorem mem_maximalIdeal_adicCompletionIntegers_iff (d : v.adicCompletionIntegers ℚ) :
    d ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers ℚ) ↔ Valued.v (d : v.adicCompletion ℚ) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  have hd : Valued.v (d : v.adicCompletion ℚ) ≤ 1 := d.2
  exact ⟨fun h => lt_of_le_of_ne hd h, fun h => ne_of_lt h⟩

theorem residue_algebraMap_ringOfIntegers_surjective :
    Function.Surjective (fun a : 𝓞 ℚ => IsLocalRing.residue (v.adicCompletionIntegers ℚ)
      (algebraMap (𝓞 ℚ) (v.adicCompletionIntegers ℚ) a)) := by
  intro z
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
  obtain ⟨a, ha⟩ := exists_integer_valued_sub_lt_one v x
  refine ⟨a, ?_⟩
  show Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
  rw [Ideal.Quotient.eq, mem_maximalIdeal_adicCompletionIntegers_iff, AddSubgroupClass.coe_sub]
  exact ha

theorem residue_algebraMap_ringOfIntegers_eq_zero_iff (a : 𝓞 ℚ) :
    IsLocalRing.residue (v.adicCompletionIntegers ℚ) (algebraMap (𝓞 ℚ) (v.adicCompletionIntegers ℚ) a) = 0 ↔
      a ∈ v.asIdeal := by
  rw [IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_adicCompletionIntegers_iff]
  simp only [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_lt_one_iff_mem v a

theorem exists_bijective_quotient_residueField :
    ∃ f : 𝓞 ℚ ⧸ v.asIdeal → IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ), Function.Bijective f := by
  refine ⟨Ideal.Quotient.lift v.asIdeal
    ((IsLocalRing.residue (v.adicCompletionIntegers ℚ)).comp (algebraMap (𝓞 ℚ) (v.adicCompletionIntegers ℚ)))
    (fun a ha => (residue_algebraMap_ringOfIntegers_eq_zero_iff v a).mpr ha), ?_, ?_⟩
  · refine (injective_iff_map_eq_zero _).mpr fun z hz => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [Ideal.Quotient.lift_mk] at hz
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((residue_algebraMap_ringOfIntegers_eq_zero_iff v a).mp hz)
  · intro z
    obtain ⟨a, ha⟩ := residue_algebraMap_ringOfIntegers_surjective v z
    exact ⟨Ideal.Quotient.mk _ a, by rw [Ideal.Quotient.lift_mk]; exact ha⟩

theorem finite_residueField_adicCompletionIntegers_rat :
    Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) := by
  haveI : Finite (𝓞 ℚ ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  obtain ⟨f, hf⟩ := exists_bijective_quotient_residueField v
  exact Finite.of_surjective f hf.2

theorem natCard_residueField_adicCompletionIntegers :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) = Nat.card (𝓞 ℚ ⧸ v.asIdeal) := by
  obtain ⟨f, hf⟩ := exists_bijective_quotient_residueField v
  exact (Nat.card_eq_of_bijective f hf).symm

theorem one_lt_natCard_quot : 1 < Nat.card (𝓞 ℚ ⧸ v.asIdeal) := by
  rw [← natCard_residueField_adicCompletionIntegers v]
  haveI := finite_residueField_adicCompletionIntegers_rat v
  exact Finite.one_lt_card_iff_nontrivial.mpr inferInstance

theorem natCast_natCard_quot_ne_zero : (Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (by have := one_lt_natCard_quot v; omega)

theorem natCard_quot_eq_absNorm : Nat.card (𝓞 ℚ ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

open scoped Valued in

theorem properSpace_adicCompletion_rat : ProperSpace (v.adicCompletion ℚ) := by
  haveI : IsDiscreteValuationRing 𝒪[v.adicCompletion ℚ] :=
    inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers ℚ))
  haveI := finite_residueField_adicCompletionIntegers_rat v
  haveI : Finite 𝓀[v.adicCompletion ℚ] :=
    inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)))
  exact Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.mpr
    ⟨inferInstance, inferInstance, inferInstance⟩

open scoped Valued in

theorem isCompact_setOf_valued_le_one :
    IsCompact {x : v.adicCompletion ℚ | Valued.v x ≤ 1} := by
  haveI := properSpace_adicCompletion_rat v
  have h : CompactSpace 𝒪[v.adicCompletion ℚ] := Valued.integer.properSpace_iff_compactSpace_integer.mp inferInstance
  exact isCompact_iff_compactSpace.mpr h

theorem isCompact_setOf_valued_sub_le (y : v.adicCompletion ℚ) (k : ℤ) :
    IsCompact {x : v.adicCompletion ℚ | Valued.v (x - y) ≤ WithZero.exp (-k)} := by
  obtain ⟨t, ht, htk⟩ := exists_valued_eq_exp v (-k)
  rw [setOf_valued_sub_le_eq_image v y ht htk]
  exact (isCompact_setOf_valued_le_one v).image (continuous_const.add (continuous_const.mul continuous_id))

theorem isClopen_setOf_valued_sub_le (y : v.adicCompletion ℚ) (k : ℤ) :
    IsClopen {x : v.adicCompletion ℚ | Valued.v (x - y) ≤ WithZero.exp (-k)} := by
  obtain ⟨t, ht, htk⟩ := exists_valued_eq_exp v (-k)
  have hpre : {x : v.adicCompletion ℚ | Valued.v (x - y) ≤ WithZero.exp (-k)} =
      (fun x : v.adicCompletion ℚ => t⁻¹ * (x - y)) ⁻¹' {z : v.adicCompletion ℚ | Valued.v z ≤ 1} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, map_mul, map_inv₀, htk]
    constructor
    · intro hx
      calc (WithZero.exp (-k))⁻¹ * Valued.v (x - y)
          ≤ (WithZero.exp (-k))⁻¹ * WithZero.exp (-k) := mul_le_mul_right hx _
        _ = 1 := inv_mul_cancel₀ WithZero.exp_ne_zero
    · intro hx
      have h := mul_le_mul_right hx (WithZero.exp (-k))
      rwa [← mul_assoc, mul_inv_cancel₀ WithZero.exp_ne_zero, one_mul, mul_one] at h
  rw [hpre]
  exact (Valued.isClopen_integer (v.adicCompletion ℚ)).preimage
    (continuous_const.mul (continuous_id.sub continuous_const))

theorem ballIndicator_mem_stepFunctions (y : v.adicCompletion ℚ) (k : ℤ) :
    ballIndicator v y k ∈ stepFunctions v := by
  have hB := isClopen_setOf_valued_sub_le v y k
  refine (mem_stepFunctions_iff v _).mpr ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_, ?_⟩
  · by_cases hx : Valued.v (x - y) ≤ WithZero.exp (-k)
    · filter_upwards [hB.isOpen.mem_nhds hx] with z hz
      have hz' : Valued.v (z - y) ≤ WithZero.exp (-k) := hz
      show (if Valued.v (z - y) ≤ WithZero.exp (-k) then (1 : ℂ) else 0) =
        (if Valued.v (x - y) ≤ WithZero.exp (-k) then (1 : ℂ) else 0)
      rw [if_pos hz', if_pos hx]
    · filter_upwards [hB.isClosed.isOpen_compl.mem_nhds hx] with z hz
      have hz' : ¬ Valued.v (z - y) ≤ WithZero.exp (-k) := hz
      show (if Valued.v (z - y) ≤ WithZero.exp (-k) then (1 : ℂ) else 0) =
        (if Valued.v (x - y) ≤ WithZero.exp (-k) then (1 : ℂ) else 0)
      rw [if_neg hz', if_neg hx]
  · exact HasCompactSupport.intro (isCompact_setOf_valued_sub_le v y k)
      fun x hx => if_neg (hx : ¬ Valued.v (x - y) ≤ WithZero.exp (-k))

theorem exists_setOf_valued_sub_le_subset_of_isOpen {U : Set (v.adicCompletion ℚ)} (hU : IsOpen U)
    {x : v.adicCompletion ℚ} (hx : x ∈ U) :
    ∃ j : ℤ, {y : v.adicCompletion ℚ | Valued.v (y - x) ≤ WithZero.exp (-j)} ⊆ U := by
  by_contra hcon
  replace hcon : ∀ j : ℤ, ¬ {y : v.adicCompletion ℚ | Valued.v (y - x) ≤ WithZero.exp (-j)} ⊆ U :=
    fun j h => hcon ⟨j, h⟩
  set C : ℕ → Set (v.adicCompletion ℚ) :=
    fun n => {y : v.adicCompletion ℚ | Valued.v (y - x) ≤ WithZero.exp (-(n : ℤ))} \ U
  have hne : (⋂ n, C n).Nonempty := by
    refine IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C (fun n => ?_) (fun n => ?_)
      ?_ (fun n => ?_)
    · intro y hy
      have h1 : Valued.v (y - x) ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ)) := hy.1
      refine ⟨le_trans h1 (WithZero.exp_le_exp.mpr ?_), hy.2⟩
      push_cast
      omega
    · obtain ⟨y, hy⟩ := Set.not_subset.mp (hcon n)
      exact ⟨y, hy.1, hy.2⟩
    · exact (isCompact_setOf_valued_sub_le v x ((0 : ℕ) : ℤ)).diff hU
    · exact (isClopen_setOf_valued_sub_le v x n).isClosed.sdiff hU
  obtain ⟨y, hy⟩ := hne
  have hyU : y ∉ U := (Set.mem_iInter.mp hy 0).2
  have hyx : y = x := by
    by_contra hyx
    have h0 : Valued.v (y - x) ≠ 0 := (Valuation.ne_zero_iff _).mpr (sub_ne_zero.mpr hyx)
    obtain ⟨L, hL⟩ : ∃ L : ℤ, Valued.v (y - x) = WithZero.exp L := ⟨_, (WithZero.exp_log h0).symm⟩
    have hn' : Valued.v (y - x) ≤ WithZero.exp (-(((-L).toNat + 1 : ℕ) : ℤ)) :=
      (Set.mem_iInter.mp hy ((-L).toNat + 1)).1
    rw [hL, WithZero.exp_le_exp] at hn'
    have := Int.self_le_toNat (-L)
    push_cast at hn'
    omega
  exact hyU (hyx ▸ hx)

theorem exists_forall_eq_of_isLocallyConstant {φ : v.adicCompletion ℚ → ℂ} (hφ : IsLocallyConstant φ)
    (x : v.adicCompletion ℚ) :
    ∃ j : ℤ, ∀ y, Valued.v (y - x) ≤ WithZero.exp (-j) → φ y = φ x := by
  obtain ⟨U, hU, hxU, hconst⟩ := hφ.exists_open x
  obtain ⟨j, hj⟩ := exists_setOf_valued_sub_le_subset_of_isOpen v hU hxU
  exact ⟨j, fun y hy => hconst y (hj hy)⟩

theorem exists_valued_le_exp (x : v.adicCompletion ℚ) : ∃ n : ℕ, Valued.v x ≤ WithZero.exp (n : ℤ) := by
  by_cases h0 : Valued.v x = 0
  · exact ⟨0, by rw [h0]; exact zero_le'⟩
  · obtain ⟨L, hL⟩ : ∃ L : ℤ, Valued.v x = WithZero.exp L := ⟨_, (WithZero.exp_log h0).symm⟩
    refine ⟨L.toNat, ?_⟩
    rw [hL, WithZero.exp_le_exp]
    exact Int.self_le_toNat L

theorem exists_level_of_mem_stepFunctions {φ : v.adicCompletion ℚ → ℂ} (hφ : φ ∈ stepFunctions v) :
    ∃ k m : ℤ, (∀ x, φ x ≠ 0 → Valued.v x ≤ WithZero.exp m) ∧
      ∀ x y, Valued.v (x - y) ≤ WithZero.exp (-k) → φ x = φ y := by
  obtain ⟨hlc, hcs⟩ := (mem_stepFunctions_iff v φ).mp hφ

  choose j hj using exists_forall_eq_of_isLocallyConstant v hlc
  obtain ⟨t, -, ht⟩ := IsCompact.elim_nhds_subcover hcs
    (fun x => {y : v.adicCompletion ℚ | Valued.v (y - x) ≤ WithZero.exp (-(j x))})
    (fun x _ => (isClopen_setOf_valued_sub_le v x (j x)).isOpen.mem_nhds
      (by simp only [Set.mem_setOf_eq, sub_self, map_zero]; exact zero_le'))

  choose n hn using exists_valued_le_exp v
  obtain ⟨s, -, hs⟩ := IsCompact.elim_nhds_subcover hcs
    (fun x => {y : v.adicCompletion ℚ | Valued.v (y - 0) ≤ WithZero.exp (-(-(n x : ℤ)))})
    (fun x _ => (isClopen_setOf_valued_sub_le v 0 (-(n x : ℤ))).isOpen.mem_nhds
      (by simpa using hn x))
  refine ⟨(t.sup fun x => (j x).toNat : ℕ), (s.sup fun x => n x : ℕ), fun x hx => ?_, fun x y hxy => ?_⟩
  · have hxs : x ∈ tsupport φ := subset_tsupport φ hx
    obtain ⟨x₀, hx₀, hxx₀⟩ := Set.mem_iUnion₂.mp (hs hxs)
    have hxx₀' : Valued.v (x - 0) ≤ WithZero.exp (-(-(n x₀ : ℤ))) := hxx₀
    rw [sub_zero, neg_neg] at hxx₀'
    refine hxx₀'.trans (WithZero.exp_le_exp.mpr ?_)
    exact_mod_cast Finset.le_sup (f := fun x => n x) hx₀
  ·

    have key : ∀ x y, x ∈ tsupport φ →
        Valued.v (x - y) ≤ WithZero.exp (-((t.sup fun x => (j x).toNat : ℕ) : ℤ)) → φ x = φ y := by
      intro x y hx hxy
      obtain ⟨x₀, hx₀, hxx₀⟩ := Set.mem_iUnion₂.mp (ht hx)
      have hxx₀' : Valued.v (x - x₀) ≤ WithZero.exp (-(j x₀)) := hxx₀
      have hk : WithZero.exp (-((t.sup fun x => (j x).toNat : ℕ) : ℤ)) ≤ WithZero.exp (-(j x₀)) := by
        rw [WithZero.exp_le_exp, neg_le_neg_iff]
        exact (Int.self_le_toNat _).trans (by exact_mod_cast Finset.le_sup (f := fun x => (j x).toNat) hx₀)
      have hyx₀ : Valued.v (y - x₀) ≤ WithZero.exp (-(j x₀)) := by
        have e : y - x₀ = (x - x₀) - (x - y) := by ring
        rw [e]
        exact (Valuation.map_sub _ _ _).trans (max_le hxx₀' (hxy.trans hk))
      rw [hj x₀ x hxx₀', hj x₀ y hyx₀]
    by_cases hx : x ∈ tsupport φ
    · exact key x y hx hxy
    · by_cases hy : y ∈ tsupport φ
      · rw [Valuation.map_sub_swap] at hxy
        exact (key y x hy hxy).symm
      · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hy]

theorem withZero_lt_one_iff_le_exp_neg_one (e : WithZero (Multiplicative ℤ)) : e < 1 ↔ e ≤ WithZero.exp (-1) := by
  rcases eq_or_ne e 0 with rfl | he
  · exact iff_of_true (zero_lt_iff.mpr one_ne_zero) zero_le'
  · obtain ⟨n, rfl⟩ : ∃ n : ℤ, e = WithZero.exp n := ⟨_, (WithZero.exp_log he).symm⟩
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]
    omega

theorem exists_ball_representatives_zero_one :
    ∃ X : Finset (v.adicCompletion ℚ), (∀ r ∈ X, Valued.v r ≤ WithZero.exp (-(0 : ℤ))) ∧
      (∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-(0 : ℤ)) →
        ∃! r, r ∈ X ∧ Valued.v (x - r) ≤ WithZero.exp (-(1 : ℤ))) ∧
      X.card = Nat.card (𝓞 ℚ ⧸ v.asIdeal) := by
  classical
  haveI := finite_residueField_adicCompletionIntegers_rat v
  haveI : Fintype (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) := Fintype.ofFinite _
  obtain ⟨lift, hlift⟩ : ∃ lift : IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ) → v.adicCompletionIntegers ℚ,
      ∀ c, IsLocalRing.residue (v.adicCompletionIntegers ℚ) (lift c) = c :=
    ⟨fun c => (IsLocalRing.residue_surjective c).choose, fun c => (IsLocalRing.residue_surjective c).choose_spec⟩
  have key : ∀ (x : v.adicCompletion ℚ) (hx : Valued.v x ≤ 1) (d : v.adicCompletionIntegers ℚ),
      Valued.v (x - (d : v.adicCompletion ℚ)) ≤ WithZero.exp (-1) ↔
        IsLocalRing.residue (v.adicCompletionIntegers ℚ) ⟨x, hx⟩ =
          IsLocalRing.residue (v.adicCompletionIntegers ℚ) d := by
    intro x hx d
    rw [← withZero_lt_one_iff_le_exp_neg_one, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
      mem_maximalIdeal_adicCompletionIntegers_iff]
    simp
  have hinj : Function.Injective fun c => ((lift c : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) := by
    intro c c' h
    have h' := congrArg (IsLocalRing.residue (v.adicCompletionIntegers ℚ)) (Subtype.val_injective h)
    rwa [hlift, hlift] at h'
  refine ⟨Finset.univ.image fun c => ((lift c : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ), ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hr
    rw [neg_zero, WithZero.exp_zero]
    exact (lift c).2
  · intro x hx
    rw [neg_zero, WithZero.exp_zero] at hx
    refine ⟨((lift (IsLocalRing.residue (v.adicCompletionIntegers ℚ) ⟨x, hx⟩) : v.adicCompletionIntegers ℚ) :
        v.adicCompletion ℚ),
      ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), (key x hx _).mpr (hlift _).symm⟩, ?_⟩
    rintro r ⟨hr, hclose⟩
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hr
    have hc := (key x hx _).mp hclose
    rw [hlift] at hc
    rw [← hc]
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, ← Nat.card_eq_fintype_card,
      natCard_residueField_adicCompletionIntegers]

theorem valued_mul_le_exp_iff {t : v.adicCompletion ℚ} {a : ℤ} (hta : Valued.v t = WithZero.exp (-a))
    (z : v.adicCompletion ℚ) (j : ℤ) :
    Valued.v (t * z) ≤ WithZero.exp (-(j + a)) ↔ Valued.v z ≤ WithZero.exp (-j) := by
  rw [map_mul, hta, show -(j + a) = -a + -j by ring, WithZero.exp_add]
  constructor
  · intro h
    have h' := mul_le_mul_right h (WithZero.exp (-a))⁻¹
    rwa [inv_mul_cancel_left₀ WithZero.exp_ne_zero, inv_mul_cancel_left₀ WithZero.exp_ne_zero] at h'
  · intro h
    exact mul_le_mul_right h _

theorem exists_ball_representatives_of_valued_eq {k m : ℤ} {X : Finset (v.adicCompletion ℚ)}
    (hX : ∀ r ∈ X, Valued.v r ≤ WithZero.exp (-k))
    (hX' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-k) →
      ∃! r, r ∈ X ∧ Valued.v (x - r) ≤ WithZero.exp (-m))
    {t : v.adicCompletion ℚ} (ht : t ≠ 0) {a : ℤ} (hta : Valued.v t = WithZero.exp (-a))
    {k' m' : ℤ} (hk' : k' = k + a) (hm' : m' = m + a) :
    ∃ Y : Finset (v.adicCompletion ℚ), (∀ r ∈ Y, Valued.v r ≤ WithZero.exp (-k')) ∧
      (∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-k') →
        ∃! r, r ∈ Y ∧ Valued.v (x - r) ≤ WithZero.exp (-m')) ∧
      Y.card = X.card := by
  classical
  subst hk' hm'
  refine ⟨X.image (t * ·), ?_, ?_, Finset.card_image_of_injective _ (mul_right_injective₀ ht)⟩
  · intro r hr
    obtain ⟨r₀, hr₀, rfl⟩ := Finset.mem_image.mp hr
    exact (valued_mul_le_exp_iff v hta r₀ k).mpr (hX r₀ hr₀)
  · intro x hx
    have hx' : Valued.v (t⁻¹ * x) ≤ WithZero.exp (-k) := by
      rw [← valued_mul_le_exp_iff v hta, mul_inv_cancel_left₀ ht]
      exact hx
    obtain ⟨r₀, ⟨hr₀, hxr₀⟩, huniq⟩ := hX' (t⁻¹ * x) hx'
    refine ⟨t * r₀, ⟨Finset.mem_image_of_mem _ hr₀, ?_⟩, ?_⟩
    · have e : x - t * r₀ = t * (t⁻¹ * x - r₀) := by rw [mul_sub, mul_inv_cancel_left₀ ht]
      rw [e]
      exact (valued_mul_le_exp_iff v hta _ m).mpr hxr₀
    · rintro r ⟨hr, hclose⟩
      obtain ⟨r₁, hr₁, rfl⟩ := Finset.mem_image.mp hr
      have e : x - t * r₁ = t * (t⁻¹ * x - r₁) := by rw [mul_sub, mul_inv_cancel_left₀ ht]
      rw [e, valued_mul_le_exp_iff v hta] at hclose
      rw [huniq r₁ ⟨hr₁, hclose⟩]

theorem exists_ball_representatives_add {k n : ℤ} (hkn : k ≤ n) {X Y : Finset (v.adicCompletion ℚ)}
    (hX : ∀ r ∈ X, Valued.v r ≤ WithZero.exp (-k))
    (hX' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-k) →
      ∃! r, r ∈ X ∧ Valued.v (x - r) ≤ WithZero.exp (-n))
    (hY : ∀ s ∈ Y, Valued.v s ≤ WithZero.exp (-n))
    (hY' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-n) →
      ∃! s, s ∈ Y ∧ Valued.v (x - s) ≤ WithZero.exp (-(n + 1))) :
    ∃ Z : Finset (v.adicCompletion ℚ), (∀ z ∈ Z, Valued.v z ≤ WithZero.exp (-k)) ∧
      (∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-k) →
        ∃! z, z ∈ Z ∧ Valued.v (x - z) ≤ WithZero.exp (-(n + 1))) ∧
      Z.card = X.card * Y.card ∧
      ∀ ψ : v.adicCompletion ℚ → ℂ, ∑ z ∈ Z, ψ z = ∑ r ∈ X, ∑ s ∈ Y, ψ (r + s) := by
  classical
  have hn1 : WithZero.exp (-(n + 1)) ≤ WithZero.exp (-n) := WithZero.exp_le_exp.mpr (by omega)
  have hn0 : WithZero.exp (-n) ≤ WithZero.exp (-k) := WithZero.exp_le_exp.mpr (by omega)

  have hdecomp : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-k) →
      ∃! p : v.adicCompletion ℚ × v.adicCompletion ℚ, p ∈ X ×ˢ Y ∧
        Valued.v (x - (p.1 + p.2)) ≤ WithZero.exp (-(n + 1)) := by
    intro x hx
    obtain ⟨r, ⟨hr, hxr⟩, hruniq⟩ := hX' x hx
    obtain ⟨s, ⟨hs, hxs⟩, hsuniq⟩ := hY' (x - r) hxr
    refine ⟨(r, s), ⟨Finset.mem_product.mpr ⟨hr, hs⟩, ?_⟩, ?_⟩
    · show Valued.v (x - (r + s)) ≤ WithZero.exp (-(n + 1))
      rw [← sub_sub]
      exact hxs
    rintro ⟨r', s'⟩ ⟨hp, hclose⟩
    replace hclose : Valued.v (x - (r' + s')) ≤ WithZero.exp (-(n + 1)) := hclose
    obtain ⟨hr', hs'⟩ := Finset.mem_product.mp hp
    have hxr' : Valued.v (x - r') ≤ WithZero.exp (-n) := by
      have e : x - r' = (x - (r' + s')) + s' := by ring
      rw [e]
      exact (Valuation.map_add _ _ _).trans (max_le (hclose.trans hn1) (hY s' hs'))
    obtain rfl : r' = r := hruniq r' ⟨hr', hxr'⟩
    have hss : s' = s := hsuniq s' ⟨hs', by rw [sub_sub]; exact hclose⟩
    rw [hss]
  have hsum : ∀ p ∈ X ×ˢ Y, Valued.v (Prod.fst p + Prod.snd p) ≤ WithZero.exp (-k) := by
    intro p hp
    obtain ⟨hr, hs⟩ := Finset.mem_product.mp hp
    exact (Valuation.map_add _ _ _).trans (max_le (hX _ hr) ((hY _ hs).trans hn0))
  have hinj : Set.InjOn (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ => p.1 + p.2)
      (((X ×ˢ Y : Finset (v.adicCompletion ℚ × v.adicCompletion ℚ)) :
        Set (v.adicCompletion ℚ × v.adicCompletion ℚ))) := by
    intro p hp p' hp' hpp'
    have hpp'' : p.1 + p.2 = p'.1 + p'.2 := hpp'
    obtain ⟨q, -, hquniq⟩ := hdecomp (p.1 + p.2) (hsum p hp)
    have h1 : p = q := hquniq p ⟨hp, by rw [sub_self, map_zero]; exact zero_le'⟩
    have h2 : p' = q := hquniq p' ⟨hp', by rw [hpp'', sub_self, map_zero]; exact zero_le'⟩
    rw [h1, h2]
  refine ⟨(X ×ˢ Y).image fun p => p.1 + p.2, ?_, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
    exact hsum p hp
  · intro x hx
    obtain ⟨p, ⟨hp, hxp⟩, hpuniq⟩ := hdecomp x hx
    refine ⟨p.1 + p.2, ⟨Finset.mem_image_of_mem _ hp, hxp⟩, ?_⟩
    rintro z ⟨hz, hxz⟩
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hz
    rw [hpuniq p' ⟨hp', hxz⟩]
  · rw [Finset.card_image_of_injOn hinj, Finset.card_product]
  · intro ψ
    rw [Finset.sum_image hinj, Finset.sum_product]

theorem exists_ball_representatives_zero (n : ℕ) :
    ∃ X : Finset (v.adicCompletion ℚ), (∀ r ∈ X, Valued.v r ≤ WithZero.exp (-(0 : ℤ))) ∧
      (∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-(0 : ℤ)) →
        ∃! r, r ∈ X ∧ Valued.v (x - r) ≤ WithZero.exp (-(n : ℤ))) ∧
      X.card = Nat.card (𝓞 ℚ ⧸ v.asIdeal) ^ n := by
  induction n with
  | zero =>
    refine ⟨{0}, fun r hr => ?_, fun x hx => ⟨0, ⟨Finset.mem_singleton_self 0, ?_⟩, fun r hr => ?_⟩, ?_⟩
    · rw [Finset.mem_singleton.mp hr, map_zero]
      exact zero_le'
    · rw [sub_zero]
      exact hx.trans (WithZero.exp_le_exp.mpr (by simp))
    · exact Finset.mem_singleton.mp hr.1
    · simp
  | succ n ih =>
    obtain ⟨X, hX, hX', hXcard⟩ := ih
    obtain ⟨B, hB, hB', hBcard⟩ := exists_ball_representatives_zero_one v
    obtain ⟨t, ht, hta⟩ := exists_valued_eq_exp v (-(n : ℤ))
    obtain ⟨Y, hY, hY', hYcard⟩ := exists_ball_representatives_of_valued_eq v hB hB' ht hta
      (k' := (n : ℤ)) (m' := (n : ℤ) + 1) (by simp) (by ring)
    obtain ⟨Z, hZ, hZ', hZcard, -⟩ := exists_ball_representatives_add v (n.cast_nonneg) hX hX' hY hY'
    refine ⟨Z, hZ, ?_, ?_⟩
    · push_cast
      exact hZ'
    · rw [hZcard, hXcard, hYcard, hBcard, pow_succ]

theorem exists_finset_ball_representatives (k m : ℤ) (hkm : k ≤ m) :
    ∃ X : Finset (v.adicCompletion ℚ), (∀ r ∈ X, Valued.v r ≤ WithZero.exp (-k)) ∧
      (∀ x, Valued.v x ≤ WithZero.exp (-k) → ∃! r, r ∈ X ∧ Valued.v (x - r) ≤ WithZero.exp (-m)) ∧
      X.card = (Nat.card (𝓞 ℚ ⧸ v.asIdeal)) ^ (m - k).toNat := by
  obtain ⟨X₀, hX₀, hX₀', hX₀card⟩ := exists_ball_representatives_zero v (m - k).toNat
  obtain ⟨t, ht, htk⟩ := exists_valued_eq_exp v (-k)
  have hmk : (((m - k).toNat : ℕ) : ℤ) = m - k := Int.toNat_of_nonneg (sub_nonneg.mpr hkm)
  obtain ⟨X, hX, hX', hXcard⟩ := exists_ball_representatives_of_valued_eq v hX₀ hX₀' ht htk
    (k' := k) (m' := m) (by simp) (by rw [hmk]; ring)
  exact ⟨X, hX, hX', by rw [hXcard, hX₀card]⟩

theorem translateFn_ballIndicator (c y : v.adicCompletion ℚ) (k : ℤ) :
    translateFn v c (ballIndicator v y k) = ballIndicator v (y - c) k := by
  funext x
  simp only [translateFn_apply, ballIndicator]
  rw [show x + c - y = x - (y - c) by ring]

theorem ballIndicator_eq_sum_ballIndicator (y : v.adicCompletion ℚ) {k m : ℤ} (hkm : k ≤ m)
    {X : Finset (v.adicCompletion ℚ)} (hX : ∀ r ∈ X, Valued.v r ≤ WithZero.exp (-k))
    (hX' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-k) →
      ∃! r, r ∈ X ∧ Valued.v (x - r) ≤ WithZero.exp (-m)) :
    ballIndicator v y k = ∑ r ∈ X, ballIndicator v (y + r) m := by
  have hmk : WithZero.exp (-m) ≤ WithZero.exp (-k) := WithZero.exp_le_exp.mpr (by omega)
  funext x
  rw [Finset.sum_apply]
  simp only [ballIndicator]
  by_cases hx : Valued.v (x - y) ≤ WithZero.exp (-k)
  · rw [if_pos hx]
    obtain ⟨r₀, ⟨hr₀, hxr₀⟩, huniq⟩ := hX' (x - y) hx
    rw [Finset.sum_eq_single_of_mem r₀ hr₀]
    · rw [if_pos]
      rw [show x - (y + r₀) = x - y - r₀ by ring]
      exact hxr₀
    · intro r hr hne
      rw [if_neg]
      intro h
      apply hne
      refine huniq r ⟨hr, ?_⟩
      rw [show x - y - r = x - (y + r) by ring]
      exact h
  · rw [if_neg hx]
    symm
    refine Finset.sum_eq_zero fun r hr => ?_
    rw [if_neg]
    intro h
    apply hx
    rw [show x - y = (x - (y + r)) + r by ring]
    exact (Valuation.map_add _ _ _).trans (max_le (h.trans hmk) (hX r hr))

theorem stepFunctions_le_span_ballIndicator :
    stepFunctions v ≤ Submodule.span ℂ
      (Set.range fun p : v.adicCompletion ℚ × ℤ => ballIndicator v p.1 p.2) := by
  intro φ hφ
  obtain ⟨k, m, hsupp, hconst⟩ := exists_level_of_mem_stepFunctions v hφ

  set k₁ : ℤ := max k (-m) with hk₁
  have hkk₁ : WithZero.exp (-k₁) ≤ WithZero.exp (-k) := WithZero.exp_le_exp.mpr (by omega)
  have hk₁m : WithZero.exp (-k₁) ≤ WithZero.exp (-(-m)) := WithZero.exp_le_exp.mpr (by omega)
  obtain ⟨X, hX, hX', -⟩ := exists_finset_ball_representatives v (-m) k₁ (by omega)
  have hφeq : φ = ∑ r ∈ X, φ r • ballIndicator v r k₁ := by
    funext x
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, ballIndicator]
    by_cases hx : Valued.v x ≤ WithZero.exp (-(-m))
    · obtain ⟨r₀, ⟨hr₀, hxr₀⟩, huniq⟩ := hX' x hx
      rw [Finset.sum_eq_single_of_mem r₀ hr₀]
      · rw [if_pos hxr₀, mul_one]
        exact hconst x r₀ (hxr₀.trans hkk₁)
      · intro r hr hne
        rw [if_neg fun h => hne (huniq r ⟨hr, h⟩), mul_zero]
    · rw [neg_neg] at hx
      rw [of_not_not (mt (hsupp x) hx)]
      symm
      refine Finset.sum_eq_zero fun r hr => ?_
      rw [if_neg, mul_zero]
      intro h
      apply hx
      rw [show x = (x - r) + r by ring]
      refine (Valuation.map_add _ _ _).trans (max_le (h.trans ?_) ?_)
      · rwa [neg_neg] at hk₁m
      · have := hX r hr
        rwa [neg_neg] at this
  rw [hφeq]
  exact Submodule.sum_mem _ fun r _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨(r, k₁), rfl⟩)

theorem span_ballIndicator_eq_top :
    Submodule.span ℂ (Set.range fun p : v.adicCompletion ℚ × ℤ =>
      (⟨ballIndicator v p.1 p.2, ballIndicator_mem_stepFunctions v p.1 p.2⟩ :
        ↥(stepFunctions v))) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨φ, hφ⟩ -
  have hle : Submodule.span ℂ (Set.range fun p : v.adicCompletion ℚ × ℤ => ballIndicator v p.1 p.2) ≤
      Submodule.map (stepFunctions v).subtype (Submodule.span ℂ
        (Set.range fun p : v.adicCompletion ℚ × ℤ =>
          (⟨ballIndicator v p.1 p.2, ballIndicator_mem_stepFunctions v p.1 p.2⟩ : ↥(stepFunctions v)))) := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨y, k⟩, rfl⟩
    exact ⟨⟨ballIndicator v y k, ballIndicator_mem_stepFunctions v y k⟩,
      Submodule.subset_span ⟨(y, k), rfl⟩, rfl⟩
  obtain ⟨ψ, hψ, hψφ⟩ := hle (stepFunctions_le_span_ballIndicator v hφ)
  have hεq : (⟨φ, hφ⟩ : ↥(stepFunctions v)) = ψ := Subtype.ext (by simpa using hψφ.symm)
  rw [hεq]
  exact hψ

theorem sum_ite_valued_sub_le {k m : ℤ} {X : Finset (v.adicCompletion ℚ)}
    (hX' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-k) →
      ∃! r, r ∈ X ∧ Valued.v (x - r) ≤ WithZero.exp (-m))
    {x : v.adicCompletion ℚ} (hx : Valued.v x ≤ WithZero.exp (-k)) (c : ℂ) :
    (∑ r ∈ X, if Valued.v (x - r) ≤ WithZero.exp (-m) then c else 0) = c := by
  obtain ⟨r₀, ⟨hr₀, hxr₀⟩, huniq⟩ := hX' x hx
  rw [Finset.sum_eq_single_of_mem r₀ hr₀, if_pos hxr₀]
  intro r hr hne
  exact if_neg fun h => hne (huniq r ⟨hr, h⟩)

theorem sum_eq_sum_of_ball_representatives {φ : v.adicCompletion ℚ → ℂ} {k m : ℤ}
    (hconst : ∀ x y, Valued.v (x - y) ≤ WithZero.exp (-m) → φ x = φ y)
    {X : Finset (v.adicCompletion ℚ)} (hX : ∀ r ∈ X, Valued.v r ≤ WithZero.exp (-k))
    (hX' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-k) →
      ∃! r, r ∈ X ∧ Valued.v (x - r) ≤ WithZero.exp (-m))
    {X' : Finset (v.adicCompletion ℚ)} (hY : ∀ r ∈ X', Valued.v r ≤ WithZero.exp (-k))
    (hY' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-k) →
      ∃! r, r ∈ X' ∧ Valued.v (x - r) ≤ WithZero.exp (-m)) :
    ∑ r ∈ X, φ r = ∑ r ∈ X', φ r :=
  calc ∑ r ∈ X, φ r
      = ∑ r ∈ X, ∑ r' ∈ X', (if Valued.v (r - r') ≤ WithZero.exp (-m) then φ r' else 0) := by
        refine Finset.sum_congr rfl fun r hr => ?_
        obtain ⟨r', ⟨hr', hrr'⟩, huniq⟩ := hY' r (hX r hr)
        rw [Finset.sum_eq_single_of_mem r' hr', if_pos hrr']
        · exact hconst r r' hrr'
        · intro s hs hne
          exact if_neg fun h => hne (huniq s ⟨hs, h⟩)
    _ = ∑ r' ∈ X', ∑ r ∈ X, (if Valued.v (r - r') ≤ WithZero.exp (-m) then φ r' else 0) :=
        Finset.sum_comm
    _ = ∑ r' ∈ X', φ r' := by
        refine Finset.sum_congr rfl fun r' hr' => ?_
        refine Eq.trans (Finset.sum_congr rfl fun r _ => ?_) (sum_ite_valued_sub_le v hX' (hY r' hr') (φ r'))
        rw [Valuation.map_sub_swap]

theorem inv_zpow_mul_sum_eq_of_eq_add_one {φ : v.adicCompletion ℚ → ℂ} {k m : ℤ} (hkm : k ≤ m)
    (hconst : ∀ x y, Valued.v (x - y) ≤ WithZero.exp (-m) → φ x = φ y)
    {X : Finset (v.adicCompletion ℚ)} (hX : ∀ r ∈ X, Valued.v r ≤ WithZero.exp (-k))
    (hX' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-k) →
      ∃! r, r ∈ X ∧ Valued.v (x - r) ≤ WithZero.exp (-m))
    {m₁ : ℤ} (hm₁ : m₁ = m + 1)
    {X₁ : Finset (v.adicCompletion ℚ)} (hX₁ : ∀ r ∈ X₁, Valued.v r ≤ WithZero.exp (-k))
    (hX₁' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-k) →
      ∃! r, r ∈ X₁ ∧ Valued.v (x - r) ≤ WithZero.exp (-m₁)) :
    ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℂ) ^ m₁)⁻¹ * ∑ r ∈ X₁, φ r =
      ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℂ) ^ m)⁻¹ * ∑ r ∈ X, φ r := by
  subst hm₁
  have hq := natCast_natCard_quot_ne_zero v
  obtain ⟨Y, hY, hY', hYcard⟩ := exists_finset_ball_representatives v m (m + 1) (by omega)
  obtain ⟨Z, hZ, hZ', -, hZsum⟩ := exists_ball_representatives_add v hkm hX hX' hY hY'
  have hconst' : ∀ x y, Valued.v (x - y) ≤ WithZero.exp (-(m + 1)) → φ x = φ y :=
    fun x y hxy => hconst x y (hxy.trans (WithZero.exp_le_exp.mpr (by omega)))
  have hYq : Y.card = Nat.card (𝓞 ℚ ⧸ v.asIdeal) := by rw [hYcard]; simp
  have hinner : ∀ r, ∑ s ∈ Y, φ (r + s) = (Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℂ) * φ r := fun r => by
    rw [Finset.sum_congr rfl fun s hs => hconst (r + s) r (by rw [add_sub_cancel_left]; exact hY s hs),
      Finset.sum_const, hYq, nsmul_eq_mul]
  rw [sum_eq_sum_of_ball_representatives v hconst' hX₁ hX₁' hZ hZ', hZsum,
    Finset.sum_congr rfl fun r _ => hinner r, ← Finset.mul_sum, zpow_add_one₀ hq, mul_inv, mul_assoc,
    inv_mul_cancel_left₀ hq]

theorem inv_zpow_mul_sum_eq_of_le {φ : v.adicCompletion ℚ → ℂ} {k m : ℤ} (hkm : k ≤ m)
    (hconst : ∀ x y, Valued.v (x - y) ≤ WithZero.exp (-m) → φ x = φ y)
    {X : Finset (v.adicCompletion ℚ)} (hX : ∀ r ∈ X, Valued.v r ≤ WithZero.exp (-k))
    (hX' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-k) →
      ∃! r, r ∈ X ∧ Valued.v (x - r) ≤ WithZero.exp (-m)) (j : ℕ) {m' : ℤ} (hm' : m' = m + j)
    {X' : Finset (v.adicCompletion ℚ)} (hY : ∀ r ∈ X', Valued.v r ≤ WithZero.exp (-k))
    (hY' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-k) →
      ∃! r, r ∈ X' ∧ Valued.v (x - r) ≤ WithZero.exp (-m')) :
    ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℂ) ^ m')⁻¹ * ∑ r ∈ X', φ r =
      ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℂ) ^ m)⁻¹ * ∑ r ∈ X, φ r := by
  induction j generalizing m' X' with
  | zero =>
    obtain rfl : m' = m := by simpa using hm'
    rw [sum_eq_sum_of_ball_representatives v hconst hY hY' hX hX']
  | succ j ih =>
    obtain ⟨X₁, hX₁, hX₁', -⟩ := exists_finset_ball_representatives v k (m + j) (by omega)
    have hconst₁ : ∀ x y, Valued.v (x - y) ≤ WithZero.exp (-(m + j)) → φ x = φ y :=
      fun x y hxy => hconst x y (hxy.trans (WithZero.exp_le_exp.mpr (by omega)))
    rw [inv_zpow_mul_sum_eq_of_eq_add_one v (by omega : k ≤ m + j) hconst₁ hX₁ hX₁' (by omega) hY hY',
      ih (m' := m + (j : ℤ)) (X' := X₁) rfl hX₁ hX₁']

theorem sum_eq_sum_of_ball_representatives_of_le {φ : v.adicCompletion ℚ → ℂ} {k k' m : ℤ}
    (hk'k : k' ≤ k) (hkm : k ≤ m) (hsupp : ∀ x, φ x ≠ 0 → Valued.v x ≤ WithZero.exp (-k))
    (hconst : ∀ x y, Valued.v (x - y) ≤ WithZero.exp (-m) → φ x = φ y)
    {X : Finset (v.adicCompletion ℚ)} (hX : ∀ r ∈ X, Valued.v r ≤ WithZero.exp (-k))
    (hX' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-k) →
      ∃! r, r ∈ X ∧ Valued.v (x - r) ≤ WithZero.exp (-m))
    {X' : Finset (v.adicCompletion ℚ)}
    (hY' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-k') →
      ∃! r, r ∈ X' ∧ Valued.v (x - r) ≤ WithZero.exp (-m)) :
    ∑ r ∈ X', φ r = ∑ r ∈ X, φ r := by
  have hkk' : WithZero.exp (-k) ≤ WithZero.exp (-k') := WithZero.exp_le_exp.mpr (by omega)
  have hmk : WithZero.exp (-m) ≤ WithZero.exp (-k) := WithZero.exp_le_exp.mpr (by omega)
  rw [← Finset.sum_filter_of_ne (s := X') (p := fun r => Valued.v r ≤ WithZero.exp (-k))
    fun r _ hr => hsupp r hr]
  refine sum_eq_sum_of_ball_representatives v hconst (fun r hr => (Finset.mem_filter.mp hr).2) ?_ hX hX'
  intro x hx
  obtain ⟨r, ⟨hr, hxr⟩, huniq⟩ := hY' x (hx.trans hkk')
  have hrk : Valued.v r ≤ WithZero.exp (-k) := by
    rw [show r = x - (x - r) by ring]
    exact (Valuation.map_sub _ _ _).trans (max_le hx (hxr.trans hmk))
  exact ⟨r, ⟨Finset.mem_filter.mpr ⟨hr, hrk⟩, hxr⟩,
    fun r' hr' => huniq r' ⟨(Finset.mem_filter.mp hr'.1).1, hr'.2⟩⟩

theorem inv_zpow_mul_sum_eq {φ : v.adicCompletion ℚ → ℂ} {k m : ℤ} (hkm : k ≤ m)
    (hsupp : ∀ x, φ x ≠ 0 → Valued.v x ≤ WithZero.exp (-k))
    (hconst : ∀ x y, Valued.v (x - y) ≤ WithZero.exp (-m) → φ x = φ y)
    {X : Finset (v.adicCompletion ℚ)} (hX : ∀ r ∈ X, Valued.v r ≤ WithZero.exp (-k))
    (hX' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-k) →
      ∃! r, r ∈ X ∧ Valued.v (x - r) ≤ WithZero.exp (-m))
    {k' m' : ℤ} (hk'm' : k' ≤ m') (hsupp' : ∀ x, φ x ≠ 0 → Valued.v x ≤ WithZero.exp (-k'))
    (hconst' : ∀ x y, Valued.v (x - y) ≤ WithZero.exp (-m') → φ x = φ y)
    {X' : Finset (v.adicCompletion ℚ)} (hY : ∀ r ∈ X', Valued.v r ≤ WithZero.exp (-k'))
    (hY' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-k') →
      ∃! r, r ∈ X' ∧ Valued.v (x - r) ≤ WithZero.exp (-m')) :
    ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℂ) ^ m)⁻¹ * ∑ r ∈ X, φ r =
      ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℂ) ^ m')⁻¹ * ∑ r ∈ X', φ r := by
  obtain ⟨X₁, hX₁, hX₁', -⟩ := exists_finset_ball_representatives v (min k k') m (by omega)
  obtain ⟨X₁', hY₁, hY₁', -⟩ := exists_finset_ball_representatives v (min k k') m' (by omega)
  obtain ⟨X₂, hX₂, hX₂', -⟩ := exists_finset_ball_representatives v (min k k') (max m m') (by omega)
  have h1 : ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℂ) ^ m)⁻¹ * ∑ r ∈ X, φ r =
      ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℂ) ^ max m m')⁻¹ * ∑ r ∈ X₂, φ r := by
    rw [← sum_eq_sum_of_ball_representatives_of_le v (min_le_left k k') hkm hsupp hconst hX hX' hX₁']
    exact (inv_zpow_mul_sum_eq_of_le v (by omega : min k k' ≤ m) hconst hX₁ hX₁' (max m m' - m).toNat
      (by rw [Int.toNat_of_nonneg (by omega)]; ring) hX₂ hX₂').symm
  have h2 : ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℂ) ^ m')⁻¹ * ∑ r ∈ X', φ r =
      ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℂ) ^ max m m')⁻¹ * ∑ r ∈ X₂, φ r := by
    rw [← sum_eq_sum_of_ball_representatives_of_le v (min_le_right k k') hk'm' hsupp' hconst' hY hY' hY₁']
    exact (inv_zpow_mul_sum_eq_of_le v (by omega : min k k' ≤ m') hconst' hY₁ hY₁' (max m m' - m').toNat
      (by rw [Int.toNat_of_nonneg (by omega)]; ring) hX₂ hX₂').symm
  rw [h1, h2]

theorem exists_ball_data (φ : ↥(stepFunctions v)) :
    ∃ (k m : ℤ) (X : Finset (v.adicCompletion ℚ)), k ≤ m ∧
      (∀ x, (φ : v.adicCompletion ℚ → ℂ) x ≠ 0 → Valued.v x ≤ WithZero.exp (-k)) ∧
      (∀ x y, Valued.v (x - y) ≤ WithZero.exp (-m) →
        (φ : v.adicCompletion ℚ → ℂ) x = (φ : v.adicCompletion ℚ → ℂ) y) ∧
      (∀ r ∈ X, Valued.v r ≤ WithZero.exp (-k)) ∧
      ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-k) →
        ∃! r, r ∈ X ∧ Valued.v (x - r) ≤ WithZero.exp (-m) := by
  obtain ⟨k₀, m₀, hsupp, hconst⟩ := exists_level_of_mem_stepFunctions v φ.2
  obtain ⟨X, hX, hX', -⟩ := exists_finset_ball_representatives v (-m₀) (max k₀ (-m₀)) (le_max_right _ _)
  refine ⟨-m₀, max k₀ (-m₀), X, le_max_right _ _, fun x hx => ?_, fun x y hxy => ?_, hX, hX'⟩
  · rw [neg_neg]
    exact hsupp x hx
  · exact hconst x y (hxy.trans (WithZero.exp_le_exp.mpr (by omega)))

def IsCountingFunctional (Λ : ↥(stepFunctions v) →ₗ[ℂ] ℂ) : Prop :=
  ∀ (y : v.adicCompletion ℚ) (k : ℤ),
    Λ ⟨ballIndicator v y k, ballIndicator_mem_stepFunctions v y k⟩ =
      ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℂ) ^ k)⁻¹

theorem exists_isCountingFunctional : ∃ Λ, IsCountingFunctional v Λ := by
  choose k m X hkm hsupp hconst hX hX' using exists_ball_data v

  have key : ∀ (φ : ↥(stepFunctions v)) {k' m' : ℤ}, k' ≤ m' →
      (∀ x, (φ : v.adicCompletion ℚ → ℂ) x ≠ 0 → Valued.v x ≤ WithZero.exp (-k')) →
      (∀ x y, Valued.v (x - y) ≤ WithZero.exp (-m') →
        (φ : v.adicCompletion ℚ → ℂ) x = (φ : v.adicCompletion ℚ → ℂ) y) →
      ∀ {X' : Finset (v.adicCompletion ℚ)}, (∀ r ∈ X', Valued.v r ≤ WithZero.exp (-k')) →
      (∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-k') →
        ∃! r, r ∈ X' ∧ Valued.v (x - r) ≤ WithZero.exp (-m')) →
      ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℂ) ^ m φ)⁻¹ * ∑ r ∈ X φ, (φ : v.adicCompletion ℚ → ℂ) r =
        ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℂ) ^ m')⁻¹ * ∑ r ∈ X', (φ : v.adicCompletion ℚ → ℂ) r :=
    by
      intro φ k' m' hk'm' hsupp' hconst' X' hY hY'
      exact inv_zpow_mul_sum_eq v (hkm φ) (hsupp φ) (hconst φ) (hX φ) (hX' φ) hk'm' hsupp' hconst' hY hY'
  refine ⟨{ toFun := fun φ =>
              ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℂ) ^ m φ)⁻¹ * ∑ r ∈ X φ, (φ : v.adicCompletion ℚ → ℂ) r
            map_add' := ?_
            map_smul' := ?_ }, ?_⟩
  · intro φ ψ
    show ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℂ) ^ m (φ + ψ))⁻¹ *
          ∑ r ∈ X (φ + ψ), ((φ + ψ : ↥(stepFunctions v)) : v.adicCompletion ℚ → ℂ) r =
        ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℂ) ^ m φ)⁻¹ * ∑ r ∈ X φ, (φ : v.adicCompletion ℚ → ℂ) r +
          ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℂ) ^ m ψ)⁻¹ * ∑ r ∈ X ψ, (ψ : v.adicCompletion ℚ → ℂ) r
    have hkφ := hkm φ
    have hkψ := hkm ψ
    obtain ⟨Z, hZ, hZ', -⟩ :=
      exists_finset_ball_representatives v (min (k φ) (k ψ)) (max (m φ) (m ψ)) (by omega)
    have hsφ : ∀ x, (φ : v.adicCompletion ℚ → ℂ) x ≠ 0 →
        Valued.v x ≤ WithZero.exp (-min (k φ) (k ψ)) :=
      fun x hx => (hsupp φ x hx).trans (WithZero.exp_le_exp.mpr (by omega))
    have hsψ : ∀ x, (ψ : v.adicCompletion ℚ → ℂ) x ≠ 0 →
        Valued.v x ≤ WithZero.exp (-min (k φ) (k ψ)) :=
      fun x hx => (hsupp ψ x hx).trans (WithZero.exp_le_exp.mpr (by omega))
    have hcφ : ∀ x y, Valued.v (x - y) ≤ WithZero.exp (-max (m φ) (m ψ)) →
        (φ : v.adicCompletion ℚ → ℂ) x = (φ : v.adicCompletion ℚ → ℂ) y :=
      fun x y hxy => hconst φ x y (hxy.trans (WithZero.exp_le_exp.mpr (by omega)))
    have hcψ : ∀ x y, Valued.v (x - y) ≤ WithZero.exp (-max (m φ) (m ψ)) →
        (ψ : v.adicCompletion ℚ → ℂ) x = (ψ : v.adicCompletion ℚ → ℂ) y :=
      fun x y hxy => hconst ψ x y (hxy.trans (WithZero.exp_le_exp.mpr (by omega)))
    have hsadd : ∀ x, ((φ + ψ : ↥(stepFunctions v)) : v.adicCompletion ℚ → ℂ) x ≠ 0 →
        Valued.v x ≤ WithZero.exp (-min (k φ) (k ψ)) := by
      intro x hx
      by_contra hcon
      apply hx
      have h1 : (φ : v.adicCompletion ℚ → ℂ) x = 0 := of_not_not (mt (hsφ x) hcon)
      have h2 : (ψ : v.adicCompletion ℚ → ℂ) x = 0 := of_not_not (mt (hsψ x) hcon)
      rw [Submodule.coe_add, Pi.add_apply, h1, h2, add_zero]
    have hcadd : ∀ x y, Valued.v (x - y) ≤ WithZero.exp (-max (m φ) (m ψ)) →
        ((φ + ψ : ↥(stepFunctions v)) : v.adicCompletion ℚ → ℂ) x =
          ((φ + ψ : ↥(stepFunctions v)) : v.adicCompletion ℚ → ℂ) y := by
      intro x y hxy
      rw [Submodule.coe_add, Pi.add_apply, Pi.add_apply, hcφ x y hxy, hcψ x y hxy]
    rw [key (φ + ψ) (by omega) hsadd hcadd hZ hZ', key φ (by omega) hsφ hcφ hZ hZ',
      key ψ (by omega) hsψ hcψ hZ hZ']
    simp only [Submodule.coe_add, Pi.add_apply, Finset.sum_add_distrib, mul_add]
  · intro c φ
    show ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℂ) ^ m (c • φ))⁻¹ *
          ∑ r ∈ X (c • φ), ((c • φ : ↥(stepFunctions v)) : v.adicCompletion ℚ → ℂ) r =
        (RingHom.id ℂ) c •
          (((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℂ) ^ m φ)⁻¹ * ∑ r ∈ X φ, (φ : v.adicCompletion ℚ → ℂ) r)
    have hs : ∀ x, ((c • φ : ↥(stepFunctions v)) : v.adicCompletion ℚ → ℂ) x ≠ 0 →
        Valued.v x ≤ WithZero.exp (-k φ) := by
      intro x hx
      refine hsupp φ x fun h => hx ?_
      rw [Submodule.coe_smul, Pi.smul_apply, h, smul_zero]
    have hc : ∀ x y, Valued.v (x - y) ≤ WithZero.exp (-m φ) →
        ((c • φ : ↥(stepFunctions v)) : v.adicCompletion ℚ → ℂ) x =
          ((c • φ : ↥(stepFunctions v)) : v.adicCompletion ℚ → ℂ) y := by
      intro x y hxy
      rw [Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, hconst φ x y hxy]
    rw [key (c • φ) (hkm φ) hs hc (hX φ) (hX' φ), RingHom.id_apply, smul_eq_mul]
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    ring
  · intro y j
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    obtain ⟨n, hn⟩ := exists_valued_le_exp v y
    have hk₁ : min (-(n : ℤ)) j ≤ j := min_le_right _ _
    obtain ⟨Z, hZ, hZ', -⟩ := exists_finset_ball_representatives v (min (-(n : ℤ)) j) j hk₁
    have hy : Valued.v y ≤ WithZero.exp (-min (-(n : ℤ)) j) :=
      hn.trans (WithZero.exp_le_exp.mpr (by omega))
    have hsb : ∀ x, ballIndicator v y j x ≠ 0 → Valued.v x ≤ WithZero.exp (-min (-(n : ℤ)) j) := by
      intro x hx
      have h : Valued.v (x - y) ≤ WithZero.exp (-j) := by
        by_contra hcon
        exact hx (by simp only [ballIndicator]; exact if_neg hcon)
      rw [show x = (x - y) + y by ring]
      exact (Valuation.map_add _ _ _).trans
        (max_le (h.trans (WithZero.exp_le_exp.mpr (by omega))) hy)
    have hcb : ∀ x x', Valued.v (x - x') ≤ WithZero.exp (-j) →
        ballIndicator v y j x = ballIndicator v y j x' := by
      intro x x' hxx'
      have hiff : Valued.v (x - y) ≤ WithZero.exp (-j) ↔ Valued.v (x' - y) ≤ WithZero.exp (-j) := by
        constructor
        · intro h
          rw [show x' - y = (x - y) - (x - x') by ring]
          exact (Valuation.map_sub _ _ _).trans (max_le h hxx')
        · intro h
          rw [show x - y = (x' - y) + (x - x') by ring]
          exact (Valuation.map_add _ _ _).trans (max_le h hxx')
      by_cases h : Valued.v (x - y) ≤ WithZero.exp (-j)
      · simp only [ballIndicator, if_pos h, if_pos (hiff.mp h)]
      · simp only [ballIndicator, if_neg h, if_neg (mt hiff.mpr h)]
    have hcount : ∑ r ∈ Z, ballIndicator v y j r = 1 := by
      refine Eq.trans (Finset.sum_congr rfl fun r _ => ?_) (sum_ite_valued_sub_le v hZ' hy (1 : ℂ))
      simp only [ballIndicator]
      rw [Valuation.map_sub_swap]
    refine (key ⟨ballIndicator v y j, ballIndicator_mem_stepFunctions v y j⟩ hk₁ hsb hcb hZ hZ').trans ?_
    show ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℂ) ^ j)⁻¹ * ∑ r ∈ Z, ballIndicator v y j r = _
    rw [hcount, mul_one]

theorem IsCountingFunctional.unique {Λ Λ' : ↥(stepFunctions v) →ₗ[ℂ] ℂ}
    (hΛ : IsCountingFunctional v Λ) (hΛ' : IsCountingFunctional v Λ') : Λ = Λ' := by
  refine LinearMap.ext_on_range (span_ballIndicator_eq_top v) fun p => ?_
  exact (hΛ p.1 p.2).trans (hΛ' p.1 p.2).symm

def countingFunctional : ↥(stepFunctions v) →ₗ[ℂ] ℂ :=
  (exists_isCountingFunctional v).choose

theorem countingFunctional_ballIndicator (y : v.adicCompletion ℚ) (k : ℤ) :
    countingFunctional v ⟨ballIndicator v y k, ballIndicator_mem_stepFunctions v y k⟩ =
      ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℂ) ^ k)⁻¹ :=
  (exists_isCountingFunctional v).choose_spec y k

theorem countingFunctional_ballIndicator_zero_zero :
    countingFunctional v ⟨ballIndicator v 0 0, ballIndicator_mem_stepFunctions v 0 0⟩ = 1 := by
  have h := countingFunctional_ballIndicator v 0 0
  simpa using h

theorem countingFunctional_translate (y : Multiplicative (v.adicCompletion ℚ))
    (φ : ↥(stepFunctions v)) :
    countingFunctional v (translateRepStep v y φ) = countingFunctional v φ := by
  have h : countingFunctional v ∘ₗ translateRepStep v y = countingFunctional v := by
    refine LinearMap.ext_on_range (span_ballIndicator_eq_top v) fun p => ?_
    have hτ : translateRepStep v y ⟨ballIndicator v p.1 p.2, ballIndicator_mem_stepFunctions v p.1 p.2⟩ =
        ⟨ballIndicator v (p.1 - Multiplicative.toAdd y) p.2,
          ballIndicator_mem_stepFunctions v (p.1 - Multiplicative.toAdd y) p.2⟩ :=
      Subtype.ext (translateFn_ballIndicator v (Multiplicative.toAdd y) p.1 p.2)
    show countingFunctional v (translateRepStep v y ⟨ballIndicator v p.1 p.2, _⟩) =
      countingFunctional v ⟨ballIndicator v p.1 p.2, _⟩
    rw [hτ, countingFunctional_ballIndicator, countingFunctional_ballIndicator]
  exact LinearMap.congr_fun h φ

theorem comp_mul_left_mem_stepFunctions {t : v.adicCompletion ℚ} (ht : t ≠ 0)
    {φ : v.adicCompletion ℚ → ℂ} (hφ : φ ∈ stepFunctions v) :
    (fun x => φ (t * x)) ∈ stepFunctions v := by
  obtain ⟨hlc, hcs⟩ := (mem_stepFunctions_iff v φ).mp hφ
  exact (mem_stepFunctions_iff v _).mpr
    ⟨hlc.comp_continuous (continuous_const_mul t), hcs.comp_homeomorph (Homeomorph.mulLeft₀ t ht)⟩

theorem ofReal_norm_eq_of_valued_eq {t : v.adicCompletion ℚ} {a : ℤ}
    (hta : Valued.v t = WithZero.exp (-a)) :
    ((‖t‖ : ℝ) : ℂ) = ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℂ) ^ a)⁻¹ := by
  have h : Multiplicative.toAdd
      (WithZero.unzero (WithZero.exp_ne_zero : (WithZero.exp (-a) : WithZero (Multiplicative ℤ)) ≠ 0)) =
        -a := rfl
  rw [NumberField.FinitePlace.norm_def, hta, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, h,
    natCard_quot_eq_absNorm]
  simp

theorem ballIndicator_comp_mul_left {t : v.adicCompletion ℚ} (ht : t ≠ 0) {a : ℤ}
    (hta : Valued.v t = WithZero.exp (-a)) (y : v.adicCompletion ℚ) (k : ℤ) :
    (fun x => ballIndicator v y k (t * x)) = ballIndicator v (t⁻¹ * y) (k - a) := by
  funext x
  have hiff : Valued.v (t * x - y) ≤ WithZero.exp (-k) ↔
      Valued.v (x - t⁻¹ * y) ≤ WithZero.exp (-(k - a)) := by
    rw [show t * x - y = t * (x - t⁻¹ * y) by rw [mul_sub, mul_inv_cancel_left₀ ht]]
    have h := valued_mul_le_exp_iff v hta (x - t⁻¹ * y) (k - a)
    rwa [sub_add_cancel] at h
  by_cases h : Valued.v (t * x - y) ≤ WithZero.exp (-k)
  · simp only [ballIndicator, if_pos h, if_pos (hiff.mp h)]
  · simp only [ballIndicator, if_neg h, if_neg (mt hiff.mpr h)]

theorem countingFunctional_comp_mul_left {t : v.adicCompletion ℚ} (ht : t ≠ 0)
    {φ : v.adicCompletion ℚ → ℂ} (hφ : φ ∈ stepFunctions v) :
    countingFunctional v ⟨fun x => φ (t * x), comp_mul_left_mem_stepFunctions v ht hφ⟩ =
      ((‖t‖ : ℂ))⁻¹ * countingFunctional v ⟨φ, hφ⟩ := by
  have ht' : Valued.v t ≠ 0 := (Valuation.ne_zero_iff _).mpr ht
  obtain ⟨a, hta⟩ : ∃ a : ℤ, Valued.v t = WithZero.exp (-a) :=
    ⟨-WithZero.log (Valued.v t), by rw [neg_neg, WithZero.exp_log ht']⟩
  have hq := natCast_natCard_quot_ne_zero v
  rw [ofReal_norm_eq_of_valued_eq v hta, inv_inv]

  let D : ↥(stepFunctions v) → ↥(stepFunctions v) := fun ψ =>
    ⟨fun x => (ψ : v.adicCompletion ℚ → ℂ) (t * x), comp_mul_left_mem_stepFunctions v ht ψ.2⟩
  suffices H : ∀ ψ : ↥(stepFunctions v),
      countingFunctional v (D ψ) = (Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℂ) ^ a * countingFunctional v ψ from
    H ⟨φ, hφ⟩
  intro ψ
  have hψ : ψ ∈ Submodule.span ℂ (Set.range fun p : v.adicCompletion ℚ × ℤ =>
      (⟨ballIndicator v p.1 p.2, ballIndicator_mem_stepFunctions v p.1 p.2⟩ : ↥(stepFunctions v))) := by
    rw [span_ballIndicator_eq_top v]
    exact Submodule.mem_top
  induction hψ using Submodule.span_induction with
  | mem ψ hψ =>
    obtain ⟨⟨y, k⟩, rfl⟩ := hψ
    have hD : D ⟨ballIndicator v y k, ballIndicator_mem_stepFunctions v y k⟩ =
        ⟨ballIndicator v (t⁻¹ * y) (k - a), ballIndicator_mem_stepFunctions v (t⁻¹ * y) (k - a)⟩ :=
      Subtype.ext (ballIndicator_comp_mul_left v ht hta y k)
    show countingFunctional v (D ⟨ballIndicator v y k, ballIndicator_mem_stepFunctions v y k⟩) =
      (Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℂ) ^ a *
        countingFunctional v ⟨ballIndicator v y k, ballIndicator_mem_stepFunctions v y k⟩
    rw [hD, countingFunctional_ballIndicator, countingFunctional_ballIndicator, zpow_sub₀ hq, inv_div,
      div_eq_mul_inv]
  | zero =>
    have hD : D 0 = 0 := Subtype.ext (funext fun x => by simp [D])
    rw [hD, map_zero, mul_zero]
  | add ψ₁ ψ₂ _ _ ih₁ ih₂ =>
    have hD : D (ψ₁ + ψ₂) = D ψ₁ + D ψ₂ := Subtype.ext (funext fun x => by simp [D])
    rw [hD, map_add, map_add, ih₁, ih₂, mul_add]
  | smul c ψ _ ih =>
    have hD : D (c • ψ) = c • D ψ := Subtype.ext (funext fun x => by simp [D])
    rw [hD, map_smul, map_smul, ih, smul_eq_mul, smul_eq_mul]
    ring

end AdditiveJacquet

end LanglandsTunnell.CubicInduction

end


