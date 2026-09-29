-- Prove2me | Definitions.Def_NumberField_IntegralAdelicTrace
-- name    : NumberField_IntegralAdelicTrace
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/56b5d7b1-90a2-5a5b-b3b7-0d194e2ba483
-- title:
--   The integral adelic trace on the finite integral adeles
-- statement:
--   The standing context is a number field $F$, and the ambient object is the full product $\widehat{\mathcal O}_F=\prod_{v}\mathcal O_{F,v}$ over the height-one primes $v$ of $\mathcal O_F$ of the valuation rings `v.adicCompletionIntegers F`, with the product topology. For $N\in\mathbb N$, `valBox F N` is the set of $z$ with $|z_v|_v\le|N|_v$ at every $v$, the valuations being those of the completions and $N$ read through $\mathbb N\to\mathcal O_F\to F_v$; this is the level-$N$ box $N\widehat{\mathcal O}_F$ presented by valuation inequalities rather than as an ideal. Accompanying lemmas show it contains $0$ and is stable under addition and negation, is closed, is antitone in divisibility ($M\mid N$ gives `valBox F N ⊆ valBox F M`), is a neighbourhood of $0$ when $N\neq0$, has intersection over all $N\neq0$ equal to $\{0\}$, and that every neighbourhood of $0$ contains some box with $N\neq0$; further, $\operatorname{diag}(a)\in$ `valBox F N` forces $N\mid a$ in $\mathcal O_F$, whence $N\mid\operatorname{Tr}_{\mathcal O_F/\mathbb Z}(a)-\operatorname{Tr}_{\mathcal O_F/\mathbb Z}(b)$ when $a-b$ is so divisible adelically, and every $z$ is congruent to some $a\in\mathcal O_F$ modulo `valBox F N`.
--
--   For a number field $K$, `diag K` is the ring homomorphism $\mathcal O_K\to\widehat{\mathcal O}_K$ with all components the structure maps $\mathcal O_K\to\mathcal O_{K,v}$; it is shown injective and of dense range. `traceDiag F` is the additive map $\mathcal O_F\to\widehat{\mathcal O}_{\mathbb Q}$ obtained by composing $\operatorname{Tr}_{\mathcal O_F/\mathbb Z}$, the map $\mathbb Z\to\mathcal O_{\mathbb Q}$ and $\operatorname{diag}_{\mathbb Q}$. The main definition `traceInt F` is the additive monoid homomorphism $\widehat{\mathcal O}_F\to\widehat{\mathcal O}_{\mathbb Q}$ obtained by extending, along the dense inclusion of the subgroup $\operatorname{diag}(\mathcal O_F)$, the map transported from `traceDiag F`; additivity and vanishing at $0$ are part of the definition. It is continuous, satisfies $\operatorname{traceInt}(\operatorname{diag}a)=\operatorname{diag}_{\mathbb Q}(\operatorname{Tr}_{\mathcal O_F/\mathbb Z}a)$, and is the unique continuous additive map with that property.
--
--   **Relation to Mathlib.** Mathlib supplies the adic completions and their valuation rings, the finite adele ring as a restricted product, and `Algebra.trace`; the boxes $N\widehat{\mathcal O}_F$ and the trace map $\widehat{\mathcal O}_F\to\widehat{\mathcal O}_{\mathbb Q}$ are the project's own.
--
--   **Where it is used.** The map constructed here is the finite integral part of the adelic trace $\mathbb A_F\to\mathbb A_{\mathbb Q}$, from which the standard additive character of $\mathbb A_F$ is obtained by composition with the rational one; this character underlies the adelic analysis on the automorphic side of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_NumberField_IntegralAdelicTrace.lean

import Definitions.Def_NumberField_AdelicBox
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.Topology.DenseEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace NumberField.AdelicTrace

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicBox
  Topology Filter Set
open scoped nonZeroDivisors

variable (F : Type) [Field F] [NumberField F]

def valBox (N : ℕ) : Set (Π v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) :=
  {z | ∀ v, Valued.v ((z v : v.adicCompletion F))
    ≤ Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) (N : 𝓞 F))}

variable {F}

theorem mem_valBox {N : ℕ} {z : Π v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F} :
    z ∈ valBox F N ↔ ∀ v, Valued.v ((z v : v.adicCompletion F))
      ≤ Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) (N : 𝓞 F)) := Iff.rfl

theorem algebraMap_adicCompletion_eq (v : HeightOneSpectrum (𝓞 F)) (a : 𝓞 F) :
    algebraMap (𝓞 F) (v.adicCompletion F) a = ((a : F) : v.adicCompletion F) :=
  IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F) a

theorem valued_algebraMap (v : HeightOneSpectrum (𝓞 F)) (a : 𝓞 F) :
    Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) a) = v.intValuation a := by
  rw [algebraMap_adicCompletion_eq, valuedAdicCompletion_eq_valuation', valuation_of_algebraMap]

theorem coe_algebraMap_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 F)) (a : 𝓞 F) :
    ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) a : v.adicCompletion F))
      = algebraMap (𝓞 F) (v.adicCompletion F) a := by
  rw [algebraMap_adicCompletionIntegers_apply, algebraMap_adicCompletion_eq]

theorem algebraMap_adicCompletion_injective (v : HeightOneSpectrum (𝓞 F)) :
    Function.Injective (algebraMap (𝓞 F) (v.adicCompletion F)) := fun a b h => by
  rw [algebraMap_adicCompletion_eq, algebraMap_adicCompletion_eq] at h
  exact RingOfIntegers.coe_injective ((algebraMap F (v.adicCompletion F)).injective h)

theorem natCast_ringOfIntegers_ne_zero {N : ℕ} (hN : N ≠ 0) : (N : 𝓞 F) ≠ 0 :=
  Nat.cast_ne_zero.mpr hN

theorem zero_mem_valBox (N : ℕ) : (0 : Π v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F)
    ∈ valBox F N := fun v => by
  simp only [Pi.zero_apply, ZeroMemClass.coe_zero, map_zero, zero_le']

theorem add_mem_valBox {N : ℕ} {x y : Π v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F}
    (hx : x ∈ valBox F N) (hy : y ∈ valBox F N) : x + y ∈ valBox F N := fun v => by
  simp only [Pi.add_apply, AddMemClass.coe_add]
  exact Valuation.map_add_le _ (hx v) (hy v)

theorem neg_mem_valBox {N : ℕ} {x : Π v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F}
    (hx : x ∈ valBox F N) : -x ∈ valBox F N := fun v => by
  simp only [Pi.neg_apply, NegMemClass.coe_neg, Valuation.map_neg]
  exact hx v

theorem sub_mem_valBox {N : ℕ} {x y : Π v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F}
    (hx : x ∈ valBox F N) (hy : y ∈ valBox F N) : x - y ∈ valBox F N := by
  rw [sub_eq_add_neg]; exact add_mem_valBox hx (neg_mem_valBox hy)

theorem valBox_subset_of_dvd {M N : ℕ} (h : M ∣ N) : valBox F N ⊆ valBox F M := by
  intro z hz v
  obtain ⟨k, rfl⟩ := h
  refine (hz v).trans ?_
  rw [Nat.cast_mul, map_mul, Valuation.map_mul, valued_algebraMap (a := (k : 𝓞 F))]
  exact mul_le_of_le_one_right' (intValuation_le_one v _)

theorem natCast_dvd_of_mem_valBox {N : ℕ} (hN : N ≠ 0) {a : 𝓞 F}
    (h : (fun v : HeightOneSpectrum (𝓞 F) => algebraMap (𝓞 F) (v.adicCompletionIntegers F) a) ∈ valBox F N) :
    (N : 𝓞 F) ∣ a := by
  have hNF : ((N : 𝓞 F) : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr (natCast_ringOfIntegers_ne_zero hN)
  set y : F := (a : F) / ((N : 𝓞 F) : F) with hy
  have hyint : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F y ≤ 1 := fun v => by
    have hv := h v
    rw [coe_algebraMap_adicCompletionIntegers, valued_algebraMap, valued_algebraMap] at hv
    have hN0 : v.intValuation (N : 𝓞 F) ≠ 0 := intValuation_ne_zero v _ (natCast_ringOfIntegers_ne_zero hN)
    rw [hy, map_div₀, valuation_of_algebraMap, valuation_of_algebraMap]
    exact (div_le_one₀ (zero_lt_iff.mpr hN0)).mpr hv
  obtain ⟨c, hc⟩ := mem_integers_of_valuation_le_one F y hyint
  refine ⟨c, RingOfIntegers.coe_injective ?_⟩
  change (a : F) = ((N : 𝓞 F) * c : 𝓞 F)
  rw [RingOfIntegers.coe_eq_algebraMap ((N : 𝓞 F) * c), map_mul, hc, hy,
    ← RingOfIntegers.coe_eq_algebraMap, mul_div_cancel₀ _ hNF]

theorem natCast_dvd_trace_sub {N : ℕ} (hN : N ≠ 0) {a b : 𝓞 F}
    (h : (fun v : HeightOneSpectrum (𝓞 F) => algebraMap (𝓞 F) (v.adicCompletionIntegers F) (a - b)) ∈ valBox F N) :
    (N : ℤ) ∣ Algebra.trace ℤ (𝓞 F) a - Algebra.trace ℤ (𝓞 F) b := by
  obtain ⟨c, hc⟩ := natCast_dvd_of_mem_valBox hN h
  refine ⟨Algebra.trace ℤ (𝓞 F) c, ?_⟩
  rw [← map_sub, hc, show ((N : 𝓞 F) * c : 𝓞 F) = (N : ℤ) • c by rw [zsmul_eq_mul, Int.cast_natCast],
    map_zsmul, smul_eq_mul]

theorem valBox_mem_nhds_zero {N : ℕ} (hN : N ≠ 0) :
    valBox F N ∈ 𝓝 (0 : Π v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) := by

  set S : Set (HeightOneSpectrum (𝓞 F)) := {v | v.asIdeal ∣ Ideal.span {(N : 𝓞 F)}} with hS
  have hSfin : S.Finite := Ideal.finite_factors (by
    intro h0
    rw [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] at h0
    exact natCast_ringOfIntegers_ne_zero hN h0)

  let B : ∀ v : HeightOneSpectrum (𝓞 F), Set (v.adicCompletionIntegers F) := fun v =>
    {x | Valued.v ((x : v.adicCompletion F)) < Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) (N : 𝓞 F))}
  have hB : ∀ v, B v ∈ 𝓝 (0 : v.adicCompletionIntegers F) := fun v => by
    have hN0 : algebraMap (𝓞 F) (v.adicCompletion F) (N : 𝓞 F) ≠ 0 := fun h0 =>
      natCast_ringOfIntegers_ne_zero hN (algebraMap_adicCompletion_injective v (h0.trans (map_zero _).symm))
    have h1 := ball_mem_nhds (𝓞 F) F v (0 : v.adicCompletion F) _ hN0
    simp only [sub_zero] at h1
    have h2 : (fun x : v.adicCompletionIntegers F => (x : v.adicCompletion F)) ⁻¹'
        {z | Valued.v z < Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) (N : 𝓞 F))} ∈
        𝓝 (0 : v.adicCompletionIntegers F) :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds (by simpa using h1)
    exact h2
  refine mem_of_superset (set_pi_mem_nhds hSfin fun v _ => hB v) fun z hz v => ?_
  by_cases hv : v ∈ S
  · exact le_of_lt (hz v hv)
  ·
    have hN1 : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) (N : 𝓞 F)) = 1 := by
      rw [valued_algebraMap]
      refine intValuation_eq_one_iff.mpr fun hmem => hv ?_
      rw [hS, Set.mem_setOf_eq, Ideal.dvd_span_singleton]
      exact hmem
    rw [hN1]
    exact (mem_adicCompletionIntegers _ _ _).mp (z v).2

theorem isClosed_setOf_valued_le (v : HeightOneSpectrum (𝓞 F)) (r : WithZero (Multiplicative ℤ)) :
    IsClosed {y : v.adicCompletion F | Valued.v y ≤ r} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro y hy
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hy
  have hy0 : y ≠ 0 := fun h0 => by rw [h0, map_zero] at hy; exact not_lt_zero' hy
  refine mem_of_superset (ball_mem_nhds (𝓞 F) F v y y hy0) fun z hz => ?_
  simp only [Set.mem_setOf_eq] at hz
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
  have : Valued.v z = Valued.v y := by
    have := Valuation.map_add_eq_of_lt_left (v := (Valued.v : Valuation (v.adicCompletion F) _)) hz
    rwa [add_sub_cancel] at this
  rwa [this]

theorem isClosed_valBox (N : ℕ) : IsClosed (valBox F N) := by
  have : valBox F N = ⋂ v, (fun z : (Π v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) =>
      (z v : v.adicCompletion F)) ⁻¹'
        {y | Valued.v y ≤ Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) (N : 𝓞 F))} := by
    ext z; simp only [valBox, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [this]
  exact isClosed_iInter fun v => (isClosed_setOf_valued_le v _).preimage
    (continuous_subtype_val.comp (continuous_apply v))

theorem eq_zero_of_forall_mem_valBox {z : Π v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F}
    (hz : ∀ N : ℕ, N ≠ 0 → z ∈ valBox F N) : z = 0 := by
  funext v
  apply Subtype.ext
  change (z v : v.adicCompletion F) = 0

  have hle : ∀ n : ℕ, Valued.v (z v : v.adicCompletion F) ≤ WithZero.exp (-(n : ℤ)) := by
    intro n
    have hI : (v.asIdeal ^ n : Ideal (𝓞 F)) ≠ ⊥ := pow_ne_zero _ v.ne_bot
    set N : ℕ := Ideal.absNorm (v.asIdeal ^ n : Ideal (𝓞 F)) with hN
    have hN0 : N ≠ 0 := by
      rw [hN, Ne, Ideal.absNorm_eq_zero_iff]; exact hI
    have hNmem : (N : 𝓞 F) ∈ v.asIdeal ^ n := by rw [hN]; exact Ideal.absNorm_mem _
    refine (hz N hN0 v).trans ?_
    rw [valued_algebraMap]
    exact (intValuation_le_pow_iff_mem v _ n).mpr hNmem
  by_contra hne
  have hne' : Valued.v (z v : v.adicCompletion F) ≠ 0 := (Valuation.ne_zero_iff _).mpr hne
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v (z v : v.adicCompletion F) = WithZero.exp m :=
    ⟨WithZero.log (Valued.v (z v : v.adicCompletion F)), (WithZero.exp_log hne').symm⟩
  have := hle ((-m).toNat + 1)
  rw [hm, WithZero.exp_le_exp] at this
  omega

theorem exists_valBox_subset {U : Set (Π v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F)}
    (hU : U ∈ 𝓝 (0 : Π v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F)) :
    ∃ N : ℕ, N ≠ 0 ∧ valBox F N ⊆ U := by
  haveI : Nonempty {N : ℕ // N ≠ 0} := ⟨⟨1, one_ne_zero⟩⟩
  have hdir : Directed (· ⊇ ·) (fun N : {N : ℕ // N ≠ 0} => valBox F N.1) := by
    rintro ⟨M, hM⟩ ⟨N, hN⟩
    exact ⟨⟨M * N, mul_ne_zero hM hN⟩, valBox_subset_of_dvd (Dvd.intro _ rfl),
      valBox_subset_of_dvd (Dvd.intro_left _ rfl)⟩
  obtain ⟨⟨N, hN⟩, h⟩ := exists_subset_nhds_of_isCompact' hdir
    (fun N => (isClosed_valBox N.1).isCompact) (fun N => isClosed_valBox N.1) (U := U)
    (fun x hx => by
      have hx0 : x = 0 := eq_zero_of_forall_mem_valBox fun N hN => Set.mem_iInter.mp hx ⟨N, hN⟩
      rwa [hx0])
  exact ⟨N, hN, h⟩

theorem exists_sub_algebraMap_mem_valBox (z : Π v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F)
    {N : ℕ} (hN : N ≠ 0) :
    ∃ a : 𝓞 F, (z - fun v : HeightOneSpectrum (𝓞 F) => algebraMap (𝓞 F) (v.adicCompletionIntegers F) a)
      ∈ valBox F N := by
  let x : FiniteAdeleRing (𝓞 F) F :=
    RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite z
  have hx : ∀ v, x v = (z v : v.adicCompletion F) := fun v => rfl
  have hxint : x ∈ integralFiniteAdeles (𝓞 F) F := fun v => by rw [hx]; exact (z v).2
  obtain ⟨a, ha⟩ := exists_forall_valued_sub_le (𝓞 F) F hxint (natCast_ringOfIntegers_ne_zero hN)
  refine ⟨a, fun v => ?_⟩
  have h := ha v
  rw [hx, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h
  simpa only [Pi.sub_apply, AddSubgroupClass.coe_sub, coe_algebraMap_adicCompletionIntegers] using h

noncomputable section

section Extension

open Topology Filter

variable (K : Type) [Field K] [NumberField K]

def diag : 𝓞 K →+* (Π v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K) :=
  RingHom.pi fun v => algebraMap (𝓞 K) (v.adicCompletionIntegers K)

@[simp] theorem diag_apply (a : 𝓞 K) (v : HeightOneSpectrum (𝓞 K)) :
    diag K a v = algebraMap (𝓞 K) (v.adicCompletionIntegers K) a := rfl

theorem diag_eq (a : 𝓞 K) :
    diag K a = fun v : HeightOneSpectrum (𝓞 K) => algebraMap (𝓞 K) (v.adicCompletionIntegers K) a := rfl

theorem nonempty_heightOneSpectrum : Nonempty (HeightOneSpectrum (𝓞 K)) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 K)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField K)⟩⟩

theorem diag_injective : Function.Injective (diag K) := by
  intro a b hab
  obtain ⟨v⟩ := nonempty_heightOneSpectrum K
  exact algebraMap_adicCompletion_injective v (by
    have h := congrFun hab v
    simp only [diag_apply] at h
    have := congrArg (fun x : v.adicCompletionIntegers K => (x : v.adicCompletion K)) h
    simpa [coe_algebraMap_adicCompletionIntegers] using this)

theorem diag_mem_valBox_of_dvd {N : ℕ} {a : 𝓞 K} (h : (N : 𝓞 K) ∣ a) : diag K a ∈ valBox K N := by
  obtain ⟨c, rfl⟩ := h
  intro v
  simp only [diag_apply, map_mul]
  change Valued.v (((algebraMap (𝓞 K) (v.adicCompletionIntegers K) (N : 𝓞 K) : v.adicCompletion K))
    * ((algebraMap (𝓞 K) (v.adicCompletionIntegers K) c : v.adicCompletion K))) ≤ _
  rw [map_mul]
  have hc : Valued.v ((algebraMap (𝓞 K) (v.adicCompletionIntegers K) c : v.adicCompletion K)) ≤ 1 :=
    (algebraMap (𝓞 K) (v.adicCompletionIntegers K) c).2
  calc _ ≤ Valued.v ((algebraMap (𝓞 K) (v.adicCompletionIntegers K) (N : 𝓞 K) : v.adicCompletion K)) * 1 :=
        mul_le_mul' le_rfl hc
    _ = _ := by rw [mul_one]; rfl

theorem denseRange_diag : DenseRange (diag K) := by
  intro z
  rw [mem_closure_iff_nhds]
  intro U hU
  have hU0 : (fun y => y + z) ⁻¹' U ∈ 𝓝 (0 : Π v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K) := by
    have : Continuous fun y : (Π v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K) => y + z :=
      continuous_id.add continuous_const
    exact this.continuousAt.preimage_mem_nhds (by simpa using hU)
  obtain ⟨N, hN, hsub⟩ := exists_valBox_subset hU0
  obtain ⟨a, ha⟩ := exists_sub_algebraMap_mem_valBox z hN
  refine ⟨diag K a, ?_, ⟨a, rfl⟩⟩
  have hmem : diag K a - z ∈ valBox K N := by
    have := neg_mem_valBox ha
    simpa [diag_eq] using this
  have := hsub hmem
  simpa using this

end Extension

section Trace

open Topology Filter

variable (F : Type) [Field F] [NumberField F]

def traceDiag : 𝓞 F →+ (Π w : HeightOneSpectrum (𝓞 ℚ), w.adicCompletionIntegers ℚ) :=
  (diag ℚ).toAddMonoidHom.comp
    ((algebraMap ℤ (𝓞 ℚ)).toAddMonoidHom.comp (Algebra.trace ℤ (𝓞 F)).toAddMonoidHom)

@[simp] theorem traceDiag_apply (a : 𝓞 F) :
    traceDiag F a = diag ℚ (algebraMap ℤ (𝓞 ℚ) (Algebra.trace ℤ (𝓞 F) a)) := rfl

theorem traceDiag_sub_mem_valBox {N : ℕ} (hN : N ≠ 0) {a b : 𝓞 F}
    (h : diag F (a - b) ∈ valBox F N) : traceDiag F a - traceDiag F b ∈ valBox ℚ N := by
  rw [← map_sub, traceDiag_apply]
  apply diag_mem_valBox_of_dvd
  obtain ⟨t, ht⟩ := natCast_dvd_trace_sub hN h
  refine ⟨algebraMap ℤ (𝓞 ℚ) t, ?_⟩
  rw [LinearMap.map_sub, ht, map_mul]
  congr 1

private def S : AddSubgroup (Π v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) :=
  (diag F).toAddMonoidHom.range

private theorem dense_S :
    Dense ((S F : AddSubgroup (Π v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F)) :
      Set (Π v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F)) := by
  have : ((S F : AddSubgroup _) : Set (Π v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F))
      = Set.range (diag F) := by
    ext x; simp [S]
  rw [this]
  exact denseRange_diag F

private def eS : 𝓞 F ≃+ S F := AddMonoidHom.ofInjective (f := (diag F).toAddMonoidHom) (diag_injective F)

private theorem eS_apply_coe (a : 𝓞 F) :
    ((eS F a : S F) : Π v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) = diag F a := rfl

private def f₀ : S F →+ (Π w : HeightOneSpectrum (𝓞 ℚ), w.adicCompletionIntegers ℚ) :=
  (traceDiag F).comp (eS F).symm.toAddMonoidHom

private theorem f₀_eS (a : 𝓞 F) : f₀ F (eS F a) = traceDiag F a := by
  simp [f₀]

private theorem continuous_f₀ : Continuous (f₀ F) := by
  apply continuous_of_continuousAt_zero
  rw [ContinuousAt, map_zero]
  intro U hU
  obtain ⟨N, hN, hsub⟩ := exists_valBox_subset hU
  have hV : (Subtype.val ⁻¹' valBox F N : Set (S F)) ∈ 𝓝 (0 : S F) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds (by simpa using valBox_mem_nhds_zero (F := F) hN)
  refine Filter.mem_map.mpr (Filter.mem_of_superset hV fun s hs => hsub ?_)
  obtain ⟨a, rfl⟩ := (eS F).surjective s
  show f₀ F (eS F a) ∈ valBox ℚ N
  rw [f₀_eS]
  have : diag F (a - 0) ∈ valBox F N := by simpa [eS_apply_coe] using hs
  simpa using traceDiag_sub_mem_valBox F hN this

private theorem uniformContinuous_f₀ : UniformContinuous (f₀ F) :=
  uniformContinuous_addMonoidHom_of_continuous (continuous_f₀ F)

private theorem di : IsDenseInducing
    (Subtype.val : S F → Π v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) :=
  (dense_S F).isDenseInducing_val

private theorem tendsto_f₀ (b : Π v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) :
    ∃ c, Tendsto (f₀ F) (comap Subtype.val (𝓝 b)) (𝓝 c) :=
  uniformly_extend_exists isUniformEmbedding_subtype_val.isUniformInducing (dense_S F).denseRange_val
    (uniformContinuous_f₀ F) b

def traceInt : (Π v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F)
    →+ (Π w : HeightOneSpectrum (𝓞 ℚ), w.adicCompletionIntegers ℚ) where
  toFun := (di F).extend (f₀ F)
  map_zero' := by
    have := (di F).extend_eq (continuous_f₀ F) (0 : S F)
    simpa using this
  map_add' := by
    have hc : Continuous ((di F).extend (f₀ F)) := (di F).continuous_extend (tendsto_f₀ F)
    intro x y
    refine DenseRange.induction_on₂ (p := fun x y => (di F).extend (f₀ F) (x + y)
        = (di F).extend (f₀ F) x + (di F).extend (f₀ F) y) (dense_S F).denseRange_val ?_ ?_ x y
    · exact isClosed_eq (hc.comp (continuous_fst.add continuous_snd))
        ((hc.comp continuous_fst).add (hc.comp continuous_snd))
    · intro s t
      rw [← AddSubgroup.coe_add, (di F).extend_eq (continuous_f₀ F), (di F).extend_eq (continuous_f₀ F),
        (di F).extend_eq (continuous_f₀ F), map_add]

theorem continuous_traceInt : Continuous (traceInt F) :=
  (di F).continuous_extend (tendsto_f₀ F)

theorem traceInt_diag (a : 𝓞 F) :
    traceInt F (diag F a)
      = fun w : HeightOneSpectrum (𝓞 ℚ) =>
          algebraMap (𝓞 ℚ) (w.adicCompletionIntegers ℚ) (algebraMap ℤ (𝓞 ℚ) (Algebra.trace ℤ (𝓞 F) a)) := by
  show (di F).extend (f₀ F) ((eS F a : S F) : Π v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) = _
  rw [(di F).extend_eq (continuous_f₀ F), f₀_eS]
  rfl

theorem eq_traceInt {T : (Π v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F)
      →+ (Π w : HeightOneSpectrum (𝓞 ℚ), w.adicCompletionIntegers ℚ)}
    (hT : Continuous T)
    (h : ∀ a : 𝓞 F, T (diag F a) = traceInt F (diag F a)) : T = traceInt F := by
  refine AddMonoidHom.ext fun x => ?_
  exact DenseRange.induction_on (denseRange_diag F) x (isClosed_eq hT (continuous_traceInt F)) h

theorem existsUnique_traceInt :
    ∃! T : (Π v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F)
        →+ (Π w : HeightOneSpectrum (𝓞 ℚ), w.adicCompletionIntegers ℚ),
      Continuous T ∧ ∀ a : 𝓞 F,
        T (fun v => algebraMap (𝓞 F) (v.adicCompletionIntegers F) a)
          = fun w : HeightOneSpectrum (𝓞 ℚ) => algebraMap (𝓞 ℚ) (w.adicCompletionIntegers ℚ)
              (algebraMap ℤ (𝓞 ℚ) (Algebra.trace ℤ (𝓞 F) a)) := by
  refine ⟨traceInt F, ⟨continuous_traceInt F, fun a => traceInt_diag F a⟩, ?_⟩
  rintro T ⟨hT, hTa⟩
  exact eq_traceInt F hT fun a => (hTa a).trans (traceInt_diag F a).symm

end Trace

end

end NumberField.AdelicTrace


