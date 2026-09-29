-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.comap_maximalIdeal_eq_span_and_residue_eq_and_ord_eq_one_of_reads_of_constants
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/bfc0b35b-d904-5884-b311-2e1e47e2ac69

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_comap_maximalIdeal_eq_span_and_residue_eq_and_ord_eq_one_of_reads_of_constants

set_option autoImplicit false

open IsLocalRing AlgebraicCurve

namespace E149P4

open IsLocalRing

theorem exists_eq_pow_mul_add {S : Type*} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (ϖ t : S) (hmax : maximalIdeal S = Ideal.span {ϖ, t})
    (ht : t ∉ Ideal.span {ϖ}) (hdom : IsDomain (S ⧸ Ideal.span {ϖ}))
    (s : S) (hs : s ∉ Ideal.span {ϖ}) :
    ∃ (n : ℕ) (u c : S), IsUnit u ∧ s = t ^ n * u + ϖ * c := by
  classical
  haveI : IsDomain (S ⧸ Ideal.span {ϖ}) := hdom
  have hItop : Ideal.span {ϖ} ≠ (⊤ : Ideal S) := by
    intro h; apply ht; rw [h]; exact Submodule.mem_top
  haveI : Nontrivial (S ⧸ Ideal.span {ϖ}) := Ideal.Quotient.nontrivial_iff.mpr hItop
  have hmk_surj : Function.Surjective (Ideal.Quotient.mk (Ideal.span {ϖ})) := Ideal.Quotient.mk_surjective
  haveI : IsLocalRing (S ⧸ Ideal.span {ϖ}) := IsLocalRing.of_surjective' _ hmk_surj
  haveI : IsNoetherianRing (S ⧸ Ideal.span {ϖ}) :=
    isNoetherianRing_of_surjective S (S ⧸ Ideal.span {ϖ}) _ hmk_surj
  have hImax : Ideal.span {ϖ} ≤ maximalIdeal S := by
    rw [hmax]; exact Ideal.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert ϖ {t}))

  have hmapmax : (maximalIdeal S).map (Ideal.Quotient.mk (Ideal.span {ϖ})) =
      maximalIdeal (S ⧸ Ideal.span {ϖ}) := by
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective _ hmk_surj (IsLocalRing.maximalIdeal.isMaximal S)
      with h | h
    · exfalso
      have hcm := Ideal.comap_map_of_surjective _ hmk_surj (maximalIdeal S)
      rw [h, Ideal.comap_top, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hImax] at hcm
      exact (IsLocalRing.maximalIdeal.isMaximal S).ne_top hcm.symm
    · exact IsLocalRing.eq_maximalIdeal h
  have hϖ0 : Ideal.Quotient.mk (Ideal.span {ϖ}) ϖ = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self ϖ)
  have hmaxD : maximalIdeal (S ⧸ Ideal.span {ϖ}) = Ideal.span {Ideal.Quotient.mk (Ideal.span {ϖ}) t} := by
    rw [← hmapmax, hmax, Ideal.map_span, Set.image_pair, hϖ0, Ideal.span_insert_zero]
  have htne : Ideal.Quotient.mk (Ideal.span {ϖ}) t ≠ 0 := fun h => ht (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hnf : ¬ IsField (S ⧸ Ideal.span {ϖ}) := by
    intro hf
    have h0 := (IsLocalRing.isField_iff_maximalIdeal_eq).mp hf
    rw [hmaxD, Ideal.span_singleton_eq_bot] at h0
    exact htne h0
  haveI : IsDiscreteValuationRing (S ⧸ Ideal.span {ϖ}) :=
    ((IsDiscreteValuationRing.TFAE (S ⧸ Ideal.span {ϖ}) hnf).out 0 4).mpr
      (show (maximalIdeal (S ⧸ Ideal.span {ϖ})).IsPrincipal from ⟨_, hmaxD⟩)
  have hirr : Irreducible (Ideal.Quotient.mk (Ideal.span {ϖ}) t) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hmaxD
  have hs' : Ideal.Quotient.mk (Ideal.span {ϖ}) s ≠ 0 := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.mp h)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hs' hirr
  obtain ⟨v, hv⟩ := hmk_surj ((u⁻¹ : (S ⧸ Ideal.span {ϖ})ˣ) : S ⧸ Ideal.span {ϖ})
  have hvunit : IsUnit v := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hvm
    have hmem : Ideal.Quotient.mk (Ideal.span {ϖ}) v ∈ maximalIdeal (S ⧸ Ideal.span {ϖ}) := by
      rw [← hmapmax]; exact Ideal.mem_map_of_mem _ hvm
    rw [hv] at hmem
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem (Units.isUnit u⁻¹)
  have hdiff : s - t ^ n * v ∈ Ideal.span {ϖ} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_pow, hv, ← hu, mul_assoc,
      Units.mul_inv, mul_one, sub_self]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hdiff
  exact ⟨n, v, c, hvunit, by rw [mul_comm ϖ c, hc]; ring⟩

end E149P4

open E149P4 in

theorem solution
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (S : Subring F) [IsLocalRing ↥S] [IsNoetherianRing ↥S]
    (hSR : ∀ f : ↥S, (f : F) ∈ R.integers)

    {ι : Type*} (cst : ι → ↥A)
    (hκ : Function.Surjective (fun i => IsLocalRing.residue ↥A (cst i)))
    (hAS : ∀ i : ι, algebraMap L F (cst i : L) ∈ S)
    (χ : ↥S →+* ResidueField A)
    (hker : RingHom.ker χ = maximalIdeal ↥S)
    (hχA : ∀ i : ι, χ ⟨algebraMap L F (cst i : L), hAS i⟩ = IsLocalRing.residue ↥A (cst i))

    (ϖS t : ↥S)
    (hmax : maximalIdeal ↥S = Ideal.span {ϖS, t})
    (hϖR : (⟨(ϖS : F), hSR ϖS⟩ : ↥R.integers) ∈ maximalIdeal ↥R.integers)
    (ht : t ∉ Ideal.span {ϖS})
    (hdom : IsDomain (↥S ⧸ Ideal.span {ϖS}))

    (hng : ∃ f : ↥S, f ∈ maximalIdeal ↥S ∧ R.residue ⟨(f : F), hSR f⟩ ≠ 0)

    (hfracbar : ∀ g : Fbar, ∃ a b : ↥S, R.residue ⟨(b : F), hSR b⟩ ≠ 0 ∧
      g * R.residue ⟨(b : F), hSR b⟩ = R.residue ⟨(a : F), hSR a⟩)

    (Q : Place (ResidueField A) Fbar)
    (hreads : ∀ f : ↥S, R.residue ⟨(f : F), hSR f⟩ ∈ Q.toValuationSubring ∧
      (R.residue ⟨(f : F), hSR f⟩ ∈ Q.toValuationSubring.nonunits ↔ f ∈ maximalIdeal ↥S)) :

    (∀ f : ↥S, (⟨(f : F), hSR f⟩ : ↥R.integers) ∈ maximalIdeal ↥R.integers ↔ ϖS ∣ f) ∧

    (∀ f : ↥S, ∃ hm : R.residue ⟨(f : F), hSR f⟩ ∈ Q.toValuationSubring,
      IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : F), hSR f⟩, hm⟩ =
        algebraMap (ResidueField ↥A) Q.ResidueField (χ f)) ∧

    Q.ord (R.residue ⟨(t : F), hSR t⟩) = 1 := by
  classical

  let ιS : ↥S →+* ↥R.integers :=
    { toFun := fun f => ⟨(f : F), hSR f⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  let red : ↥S →+* Fbar := R.residue.comp ιS
  have hred : ∀ f : ↥S, red f = R.residue ⟨(f : F), hSR f⟩ := fun f => rfl
  have hreads' : ∀ f : ↥S, red f ∈ Q.toValuationSubring ∧
      (red f ∈ Q.toValuationSubring.nonunits ↔ f ∈ maximalIdeal ↥S) := hreads
  have hkerR : ∀ f : ↥S, (⟨(f : F), hSR f⟩ : ↥R.integers) ∈ maximalIdeal ↥R.integers ↔ red f = 0 := by
    intro f
    rw [← R.ker_residue, RingHom.mem_ker]
    exact Iff.rfl
  have hϖ0 : red ϖS = 0 := (hkerR ϖS).mp hϖR
  have hdvd0 : ∀ f : ↥S, ϖS ∣ f → red f = 0 := by
    rintro f ⟨c, rfl⟩
    rw [map_mul, hϖ0, zero_mul]
  have htmax : t ∈ maximalIdeal ↥S := by
    rw [hmax]; exact Ideal.subset_span (Set.mem_insert_of_mem ϖS (Set.mem_singleton t))
  have hϖmax : ϖS ∈ maximalIdeal ↥S := by
    rw [hmax]; exact Ideal.subset_span (Set.mem_insert ϖS {t})

  have hunitO : ∀ u : ↥S, IsUnit u → IsUnit (⟨red u, (hreads' u).1⟩ : ↥Q.toValuationSubring) := by
    intro u hu
    rw [← IsLocalRing.notMem_maximalIdeal, ← ValuationSubring.coe_mem_nonunits_iff]
    intro hmem
    exact (IsLocalRing.notMem_maximalIdeal.mpr hu) ((hreads' u).2.mp hmem)
  have hunit0 : ∀ u : ↥S, IsUnit u → red u ≠ 0 := by
    intro u hu h0
    apply (IsLocalRing.notMem_maximalIdeal.mpr hu)
    rw [← (hreads' u).2, h0]
    exact Q.toValuationSubring.nonunits.zero_mem

  have hτO : red t ∈ Q.toValuationSubring := (hreads' t).1
  have hτmax : (⟨red t, hτO⟩ : ↥Q.toValuationSubring) ∈ maximalIdeal ↥Q.toValuationSubring :=
    ValuationSubring.coe_mem_nonunits_iff.mp ((hreads' t).2.mpr htmax)

  have star : ∀ s : ↥S, ¬ ϖS ∣ s → ∃ (n : ℕ) (u c : ↥S), IsUnit u ∧ s = t ^ n * u + ϖS * c := by
    intro s hs
    exact exists_eq_pow_mul_add ϖS t hmax ht hdom s (fun h => hs (Ideal.mem_span_singleton.mp h))
  have star_red : ∀ (s u c : ↥S) (n : ℕ), s = t ^ n * u + ϖS * c → red s = red t ^ n * red u := by
    rintro s u c n rfl
    rw [map_add, map_mul, map_mul, map_pow, hϖ0, zero_mul, add_zero]

  have hτ0 : red t ≠ 0 := by
    obtain ⟨f₀, hf₀m, hf₀⟩ := hng
    have hf₀' : red f₀ ≠ 0 := hf₀
    have hnd : ¬ ϖS ∣ f₀ := fun h => hf₀' (hdvd0 f₀ h)
    obtain ⟨n, u, c, hu, hf⟩ := star f₀ hnd
    intro hτ
    rcases Nat.eq_zero_or_pos n with hn | hn
    · apply (IsLocalRing.notMem_maximalIdeal.mpr hu)
      have : u = f₀ - ϖS * c := by rw [hf, hn, pow_zero, one_mul, add_sub_cancel_right]
      rw [this]
      exact Ideal.sub_mem _ hf₀m (Ideal.mul_mem_right _ _ hϖmax)
    · apply hf₀'
      rw [star_red f₀ u c n hf, hτ, zero_pow (Nat.pos_iff_ne_zero.mp hn), zero_mul]

  have hker_red : ∀ f : ↥S, red f = 0 ↔ ϖS ∣ f := by
    intro f
    refine ⟨fun h0 => ?_, hdvd0 f⟩
    by_contra hnd
    obtain ⟨n, u, c, hu, hf⟩ := star f hnd
    rw [star_red f u c n hf] at h0
    exact (mul_ne_zero (pow_ne_zero n hτ0) (hunit0 u hu)) h0
  have hcen : ∀ f : ↥S, (⟨(f : F), hSR f⟩ : ↥R.integers) ∈ maximalIdeal ↥R.integers ↔ ϖS ∣ f :=
    fun f => (hkerR f).trans (hker_red f)

  have hdomin : ∀ x : Fbar, x ∈ Q.toValuationSubring → ∃ s : ↥S, red s = x := by
    intro x hx
    obtain ⟨a, b, hb, hab⟩ := hfracbar x
    have hb' : red b ≠ 0 := hb
    have hab' : x * red b = red a := hab
    by_cases ha : ϖS ∣ a
    · refine ⟨0, ?_⟩
      rw [map_zero]
      rw [hdvd0 a ha] at hab'
      exact ((mul_eq_zero.mp hab').resolve_right hb').symm
    · have hbnd : ¬ ϖS ∣ b := fun h => hb' (hdvd0 b h)
      obtain ⟨m, ua, ca, hua, hfa⟩ := star a ha
      obtain ⟨n, ub, cb, hub, hfb⟩ := star b hbnd
      have hra : red a = red t ^ m * red ua := star_red a ua ca m hfa
      have hrb : red b = red t ^ n * red ub := star_red b ub cb n hfb
      rcases Nat.lt_or_ge m n with hmn | hnm
      swap
      ·
        refine ⟨t ^ (m - n) * ua * ((hub.unit⁻¹ : (↥S)ˣ) : ↥S), ?_⟩
        apply mul_right_cancel₀ hb'
        have hinv : red ((hub.unit⁻¹ : (↥S)ˣ) : ↥S) * red ub = 1 := by
          rw [← map_mul, hub.val_inv_mul, map_one]
        rw [hab', hra, hrb, map_mul, map_mul, map_pow]
        calc red t ^ (m - n) * red ua * red ((hub.unit⁻¹ : (↥S)ˣ) : ↥S) * (red t ^ n * red ub)
            = red t ^ (m - n) * red t ^ n * red ua * (red ((hub.unit⁻¹ : (↥S)ˣ) : ↥S) * red ub) := by ring
          _ = red t ^ m * red ua := by rw [hinv, mul_one, ← pow_add, Nat.sub_add_cancel hnm]
      ·
        exfalso
        have hτm0 : red t ^ m ≠ 0 := pow_ne_zero m hτ0
        have heq : red ua = x * red t ^ (n - m) * red ub := by
          apply mul_left_cancel₀ hτm0
          calc red t ^ m * red ua = x * red b := by rw [hab', hra]
            _ = x * (red t ^ m * red t ^ (n - m) * red ub) := by
                rw [hrb, ← pow_add, Nat.add_sub_cancel' hmn.le]
            _ = red t ^ m * (x * red t ^ (n - m) * red ub) := by ring
        apply (IsLocalRing.notMem_maximalIdeal.mpr (hunitO ua hua))
        have hmem : (⟨x, hx⟩ : ↥Q.toValuationSubring) * ⟨red t, hτO⟩ ^ (n - m) * ⟨red ub, (hreads' ub).1⟩ ∈
            maximalIdeal ↥Q.toValuationSubring :=
          Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _
            (Ideal.pow_mem_of_mem _ hτmax _ (Nat.sub_pos_of_lt hmn)))
        have hcoe : (⟨red ua, (hreads' ua).1⟩ : ↥Q.toValuationSubring) =
            ⟨x, hx⟩ * ⟨red t, hτO⟩ ^ (n - m) * ⟨red ub, (hreads' ub).1⟩ :=
          Subtype.ext (by change red ua = _; rw [heq]; first | rfl | simp)
        rw [hcoe]
        exact hmem

  have hirrQ : Irreducible (⟨red t, hτO⟩ : ↥Q.toValuationSubring) := by
    refine ⟨fun hu => (IsLocalRing.notMem_maximalIdeal.mpr hu) hτmax, ?_⟩
    intro a b habt
    by_contra hab
    rw [not_or] at hab
    obtain ⟨s₁, hs₁⟩ := hdomin (a : Fbar) a.2
    obtain ⟨s₂, hs₂⟩ := hdomin (b : Fbar) b.2
    have hs₁m : s₁ ∈ maximalIdeal ↥S := by
      rw [← (hreads' s₁).2, hs₁]
      exact ValuationSubring.coe_mem_nonunits_iff.mpr ((IsLocalRing.mem_maximalIdeal _).mpr hab.1)
    have hs₂m : s₂ ∈ maximalIdeal ↥S := by
      rw [← (hreads' s₂).2, hs₂]
      exact ValuationSubring.coe_mem_nonunits_iff.mpr ((IsLocalRing.mem_maximalIdeal _).mpr hab.2)

    have hprod : red t = (a : Fbar) * (b : Fbar) := congrArg Subtype.val habt
    have hdiff : ϖS ∣ (t - s₁ * s₂) := by
      rw [← hker_red, map_sub, map_mul, hs₁, hs₂, hprod, sub_self]
    rw [hmax] at hs₁m hs₂m
    obtain ⟨a₁, b₁, h₁⟩ := Ideal.mem_span_pair.mp hs₁m
    obtain ⟨a₂, b₂, h₂⟩ := Ideal.mem_span_pair.mp hs₂m
    obtain ⟨d, hd⟩ := hdiff
    have hkey : t * (1 - b₁ * b₂ * t) = ϖS * (d + a₁ * a₂ * ϖS + a₁ * b₂ * t + b₁ * a₂ * t) := by
      have h' : t = s₁ * s₂ + ϖS * d := by rw [← hd]; ring
      rw [← h₁, ← h₂] at h'
      linear_combination h'
    have hw : IsUnit (1 - b₁ * b₂ * t) := by
      rw [← IsLocalRing.notMem_maximalIdeal]
      intro hmem
      have h1 : (1 : ↥S) ∈ maximalIdeal ↥S := by
        have := Ideal.add_mem _ hmem (Ideal.mul_mem_left _ (b₁ * b₂) htmax)
        rwa [sub_add_cancel] at this
      exact (IsLocalRing.maximalIdeal.isMaximal ↥S).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    apply ht
    rw [Ideal.mem_span_singleton]
    refine ⟨(d + a₁ * a₂ * ϖS + a₁ * b₂ * t + b₁ * a₂ * t) * ((hw.unit⁻¹ : (↥S)ˣ) : ↥S), ?_⟩
    calc t = t * ((1 - b₁ * b₂ * t) * ((hw.unit⁻¹ : (↥S)ˣ) : ↥S)) := by
          rw [hw.mul_val_inv, mul_one]
      _ = ϖS * ((d + a₁ * a₂ * ϖS + a₁ * b₂ * t + b₁ * a₂ * t) * ((hw.unit⁻¹ : (↥S)ˣ) : ↥S)) := by
          rw [← mul_assoc, hkey, mul_assoc]
  have hordQ : Q.ord (R.residue ⟨(t : F), hSR t⟩) = 1 := Place.ord_coe_irreducible Q hirrQ

  have hres : ∀ f : ↥S, ∃ hm : R.residue ⟨(f : F), hSR f⟩ ∈ Q.toValuationSubring,
      IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : F), hSR f⟩, hm⟩ =
        algebraMap (ResidueField ↥A) Q.ResidueField (χ f) := by
    intro f
    refine ⟨(hreads' f).1, ?_⟩
    obtain ⟨i, hi⟩ := hκ (χ f)
    have ha : IsLocalRing.residue ↥A (cst i) = χ f := hi
    let sa : ↥S := ⟨algebraMap L F (cst i : L), hAS i⟩
    have hχ : χ sa = χ f := (hχA i).trans ha
    have hdm : f - sa ∈ maximalIdeal ↥S := by
      rw [← hker, RingHom.mem_ker, map_sub, hχ, sub_self]
    have hred_sa : red sa = algebraMap (ResidueField ↥A) Fbar (IsLocalRing.residue ↥A (cst i)) :=
      R.residue_algebraMap (cst i)
    have hQ : (⟨red f, (hreads' f).1⟩ : ↥Q.toValuationSubring) - ⟨red sa, (hreads' sa).1⟩ ∈
        maximalIdeal ↥Q.toValuationSubring := by
      rw [← ValuationSubring.coe_mem_nonunits_iff]
      have : (((⟨red f, (hreads' f).1⟩ : ↥Q.toValuationSubring) - ⟨red sa, (hreads' sa).1⟩ :
          ↥Q.toValuationSubring) : Fbar) = red (f - sa) := by
        rw [map_sub]; rfl
      rw [this]
      exact (hreads' (f - sa)).2.mpr hdm
    have hQ' : IsLocalRing.residue ↥Q.toValuationSubring ⟨red f, (hreads' f).1⟩ =
        IsLocalRing.residue ↥Q.toValuationSubring ⟨red sa, (hreads' sa).1⟩ := by
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
      exact hQ
    have hsaO : (⟨red sa, (hreads' sa).1⟩ : ↥Q.toValuationSubring) =
        algebraMap (ResidueField ↥A) ↥Q.toValuationSubring (IsLocalRing.residue ↥A (cst i)) :=
      Subtype.ext (by rw [Place.coe_algebraMap]; exact hred_sa)
    calc IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : F), hSR f⟩, (hreads' f).1⟩
        = IsLocalRing.residue ↥Q.toValuationSubring ⟨red sa, (hreads' sa).1⟩ := hQ'
      _ = IsLocalRing.residue ↥Q.toValuationSubring
            (algebraMap (ResidueField ↥A) ↥Q.toValuationSubring (IsLocalRing.residue ↥A (cst i))) := by rw [hsaO]
      _ = algebraMap (ResidueField ↥A) Q.ResidueField (IsLocalRing.residue ↥A (cst i)) := rfl
      _ = algebraMap (ResidueField ↥A) Q.ResidueField (χ f) := by rw [ha]
  exact ⟨hcen, hres, hordQ⟩

end S_AlgebraicCurve_RegularProlongation_comap_maximalIdeal_eq_span_and_residue_eq_and_ord_eq_one_of_reads_of_constants
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_comap_maximalIdeal_eq_span_and_residue_eq_and_ord_eq_one_of_reads_of_constants (solution)
