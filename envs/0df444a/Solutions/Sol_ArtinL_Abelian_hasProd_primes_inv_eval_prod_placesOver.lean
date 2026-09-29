-- Prove2me | solution 1 for ArtinL.Abelian.hasProd_primes_inv_eval_prod_placesOver
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/20fd6777-d591-5e91-b94a-cbaa8959f8b9

import Mathlib
import Definitions.Def_ArtinL_EulerFactor
import Definitions.Def_ArtinL_Abelian
import Theorems.Thm_ArtinL_Abelian_lSeriesSummable_and_lSeries_ne_zero_and_hasProd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ArtinL_Abelian_hasProd_primes_inv_eval_prod_placesOver

set_option autoImplicit false

open scoped MatrixGroups
open NumberField

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

namespace ArtinL
p2m_export "ArtinL" "LSeries Abelian.localValue Abelian.LSeries Abelian.lSeriesSummable_and_lSeries_ne_zero_and_hasProd"
namespace Abelian
p2m_export "ArtinL.Abelian" "localValue LSeries lSeriesSummable_and_lSeries_ne_zero_and_hasProd"
namespace C5
p2m_open "ArtinL.Abelian ArtinL"

open IsDedekindDomain NumberField Polynomial

variable (K : Type) [Field K] [NumberField K]

noncomputable def charOf (v : HeightOneSpectrum (𝓞 K)) : ℕ := ringChar (𝓞 K ⧸ v.asIdeal)

theorem charOf_prime (v : HeightOneSpectrum (𝓞 K)) : (charOf K v).Prime := by
  haveI := v.isMaximal
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  letI := Ideal.Quotient.field v.asIdeal
  exact CharP.char_is_prime (𝓞 K ⧸ v.asIdeal) _

theorem natCast_mem_iff (v : HeightOneSpectrum (𝓞 K)) (p : ℕ) (hp : p.Prime) :
    ((p : ℕ) : 𝓞 K) ∈ v.asIdeal ↔ charOf K v = p := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, CharP.cast_eq_zero_iff (𝓞 K ⧸ v.asIdeal) (charOf K v)]
  constructor
  · intro h
    exact (Nat.prime_dvd_prime_iff_eq (charOf_prime K v) hp).1 h
  · rintro rfl
    exact dvd_rfl

theorem charOf_mem (v : HeightOneSpectrum (𝓞 K)) : ((charOf K v : ℕ) : 𝓞 K) ∈ v.asIdeal :=
  (natCast_mem_iff K v _ (charOf_prime K v)).2 rfl

private noncomputable def _root_.ArtinL.Abelian.C5.under (v : HeightOneSpectrum (𝓞 K)) : Nat.Primes := ⟨charOf K v, charOf_prime K v⟩

p2m_export "ArtinL.Abelian.C5" "under"
theorem under_eq_iff (v : HeightOneSpectrum (𝓞 K)) (p : Nat.Primes) :
    under K v = p ↔ ((p : ℕ) : 𝓞 K) ∈ v.asIdeal := by
  rw [natCast_mem_iff K v p p.2, under]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

theorem liesOver_of_mem (v : HeightOneSpectrum (𝓞 K)) (p : ℕ) (hp : p.Prime) (hv : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal) :
    v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
  haveI := v.isMaximal
  haveI := v.isPrime
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    Ideal.IsPrime.isMaximal (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero) |>.2
      (Nat.prime_iff_prime_int.1 hp)) (by simpa using hp.ne_zero)
  haveI : (v.asIdeal.under ℤ).IsPrime := Ideal.IsPrime.under ℤ v.asIdeal
  refine ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩
  rw [Ideal.span_le, Set.singleton_subset_iff]
  change algebraMap ℤ (𝓞 K) (p : ℤ) ∈ v.asIdeal
  rwa [map_natCast]

theorem finite_fibre (p : Nat.Primes) : Finite {v : HeightOneSpectrum (𝓞 K) // under K v = p} := by
  haveI : (Ideal.span {((p : ℕ) : ℤ)}).IsMaximal :=
    Ideal.IsPrime.isMaximal (Ideal.span_singleton_prime (by exact_mod_cast p.2.ne_zero) |>.2
      (Nat.prime_iff_prime_int.1 p.2)) (by simpa using p.2.ne_zero)
  have hinj : Set.InjOn (fun w : HeightOneSpectrum (𝓞 K) => w.asIdeal)
      ((fun w : HeightOneSpectrum (𝓞 K) => w.asIdeal) ⁻¹' ((Ideal.span {((p : ℕ) : ℤ)}).primesOver (𝓞 K))) :=
    fun _ _ _ _ h => HeightOneSpectrum.ext h
  have hfin : {w : HeightOneSpectrum (𝓞 K) | under K w = p}.Finite :=
    ((IsDedekindDomain.primesOver_finite (Ideal.span {((p : ℕ) : ℤ)}) (𝓞 K)).preimage hinj).subset
      fun w hw => by
        have hw' : ((p : ℕ) : 𝓞 K) ∈ w.asIdeal := (under_eq_iff K w p).1 hw
        exact ⟨w.isPrime, liesOver_of_mem K w p p.2 hw'⟩
  exact hfin.to_subtype

theorem natCast_pow_cpow (p f : ℕ) (w : ℂ) : (((p ^ f : ℕ) : ℂ)) ^ w = (((p : ℕ) : ℂ) ^ w) ^ f := by
  induction f with
  | zero => simp
  | succ f ih => rw [pow_succ, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, ih, pow_succ]

theorem absNorm_eq (v : HeightOneSpectrum (𝓞 K)) (p : ℕ) (hp : p.Prime) (hv : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal) :
    Ideal.absNorm v.asIdeal = p ^ (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal := by
  haveI := liesOver_of_mem K v p hp hv
  have h := Ideal.absNorm_eq_pow_inertiaDeg v.asIdeal (p := (p : ℤ)) (Nat.prime_iff_prime_int.1 hp)
  simpa using h

end ArtinL.Abelian.C5

open scoped Classical in

theorem solution
    (K : Type) (M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois K M] (ψ : (M ≃ₐ[K] M) →* ℂˣ) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes =>
        ((∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
            if ((p : ℕ) : 𝓞 K) ∈ v.asIdeal then
              (1 - Polynomial.C (ArtinL.Abelian.localValue ψ v) *
                Polynomial.X ^ (Ideal.span {((p : ℕ) : ℤ)}).inertiaDeg' v.asIdeal : Polynomial ℂ)
            else 1).eval ((p : ℂ) ^ (-s)))⁻¹)
      (ArtinL.Abelian.LSeries ψ s) := by
  classical
  obtain ⟨-, -, hprod⟩ := ArtinL.Abelian.lSeriesSummable_and_lSeries_ne_zero_and_hasProd K M ψ hs

  have h2 := (Equiv.hasProd_iff (Equiv.sigmaFiberEquiv (ArtinL.Abelian.C5.under K))).2 hprod
  refine h2.sigma fun p => ?_
  haveI : Fintype {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) // ArtinL.Abelian.C5.under K v = p} :=
    @Fintype.ofFinite _ (ArtinL.Abelian.C5.finite_fibre K p)
  convert hasProd_fintype (fun c : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) // ArtinL.Abelian.C5.under K v = p} =>
    (1 - ArtinL.Abelian.localValue ψ c.1 * (Ideal.absNorm c.1.asIdeal : ℂ) ^ (-s))⁻¹) using 1
  · rfl
  rw [Finset.prod_inv_distrib]
  congr 1
  set x : ℂ := ((p : ℕ) : ℂ) ^ (-s) with hx
  set g : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → Polynomial ℂ := fun v =>
    if ((p : ℕ) : 𝓞 K) ∈ v.asIdeal then
      (1 - Polynomial.C (ArtinL.Abelian.localValue ψ v) *
        Polynomial.X ^ (Ideal.span {((p : ℕ) : ℤ)}).inertiaDeg' v.asIdeal : Polynomial ℂ)
    else 1 with hg
  have hfinset : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) | ArtinL.Abelian.C5.under K v = p}.Finite :=
    Set.finite_coe_iff.1 (ArtinL.Abelian.C5.finite_fibre K p)
  have hsupp : Function.HasFiniteMulSupport g := by
    refine hfinset.subset fun v hv => ?_
    rw [Function.mem_mulSupport] at hv
    by_contra hv'
    apply hv
    rw [hg]
    simp only
    rw [if_neg (fun h => hv' ((ArtinL.Abelian.C5.under_eq_iff K v p).2 h))]
  have e1 : Polynomial.eval x (∏ᶠ v, g v) = ∏ᶠ v, Polynomial.eval x (g v) := by
    have := MonoidHom.map_finprod (Polynomial.evalRingHom x).toMonoidHom hsupp
    simpa using this
  change Polynomial.eval x (∏ᶠ v, g v) = _
  rw [e1]
  have e2 : (fun v => Polynomial.eval x (g v)) =
      {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) | ArtinL.Abelian.C5.under K v = p}.mulIndicator
        fun v => (1 - ArtinL.Abelian.localValue ψ v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by
    funext v
    by_cases hv : ArtinL.Abelian.C5.under K v = p
    · have hv' : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal := (ArtinL.Abelian.C5.under_eq_iff K v p).1 hv
      rw [Set.mulIndicator_of_mem (show v ∈ {v | ArtinL.Abelian.C5.under K v = p} from hv), hg]
      simp only
      rw [if_pos hv']
      simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      rw [ArtinL.Abelian.C5.absNorm_eq K v p p.2 hv', ArtinL.Abelian.C5.natCast_pow_cpow]
    · have hv' : ¬ ((p : ℕ) : 𝓞 K) ∈ v.asIdeal := fun h => hv ((ArtinL.Abelian.C5.under_eq_iff K v p).2 h)
      rw [Set.mulIndicator_of_notMem (show v ∉ {v | ArtinL.Abelian.C5.under K v = p} from hv), hg]
      simp only
      rw [if_neg hv', Polynomial.eval_one]
  letI : Fintype (↥({v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) | ArtinL.Abelian.C5.under K v = p} :
      Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))) := this
  rw [e2, ← finprod_mem_def, ← finprod_set_coe_eq_finprod_mem, finprod_eq_prod_of_fintype]
  rfl

end S_ArtinL_Abelian_hasProd_primes_inv_eval_prod_placesOver
end P2MW
export P2MW.S_ArtinL_Abelian_hasProd_primes_inv_eval_prod_placesOver (solution)
