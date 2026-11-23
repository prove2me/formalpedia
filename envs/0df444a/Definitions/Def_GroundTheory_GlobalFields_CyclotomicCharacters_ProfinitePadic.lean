-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ProfinitePadic
-- name    : GroundTheory_GlobalFields_CyclotomicCharacters_ProfinitePadic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:42.104112+00:00
-- url     : https://prove2.me/theorems/755dd4b4-176b-4796-af28-46cf8f4580a4
-- title:
--   Profinite Padic
-- statement:
--   Definitions and structural lemmas for Profinite Padic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/ProfinitePadic.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Character
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ContinuousToZModPow
import Theorems.Thm_GroundTheory_Global_Cyclotomic_toZModPow_toPadicInt
import Theorems.Thm_GroundTheory_LocalField_Abstract_ProfiniteInteger_castHom_proj
import Theorems.Thm_GroundTheory_LocalField_Abstract_ProfiniteInteger_continuous_proj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open scoped GroundTheory.LocalField.Abstract
namespace GroundTheory.Global
namespace Cyclotomic
open GroundTheory.LocalField.Abstract
instance factPrime (q : Nat.Primes) : Fact (q : ℕ).Prime := ⟨q.2⟩
section Padic
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]
theorem norm_sub_le_of_toZModPow_eq {x y : ℤ_[ℓ]} {n : ℕ}
    (h : PadicInt.toZModPow n x = PadicInt.toZModPow n y) :
    ‖x - y‖ ≤ (ℓ : ℝ) ^ (-(n : ℤ)) := by
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
    h, sub_self]
theorem exists_zpow_neg_lt {ε : ℝ} (hε : 0 < ε) : ∃ n : ℕ, (ℓ : ℝ) ^ (-(n : ℤ)) < ε := by
  have h1 : (1 : ℝ) < ℓ := by exact_mod_cast hℓ.out.one_lt
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ h1)
  exact ⟨n, by rwa [zpow_neg, zpow_natCast, ← inv_pow]⟩
theorem continuous_of_continuous_toZModPow {X : Type*} [TopologicalSpace X] {f : X → ℤ_[ℓ]}
    (h : ∀ n, Continuous fun x => PadicInt.toZModPow n (f x)) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun x => Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨n, hn⟩ := exists_zpow_neg_lt (ℓ := ℓ) hε
  have hU : IsOpen {y | PadicInt.toZModPow n (f y) = PadicInt.toZModPow n (f x)} :=
    (isOpen_discrete {PadicInt.toZModPow n (f x)}).preimage (h n)
  filter_upwards [hU.mem_nhds rfl] with y hy
  rw [dist_eq_norm]
  exact (norm_sub_le_of_toZModPow_eq hy).trans_lt hn
variable (ℓ) in

theorem continuous_toPadicInt : Continuous (toPadicInt ℓ) :=
  continuous_of_continuous_toZModPow fun n =>
    (ProfiniteInteger.continuous_proj (primePowPNat ℓ n)).congr fun x =>
      (toZModPow_toPadicInt ℓ n x).symm
end Padic
section CRT
theorem equivPi_apply {n : ℕ} (hn : n ≠ 0) (z : ZMod n) (p : n.primeFactors) :
    ZMod.equivPi n hn z p = ZMod.castHom (Nat.ordProj_dvd n p) _ z :=
  RingHom.congr_fun (Subsingleton.elim
    ((Pi.evalRingHom (fun p : n.primeFactors => ZMod ((p : ℕ) ^ n.factorization p)) p).comp
      (ZMod.equivPi n hn).toRingHom) (ZMod.castHom (Nat.ordProj_dvd n p) _)) z
theorem eq_of_castHom_ordProj_eq {n : ℕ} (hn : n ≠ 0) {a b : ZMod n}
    (h : ∀ p ∈ n.primeFactors,
      ZMod.castHom (Nat.ordProj_dvd n p) (ZMod (p ^ n.factorization p)) a =
        ZMod.castHom (Nat.ordProj_dvd n p) _ b) : a = b :=
  (ZMod.equivPi n hn).injective (funext fun p => by rw [equivPi_apply, equivPi_apply, h p p.2])
theorem castHom_castHom {k m n : ℕ} (h₁ : k ∣ m) (h₂ : m ∣ n) (h₃ : k ∣ n) (z : ZMod n) :
    ZMod.castHom h₁ (ZMod k) (ZMod.castHom h₂ (ZMod m) z) = ZMod.castHom h₃ (ZMod k) z :=
  RingHom.congr_fun (Subsingleton.elim ((ZMod.castHom h₁ (ZMod k)).comp (ZMod.castHom h₂ (ZMod m)))
    (ZMod.castHom h₃ (ZMod k))) z
end CRT
section Product
noncomputable def padicReduceHom (n : ℕ) :
    (∀ q : Nat.Primes, ℤ_[q]) →+* ∀ p : n.primeFactors, ZMod ((p : ℕ) ^ n.factorization p) :=
  RingHom.pi fun p => (@PadicInt.toZModPow (p : ℕ) ⟨Nat.prime_of_mem_primeFactors p.2⟩
    (n.factorization p)).comp
      (Pi.evalRingHom (fun q : Nat.Primes => ℤ_[q]) ⟨p, Nat.prime_of_mem_primeFactors p.2⟩)
noncomputable def ofPadicsFamily (x : ∀ q : Nat.Primes, ℤ_[q]) (n : ℕ+) : ZMod n :=
  (ZMod.equivPi (n : ℕ) n.ne_zero).symm (padicReduceHom n x)
theorem castHom_ofPadicsFamily (x : ∀ q : Nat.Primes, ℤ_[q]) (n : ℕ+) {p : ℕ}
    (hp : p ∈ (n : ℕ).primeFactors) :
    ZMod.castHom (Nat.ordProj_dvd n p) _ (ofPadicsFamily x n) =
      @PadicInt.toZModPow p ⟨Nat.prime_of_mem_primeFactors hp⟩
        ((n : ℕ).factorization p) (x ⟨p, Nat.prime_of_mem_primeFactors hp⟩) := by
  have := equivPi_apply n.ne_zero (ofPadicsFamily x n) ⟨p, hp⟩
  rw [ofPadicsFamily, RingEquiv.apply_symm_apply] at this
  rw [ofPadicsFamily, ← this]
  rfl
theorem ofPadicsFamily_mem (x : ∀ q : Nat.Primes, ℤ_[q]) :
    ofPadicsFamily x ∈ profiniteIntegers := by
  rw [mem_profiniteIntegers]
  intro m n h
  refine eq_of_castHom_ordProj_eq m.ne_zero fun p hp => ?_
  have hpn : p ∈ (n : ℕ).primeFactors := Nat.primeFactors_mono h n.ne_zero hp
  have hle : (m : ℕ).factorization p ≤ (n : ℕ).factorization p :=
    (Nat.factorization_le_iff_dvd m.ne_zero n.ne_zero).2 h p
  rw [castHom_castHom _ h ((Nat.ordProj_dvd m p).trans h),
    ← castHom_castHom (pow_dvd_pow p hle) (Nat.ordProj_dvd n p) ((Nat.ordProj_dvd m p).trans h),
    castHom_ofPadicsFamily x n hpn, castHom_ofPadicsFamily x m hp]
  have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  exact PadicInt.cast_toZModPow _ _ hle _
noncomputable def ofPadics : (∀ q : Nat.Primes, ℤ_[q]) →+* ℤ̂ :=
  RingHom.codRestrict
    (RingHom.pi fun n : ℕ+ => (ZMod.equivPi (n : ℕ) n.ne_zero).symm.toRingHom.comp
      (padicReduceHom n)) profiniteIntegers ofPadicsFamily_mem
theorem proj_ofPadics (x : ∀ q : Nat.Primes, ℤ_[q]) (n : ℕ+) :
    ProfiniteInteger.proj n (ofPadics x) = ofPadicsFamily x n :=
  rfl
noncomputable def toPadics : ℤ̂ →+* ∀ q : Nat.Primes, ℤ_[q] :=
  RingHom.pi fun q => toPadicInt q
@[simp] theorem toPadics_apply (x : ℤ̂) (q : Nat.Primes) : toPadics x q = toPadicInt q x :=
  rfl
theorem toPadics_ofPadics (x : ∀ q : Nat.Primes, ℤ_[q]) : toPadics (ofPadics x) = x := by
  funext q
  refine PadicInt.ext_of_toZModPow.mp fun k => ?_
  rw [toPadics_apply, toZModPow_toPadicInt, proj_ofPadics]
  refine eq_of_castHom_ordProj_eq (primePowPNat q k).ne_zero fun p hp => ?_
  have hpq : p = q := by
    have hk : k ≠ 0 := by
      rintro rfl
      simp at hp
    rw [coe_primePowPNat, Nat.primeFactors_prime_pow hk q.2, Finset.mem_singleton] at hp
    exact hp
  subst hpq
  have hle : (primePowPNat (q : ℕ) k : ℕ).factorization q ≤ k := by
    simp [coe_primePowPNat, Nat.factorization_pow, Nat.Prime.factorization_self q.2]
  rw [castHom_ofPadicsFamily x _ hp]
  exact (PadicInt.cast_toZModPow _ _ hle _).symm
theorem ofPadics_toPadics (x : ℤ̂) : ofPadics (toPadics x) = x := by
  ext n
  refine eq_of_castHom_ordProj_eq n.ne_zero fun p hp => ?_
  rw [proj_ofPadics, castHom_ofPadicsFamily _ n hp]
  have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  change PadicInt.toZModPow _ (toPadicInt p x) = _
  rw [toZModPow_toPadicInt]
  exact (ProfiniteInteger.castHom_proj (m := primePowPNat p ((n : ℕ).factorization p))
    (Nat.ordProj_dvd n p) x).symm
noncomputable def padicEquiv : ℤ̂ ≃+* ∀ q : Nat.Primes, ℤ_[q] :=
  RingEquiv.ofRingHom toPadics ofPadics (RingHom.ext toPadics_ofPadics)
    (RingHom.ext ofPadics_toPadics)
theorem continuous_toPadics : Continuous toPadics :=
  continuous_pi fun q => continuous_toPadicInt q
noncomputable def padicHomeomorph : ℤ̂ ≃ₜ ∀ q : Nat.Primes, ℤ_[q] :=
  Continuous.homeoOfEquivCompactToT2 (f := padicEquiv.toEquiv) continuous_toPadics
noncomputable def unitsPadicEquiv : ℤ̂ˣ ≃* ∀ q : Nat.Primes, ℤ_[q]ˣ :=
  (Units.mapEquiv padicEquiv.toMulEquiv).trans MulEquiv.piUnits
end Product
end Cyclotomic
end GroundTheory.Global


