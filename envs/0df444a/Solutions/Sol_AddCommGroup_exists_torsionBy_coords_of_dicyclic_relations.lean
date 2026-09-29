-- Prove2me | solution 1 for AddCommGroup.exists_torsionBy_coords_of_dicyclic_relations
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/8c8cbe00-f1ae-5607-bb0e-cf2c541e1e47

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AddCommGroup_exists_torsionBy_coords_of_dicyclic_relations

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace P2MKcADAPT

variable {M : ℕ} [NeZero M]

abbrev V (M : ℕ) : Type := ZMod M × ZMod M

theorem nsmul_V (n : ℕ) (v : V M) : n • v = ((n : ZMod M) * v.1, (n : ZMod M) * v.2) := by
  ext <;> simp [nsmul_eq_mul]

theorem val_nsmul_V (u : ZMod M) (v : V M) : u.val • v = (u * v.1, u * v.2) := by
  rw [nsmul_V, ZMod.natCast_zmod_val]

theorem eq_val_smul_add (v : V M) : v = v.1.val • ((1 : ZMod M), (0 : ZMod M)) + v.2.val • ((0 : ZMod M), (1 : ZMod M)) := by
  rw [val_nsmul_V, val_nsmul_V]; ext <;> simp

theorem apply_eq (ψ : V M →+ V M) (r0 r1 : V M) (h0 : ψ (1, 0) = r0) (h1 : ψ (0, 1) = r1) (v : V M) :
    ψ v = (v.1 * r0.1 + v.2 * r1.1, v.1 * r0.2 + v.2 * r1.2) := by
  conv_lhs => rw [eq_val_smul_add v]
  rw [map_add, map_nsmul, map_nsmul, h0, h1, val_nsmul_V, val_nsmul_V]
  rfl

section Coords

variable {A : Type*} [AddCommGroup A] (e : ZMod M × ZMod M ≃+ Submodule.torsionBy ℤ A M)

def resT (φ : A →+ A) : Submodule.torsionBy ℤ A M →+ Submodule.torsionBy ℤ A M where
  toFun t := ⟨φ t, by
    rw [Submodule.mem_torsionBy_iff]
    have := t.2
    rw [Submodule.mem_torsionBy_iff] at this
    rw [← map_zsmul, this, map_zero]⟩
  map_zero' := by ext; simp
  map_add' s t := by ext; simp

@[scoped simp] theorem coe_resT (φ : A →+ A) (t : Submodule.torsionBy ℤ A M) : ((resT φ t : _) : A) = φ t := rfl

def toV (φ : A →+ A) : V M →+ V M :=
  e.symm.toAddMonoidHom.comp ((resT φ).comp e.toAddMonoidHom)

theorem toV_apply (φ : A →+ A) (v : V M) : toV e φ v = e.symm (resT φ (e v)) := rfl

theorem e_toV (φ : A →+ A) (v : V M) : e (toV e φ v) = resT φ (e v) := by
  rw [toV_apply, AddEquiv.apply_symm_apply]

theorem coe_e_toV (φ : A →+ A) (v : V M) : ((e (toV e φ v) : _) : A) = φ (e v) := by
  rw [e_toV]; rfl

theorem toV_toV (φ χ : A →+ A) (v : V M) : toV e φ (toV e χ v) = e.symm (resT φ (resT χ (e v))) := by
  rw [toV_apply, e_toV]

theorem coords_of_isUnit (φ : A →+ A) (w : V M)
    (hu : IsUnit (w.1 * (toV e φ w).2 - w.2 * (toV e φ w).1)) :
    ∃ P : A, (M : ℤ) • P = 0 ∧ ∀ T : A, (M : ℤ) • T = 0 →
      ∃! c : ZMod M × ZMod M, c.1.val • P + c.2.val • φ P = T := by
  set f : V M := toV e φ w with hf
  set P : A := ((e w : _) : A) with hP
  have hPmem : (M : ℤ) • P = 0 := by
    have := (e w).2
    rw [Submodule.mem_torsionBy_iff] at this
    exact this

  let L : V M → V M := fun c => c.1.val • w + c.2.val • f
  have hL : ∀ c, L c = (c.1 * w.1 + c.2 * f.1, c.1 * w.2 + c.2 * f.2) := by
    intro c
    show c.1.val • w + c.2.val • f = _
    rw [val_nsmul_V, val_nsmul_V]; rfl
  have hLinj : Function.Injective L := by
    intro c d hcd
    rw [hL, hL, Prod.mk.injEq] at hcd
    obtain ⟨h1, h2⟩ := hcd
    have e1 : (c.1 - d.1) * (w.1 * f.2 - w.2 * f.1) = 0 := by linear_combination f.2 * h1 - f.1 * h2
    have e2 : (c.2 - d.2) * (w.1 * f.2 - w.2 * f.1) = 0 := by linear_combination (-w.2) * h1 + w.1 * h2
    rw [hu.mul_left_eq_zero, sub_eq_zero] at e1 e2
    exact Prod.ext e1 e2
  have hLsurj : Function.Surjective L := Finite.injective_iff_surjective.mp hLinj

  have he : ∀ c : V M, ((e (L c) : _) : A) = c.1.val • P + c.2.val • φ P := by
    intro c
    show ((e (c.1.val • w + c.2.val • f) : _) : A) = _
    rw [map_add, map_nsmul, map_nsmul, Submodule.coe_add, AddSubmonoidClass.coe_nsmul,
      AddSubmonoidClass.coe_nsmul, hf, coe_e_toV]
  refine ⟨P, hPmem, fun T hT => ?_⟩
  have hTmem : T ∈ Submodule.torsionBy ℤ A M := by rw [Submodule.mem_torsionBy_iff]; exact hT
  obtain ⟨c, hc⟩ := hLsurj (e.symm ⟨T, hTmem⟩)
  refine ⟨c, ?_, fun d hd => ?_⟩
  · show c.1.val • P + c.2.val • φ P = T
    rw [← he, hc, AddEquiv.apply_symm_apply]
  · apply hLinj
    apply e.injective
    apply Subtype.ext
    rw [he, he, hd, ← he, hc, AddEquiv.apply_symm_apply]

end Coords

def Q {R : Type*} [CommRing R] (b00 b01 b10 b11 x y : R) : R :=
  b01 * x * x + (b11 - b00) * x * y - b10 * y * y

theorem det_eq_Q (ψ : V M →+ V M) (r0 r1 : V M) (h0 : ψ (1, 0) = r0) (h1 : ψ (0, 1) = r1) (w : V M) :
    w.1 * (ψ w).2 - w.2 * (ψ w).1 = Q r0.1 r0.2 r1.1 r1.2 w.1 w.2 := by
  rw [apply_eq ψ r0 r1 h0 h1, Q]
  ring

theorem map_Q {R S : Type*} [CommRing R] [CommRing S] (π : R →+* S) (b00 b01 b10 b11 x y : R) :
    π (Q b00 b01 b10 b11 x y) = Q (π b00) (π b01) (π b10) (π b11) (π x) (π y) := by
  simp [Q, map_sub, map_mul, map_add]

theorem exists_isUnit_Q (b00 b01 b10 b11 : ZMod M)
    (hns : ∀ (p : ℕ) (hp : p.Prime) (hpM : p ∣ M),
      ¬ ((ZMod.castHom hpM (ZMod p)) b01 = 0 ∧ (ZMod.castHom hpM (ZMod p)) b10 = 0 ∧
          (ZMod.castHom hpM (ZMod p)) b00 = (ZMod.castHom hpM (ZMod p)) b11)) :
    ∃ x y : ZMod M, IsUnit (Q b00 b01 b10 b11 x y) := by
  classical

  have htest : ∀ p : ℕ, ∃ v : ℕ × ℕ, ∀ (hp : p.Prime) (hpM : p ∣ M),
      (ZMod.castHom hpM (ZMod p)) (Q b00 b01 b10 b11 (v.1 : ZMod M) (v.2 : ZMod M)) ≠ 0 := by
    intro p
    by_cases hp : p.Prime ∧ p ∣ M
    · obtain ⟨hp, hpM⟩ := hp
      set π := ZMod.castHom hpM (ZMod p) with hπ
      by_contra hcon
      push Not at hcon
      obtain ⟨_, _, h10⟩ := hcon (1, 0)
      obtain ⟨_, _, h01⟩ := hcon (0, 1)
      obtain ⟨_, _, h11⟩ := hcon (1, 1)
      rw [map_Q] at h10 h01 h11
      simp only [Nat.cast_one, Nat.cast_zero, map_one, map_zero] at h10 h01 h11
      simp only [Q] at h10 h01 h11
      apply hns p hp hpM
      refine ⟨?_, ?_, ?_⟩
      · linear_combination h10
      · linear_combination -h01
      · linear_combination h10 + h01 - h11
    · exact ⟨(0, 0), fun hp' hpM' => absurd ⟨hp', hpM'⟩ hp⟩
  choose pick hpick using htest

  set t : Finset ℕ := M.primeFactors with ht
  have hs : ∀ i ∈ t, (id i : ℕ) ≠ 0 := fun i hi => (Nat.prime_of_mem_primeFactors hi).ne_zero
  have hpw : (t : Set ℕ).Pairwise (Function.onFun Nat.Coprime id) := by
    intro i hi j hj hij
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hi) (Nat.prime_of_mem_primeFactors hj)).mpr hij
  obtain ⟨X, hX⟩ := Nat.chineseRemainderOfFinset (fun p => (pick p).1) id t hs hpw
  obtain ⟨Y, hY⟩ := Nat.chineseRemainderOfFinset (fun p => (pick p).2) id t hs hpw
  refine ⟨(X : ZMod M), (Y : ZMod M), ?_⟩
  set z := Q b00 b01 b10 b11 (X : ZMod M) (Y : ZMod M) with hz
  rw [← ZMod.natCast_zmod_val z]
  apply (ZMod.isUnit_iff_coprime _ _).mpr
  apply Nat.coprime_of_dvd
  intro k hk hkz hkM
  have hkt : k ∈ t := Nat.mem_primeFactors.mpr ⟨hk, hkM, NeZero.ne M⟩
  set π := ZMod.castHom hkM (ZMod k) with hπ
  have h1 : π z = 0 := by
    rw [← ZMod.natCast_zmod_val z, map_natCast, ZMod.natCast_eq_zero_iff]
    exact hkz
  have hXk : π (X : ZMod M) = ((pick k).1 : ZMod k) := by
    rw [map_natCast]
    have hh := hX k hkt
    simp only [id] at hh
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hh
  have hYk : π (Y : ZMod M) = ((pick k).2 : ZMod k) := by
    rw [map_natCast]
    have hh := hY k hkt
    simp only [id] at hh
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hh
  have h2 : π z = π (Q b00 b01 b10 b11 ((pick k).1 : ZMod M) ((pick k).2 : ZMod M)) := by
    rw [hz, map_Q, map_Q, hXk, hYk, map_natCast, map_natCast]
  exact hpick k hk hkM (h2 ▸ h1)

theorem not_scalar {p : ℕ} [Fact p.Prime] (h3 : (3 : ZMod p) ≠ 0)
    (a00 a01 a10 a11 b00 b01 b10 b11 : ZMod p)
    (hA1 : a00 * a00 + a01 * a10 = -1) (hA2 : a00 * a01 + a01 * a11 = 0)
    (hA3 : a10 * a00 + a11 * a10 = 0) (hA4 : a10 * a01 + a11 * a11 = -1)
    (hB1 : b00 * b00 + b01 * b10 + b00 + 1 = 0) (hB2 : b00 * b01 + b01 * b11 + b01 = 0)
    (hB3 : b10 * b00 + b11 * b10 + b10 = 0) (hB4 : b10 * b01 + b11 * b11 + b11 + 1 = 0)
    (hC1 : b00 * a00 + b01 * a10 = (a00 * b00 + a01 * b10) * b00 + (a00 * b01 + a01 * b11) * b10)
    (hC2 : b00 * a01 + b01 * a11 = (a00 * b00 + a01 * b10) * b01 + (a00 * b01 + a01 * b11) * b11)
    (hC3 : b10 * a00 + b11 * a10 = (a10 * b00 + a11 * b10) * b00 + (a10 * b01 + a11 * b11) * b10)
    (hC4 : b10 * a01 + b11 * a11 = (a10 * b00 + a11 * b10) * b01 + (a10 * b01 + a11 * b11) * b11) :
    ¬ (b01 = 0 ∧ b10 = 0 ∧ b00 = b11) ∧ ¬ (a01 = 0 ∧ a10 = 0 ∧ a00 = a11) := by
  have hβ : ¬ (b01 = 0 ∧ b10 = 0 ∧ b00 = b11) := by
    rintro ⟨h01, h10, hd⟩
    subst h01 h10
    subst hd

    have E1 : b00 * a00 - b00 * b00 * a00 = 0 := by linear_combination hC1
    have E3 : b00 * a10 - b00 * b00 * a10 = 0 := by linear_combination hC3
    have hk : b00 * b00 - b00 = 0 := by
      linear_combination (b00 * b00 - b00) * hA1 + a00 * E1 + a01 * E3
    apply h3
    linear_combination (3 - 2 * b00) * hB1 + (2 * b00 + 1) * hk
  refine ⟨hβ, ?_⟩
  rintro ⟨h01, h10, hd⟩
  subst h01 h10
  subst hd

  have S1 : b00 - (b00 * b00 + b01 * b10) = 0 := by
    linear_combination (-a00) * hC1 + (b00 - (b00 * b00 + b01 * b10)) * hA1
  have S2 : b01 - (b00 * b01 + b01 * b11) = 0 := by
    linear_combination (-a00) * hC2 + (b01 - (b00 * b01 + b01 * b11)) * hA1
  have S3 : b10 - (b10 * b00 + b11 * b10) = 0 := by
    linear_combination (-a00) * hC3 + (b10 - (b10 * b00 + b11 * b10)) * hA1
  have S4 : b11 - (b10 * b01 + b11 * b11) = 0 := by
    linear_combination (-a00) * hC4 + (b11 - (b10 * b01 + b11 * b11)) * hA1
  have F1 : 2 * b00 + 1 = 0 := by linear_combination hB1 + S1
  have F2 : 2 * b01 = 0 := by linear_combination hB2 + S2
  have F3 : 2 * b10 = 0 := by linear_combination hB3 + S3
  have F4 : 2 * b11 + 1 = 0 := by linear_combination hB4 + S4
  by_cases h2 : (2 : ZMod p) = 0
  · have : (1 : ZMod p) = 0 := by linear_combination F1 - b00 * h2
    exact one_ne_zero this
  · apply hβ
    refine ⟨(mul_eq_zero.mp F2).resolve_left h2, (mul_eq_zero.mp F3).resolve_left h2, ?_⟩
    have : 2 * (b00 - b11) = 0 := by linear_combination F1 - F4
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h2)

section Assembly

variable {A : Type*} [AddCommGroup A]

theorem main (hM : ¬ 3 ∣ M) (e : ZMod M × ZMod M ≃+ Submodule.torsionBy ℤ A M)
    (α β : A →+ A) (hα : ∀ T, α (α T) = -T) (hβ : ∀ T, β (β T) + β T + T = 0)
    (hαβ : ∀ T, α (β T) = β (β (α T))) :
    (∃ P : A, (M : ℤ) • P = 0 ∧ ∀ T : A, (M : ℤ) • T = 0 →
      ∃! c : ZMod M × ZMod M, c.1.val • P + c.2.val • β P = T) ∧
    (∃ P : A, (M : ℤ) • P = 0 ∧ ∀ T : A, (M : ℤ) • T = 0 →
      ∃! c : ZMod M × ZMod M, c.1.val • P + c.2.val • α P = T) := by
  set αV := toV e α with hαVdef
  set βV := toV e β with hβVdef

  have rαα : ∀ t : Submodule.torsionBy ℤ A M, resT α (resT α t) = -t := fun t =>
    Subtype.ext (by simp [hα])
  have rββ : ∀ t : Submodule.torsionBy ℤ A M, resT β (resT β t) + resT β t + t = 0 := fun t =>
    Subtype.ext (by simp [hβ])
  have rαβ : ∀ t : Submodule.torsionBy ℤ A M, resT α (resT β t) = resT β (resT β (resT α t)) := fun t =>
    Subtype.ext (by simp [hαβ])
  have hαV : ∀ v, αV (αV v) = -v := fun v => by
    rw [hαVdef, toV_toV, rαα, map_neg, AddEquiv.symm_apply_apply]
  have hβV : ∀ v, βV (βV v) + βV v + v = 0 := fun v => by
    rw [hβVdef, toV_toV, toV_apply]
    apply e.injective
    rw [map_add, map_add, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, map_zero]
    exact rββ (e v)
  have hαβV : ∀ v, αV (βV v) = βV (βV (αV v)) := fun v => by
    rw [hαVdef, hβVdef, toV_toV, toV_apply, toV_toV, AddEquiv.apply_symm_apply, rαβ]

  obtain ⟨a00, a01, ha0⟩ : ∃ a00 a01 : ZMod M, αV (1, 0) = (a00, a01) := ⟨_, _, rfl⟩
  obtain ⟨a10, a11, ha1⟩ : ∃ a10 a11 : ZMod M, αV (0, 1) = (a10, a11) := ⟨_, _, rfl⟩
  obtain ⟨b00, b01, hb0⟩ : ∃ b00 b01 : ZMod M, βV (1, 0) = (b00, b01) := ⟨_, _, rfl⟩
  obtain ⟨b10, b11, hb1⟩ : ∃ b10 b11 : ZMod M, βV (0, 1) = (b10, b11) := ⟨_, _, rfl⟩
  have eA := apply_eq αV _ _ ha0 ha1
  have eB := apply_eq βV _ _ hb0 hb1

  have hA := hαV (1, 0)
  have hA' := hαV (0, 1)
  have hB := hβV (1, 0)
  have hB' := hβV (0, 1)
  have hC := hαβV (1, 0)
  have hC' := hαβV (0, 1)
  simp only [eA, eB, Prod.mk.injEq, Prod.neg_mk, Prod.mk_add_mk, Prod.mk_eq_zero, one_mul, zero_mul,
    add_zero, zero_add, neg_zero] at hA hA' hB hB' hC hC'
  obtain ⟨hA1, hA2⟩ := hA
  obtain ⟨hA3, hA4⟩ := hA'
  obtain ⟨hB1, hB2⟩ := hB
  obtain ⟨hB3, hB4⟩ := hB'
  obtain ⟨hC1, hC2⟩ := hC
  obtain ⟨hC3, hC4⟩ := hC'

  have hns : ∀ (p : ℕ) (hp : p.Prime) (hpM : p ∣ M),
      ¬ ((ZMod.castHom hpM (ZMod p)) b01 = 0 ∧ (ZMod.castHom hpM (ZMod p)) b10 = 0 ∧
          (ZMod.castHom hpM (ZMod p)) b00 = (ZMod.castHom hpM (ZMod p)) b11) ∧
      ¬ ((ZMod.castHom hpM (ZMod p)) a01 = 0 ∧ (ZMod.castHom hpM (ZMod p)) a10 = 0 ∧
          (ZMod.castHom hpM (ZMod p)) a00 = (ZMod.castHom hpM (ZMod p)) a11) := by
    intro p hp hpM
    haveI : Fact p.Prime := ⟨hp⟩
    set π := ZMod.castHom hpM (ZMod p) with hπ
    have h3 : (3 : ZMod p) ≠ 0 := by
      intro h
      have h' : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at h'
      have : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h'
      subst this
      exact hM hpM
    have m := fun (x y : ZMod M) (h : x = y) => congrArg π h
    refine not_scalar h3 (π a00) (π a01) (π a10) (π a11) (π b00) (π b01) (π b10) (π b11)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simpa only [map_add, map_mul, map_neg, map_one] using m _ _ hA1
    · simpa only [map_add, map_mul, map_zero] using m _ _ hA2
    · simpa only [map_add, map_mul, map_zero] using m _ _ hA3
    · simpa only [map_add, map_mul, map_neg, map_one] using m _ _ hA4
    · simpa only [map_add, map_mul, map_one, map_zero] using m _ _ hB1
    · simpa only [map_add, map_mul, map_zero] using m _ _ hB2
    · simpa only [map_add, map_mul, map_zero] using m _ _ hB3
    · simpa only [map_add, map_mul, map_one, map_zero] using m _ _ hB4
    · simpa only [map_add, map_mul] using m _ _ hC1
    · simpa only [map_add, map_mul] using m _ _ hC2
    · simpa only [map_add, map_mul] using m _ _ hC3
    · simpa only [map_add, map_mul] using m _ _ hC4
  refine ⟨?_, ?_⟩
  · obtain ⟨x, y, hu⟩ := exists_isUnit_Q b00 b01 b10 b11 (fun p hp hpM => (hns p hp hpM).1)
    refine coords_of_isUnit e β (x, y) ?_
    rw [← hβVdef, det_eq_Q βV _ _ hb0 hb1]
    exact hu
  · obtain ⟨x, y, hu⟩ := exists_isUnit_Q a00 a01 a10 a11 (fun p hp hpM => (hns p hp hpM).2)
    refine coords_of_isUnit e α (x, y) ?_
    rw [← hαVdef, det_eq_Q αV _ _ ha0 ha1]
    exact hu

end Assembly

end P2MKcADAPT
p2m_reactivate "P2MW.S_AddCommGroup_exists_torsionBy_coords_of_dicyclic_relations.P2MKcADAPT"

theorem solution
    (M : ℕ) [NeZero M] (hM : ¬ 3 ∣ M) {A : Type*} [AddCommGroup A]
    (e : ZMod M × ZMod M ≃+ Submodule.torsionBy ℤ A M)
    (α β : A →+ A) (hα : ∀ T, α (α T) = -T) (hβ : ∀ T, β (β T) + β T + T = 0)
    (hαβ : ∀ T, α (β T) = β (β (α T))) :
    (∃ P : A, (M : ℤ) • P = 0 ∧ ∀ T : A, (M : ℤ) • T = 0 →
      ∃! c : ZMod M × ZMod M, c.1.val • P + c.2.val • β P = T) ∧
    (∃ P : A, (M : ℤ) • P = 0 ∧ ∀ T : A, (M : ℤ) • T = 0 →
      ∃! c : ZMod M × ZMod M, c.1.val • P + c.2.val • α P = T) :=
  P2MKcADAPT.main hM e α β hα hβ hαβ

end
end S_AddCommGroup_exists_torsionBy_coords_of_dicyclic_relations
end P2MW
export P2MW.S_AddCommGroup_exists_torsionBy_coords_of_dicyclic_relations (solution)
