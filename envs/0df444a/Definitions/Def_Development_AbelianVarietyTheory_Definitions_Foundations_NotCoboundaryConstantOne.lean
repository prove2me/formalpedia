-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NotCoboundaryConstantOne
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_NotCoboundaryConstantOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:31.31382+00:00
-- url     : https://prove2.me/theorems/6a904670-1e31-4e1d-b551-198edb721f09
-- title:
--   Not Coboundary Constant One
-- statement:
--   Definitions and structural lemmas for Not Coboundary Constant One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotCoboundaryConstantOne.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.K5
open Polynomial
variable (p : ℕ) [Fact p.Prime]
abbrev Lau : Type := LaurentSeries ℤ_[p]
abbrev pI : Ideal (Lau p) := Ideal.span {(p : Lau p)}
abbrev O0 : Type := AdicCompletion (pI p) (Lau p)
def qO : O0 p := algebraMap (Lau p) (O0 p) (HahnSeries.single (1 : ℤ) (1 : ℤ_[p]))
def towerIdeal (n : ℕ) : Ideal (Polynomial (Polynomial (O0 p))) :=
  Ideal.span {C (cyclotomic (p ^ n) (O0 p)), X ^ (p ^ n) - C (C (qO p))}
abbrev On (n : ℕ) : Type := Polynomial (Polynomial (O0 p)) ⧸ towerIdeal p n
def xn (n : ℕ) : On p n := Ideal.Quotient.mk _ (C X)
def yn (n : ℕ) : On p n := Ideal.Quotient.mk _ X
def IsDlog (n : ℕ) (w α β : On p n) : Prop :=
  (xn p n * yn p n) • KaehlerDifferential.D (O0 p) (On p n) w =
    (w * xn p n * α) • KaehlerDifferential.D (O0 p) (On p n) (yn p n) +
    (w * yn p n * β) • KaehlerDifferential.D (O0 p) (On p n) (xn p n)
def fPi (n : ℕ) (k l : ℤ) (α β α' β' : On p n) : On p n :=
  α * ((l : On p n) * xn p n + (xn p n - 1) * β') - ((k : On p n) * xn p n + (xn p n - 1) * β) * α'
structure IsClo (Ω : Type*) [Field Ω] [Algebra (O0 p) Ω] : Prop where
  inj : Function.Injective (algebraMap (O0 p) Ω)
  alg : Algebra.IsAlgebraic (O0 p) Ω
  clo : IsAlgClosed Ω
structure Tower (Ω : Type*) [Field Ω] [Algebra (O0 p) Ω] where
  ζ : ℕ → Ω
  qq : ℕ → Ω
  prim : ∀ n, IsPrimitiveRoot (ζ n) (p ^ n)
  ζpow : ∀ n, ζ (n + 1) ^ p = ζ n
  q0 : qq 0 = algebraMap (O0 p) Ω (qO p)
  qpow : ∀ n, qq (n + 1) ^ p = qq n
abbrev Gal (Ω : Type*) [Field Ω] [Algebra (O0 p) Ω] : Type _ := Ω ≃ₐ[O0 p] Ω
variable {p}
variable {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]
def Gn (T : Tower p Ω) (n : ℕ) : Subgroup (Gal p Ω) :=
  MulAction.stabilizer (Gal p Ω) (T.ζ n) ⊓ MulAction.stabilizer (Gal p Ω) (T.qq n)
def IsEmb (T : Tower p Ω) (n : ℕ) (ι : On p n →ₐ[O0 p] Ω) : Prop :=
  ι (xn p n) = T.ζ n ∧ ι (yn p n) = T.qq n
variable (p) in

def IsInt (x : Ω) : Prop := IsIntegral (O0 p) x
variable (p) in

def Cong (k : ℕ) (x y : Ω) : Prop := ∃ z : Ω, IsInt p z ∧ x - y = (p : Ω) ^ k * z
def IsKum (T : Tower p Ω) (n : ℕ) (H : Subgroup (Gal p Ω)) (r : Ω) (a : Gal p Ω → ZMod (p ^ n)) : Prop :=
  ∀ g ∈ H, g r = T.ζ n ^ (a g).val * r
def Gms (T : Tower p Ω) (m s : ℕ) : Subgroup (Gal p Ω) :=
  MulAction.stabilizer (Gal p Ω) (T.ζ m) ⊓ MulAction.stabilizer (Gal p Ω) (T.qq s)
variable (p) in

def IsAlgZp (x : Ω) : Prop :=
  ∃ P : Polynomial ℤ_[p], P ≠ 0 ∧ Polynomial.aeval x (P.map (algebraMap ℤ_[p] (O0 p))) = 0
variable (p) in

def Ggeo (Ω : Type*) [Field Ω] [Algebra (O0 p) Ω] : Subgroup (Gal p Ω) where
  carrier := {g | ∀ x : Ω, IsAlgZp p x → g x = x}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {a b} ha hb x hx => by
    show a (b x) = x
    rw [hb x hx, ha x hx]
  inv_mem' := fun {a} ha x hx => by
    show a.symm x = x
    conv_lhs => rw [← ha x hx]
    exact a.symm_apply_apply x
def LocallyConstantOneCochain (k : ℕ) (w : Gal p Ω → Ω) : Prop :=
  (∀ g, IsInt p (w g)) ∧ ∀ g, ∃ S : Finset Ω, ∀ h : Gal p Ω, (∀ x ∈ S, h x = g x) → Cong p k (w h) (w g)
def Cob2 (k : ℕ) (H : Subgroup (Gal p Ω)) (ξ : Gal p Ω → Gal p Ω → Ω) : Prop :=
  ∃ w : Gal p Ω → Ω, LocallyConstantOneCochain k w ∧ ∀ g ∈ H, ∀ h ∈ H, Cong p k (ξ g h) (g (w h) - w (g * h) + w g)
def Cob1 (k : ℕ) (H : Subgroup (Gal p Ω)) (c : Gal p Ω → Ω) : Prop :=
  ∃ x : Ω, IsInt p x ∧ ∀ g ∈ H, Cong p k (c g) (g x - x)
end GlobalTheory.K5
namespace GlobalTheory.K5.Basic
open Polynomial
section Ring
variable (p : ℕ) [hp : Fact p.Prime]
theorem natCast_pow_dvd_iff (k : ℕ) (f : Lau p) :
    (p : Lau p) ^ k ∣ f ↔ ∀ n, (p : ℤ_[p]) ^ k ∣ f.coeff n := by
  have hc : (p : Lau p) ^ k = HahnSeries.C ((p : ℤ_[p]) ^ k) := by rw [map_pow, map_natCast]
  have hne : (p : ℤ_[p]) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  constructor
  · rintro ⟨g, rfl⟩ n
    rw [hc, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul]
    exact Dvd.intro _ rfl
  · intro h
    choose c hcn using h
    refine ⟨⟨c, f.isPWO_support'.mono ?_⟩, ?_⟩
    · intro n hn
      simp only [Function.mem_support] at hn ⊢
      rw [hcn n]
      exact mul_ne_zero hne hn
    · ext n
      rw [hc, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, hcn n]
      rfl
theorem dvd_iff_map (f : Lau p) :
    (p : Lau p) ∣ f ↔ f.map (PadicInt.toZMod (p := p)).toNonUnitalRingHom = 0 := by
  have := natCast_pow_dvd_iff p 1 f
  simp only [pow_one] at this
  rw [this]
  have key : ∀ c : ℤ_[p], (p : ℤ_[p]) ∣ c ↔ PadicInt.toZMod c = 0 := by
    intro c
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
      Ideal.mem_span_singleton]
  constructor
  · intro h; ext n; exact (key _).1 (h n)
  · intro h n
    have := congrArg (fun s => HahnSeries.coeff s n) h
    exact (key _).2 this
theorem prime_lau : Prime (p : Lau p) := by
  refine ⟨?_, ?_, ?_⟩
  · have hc : (p : Lau p) = HahnSeries.C (p : ℤ_[p]) := by simp
    rw [hc]
    exact HahnSeries.C_ne_zero (by exact_mod_cast hp.out.ne_zero)
  · intro hu
    have h1 := (dvd_iff_map p 1).1 hu.dvd
    have := congrArg (fun s => HahnSeries.coeff s 0) h1
    have h2 : PadicInt.toZMod (p := p) (HahnSeries.coeff (1 : Lau p) 0) = 0 := this
    simp at h2
  · intro a b h
    rw [dvd_iff_map, HahnSeries.map_mul] at h
    rw [dvd_iff_map, dvd_iff_map]
    exact mul_eq_zero.1 h
theorem mem_pI_pow (k : ℕ) (f : Lau p) : f ∈ pI p ^ k ↔ (p : Lau p) ^ k ∣ f := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
theorem seq_sub_dvd (x : AdicCompletion.AdicCauchySequence (pI p) (Lau p)) {m n : ℕ} (h : m ≤ n) :
    (p : Lau p) ^ m ∣ x.1 n - x.1 m := by
  have h1 := AdicCompletion.AdicCauchySequence.mk_eq_mk h x
  rw [Submodule.Quotient.eq] at h1
  rw [← mem_pI_pow]
  simpa using h1
theorem exists_not_dvd (x : AdicCompletion.AdicCauchySequence (pI p) (Lau p))
    (hx : AdicCompletion.mk (pI p) (Lau p) x ≠ 0) :
    ∃ a, ∀ n, a ≤ n → ¬ (p : Lau p) ^ a ∣ x.1 n := by
  by_contra hcon
  push_neg at hcon
  apply hx
  apply AdicCompletion.ext_evalₐ
  intro a
  obtain ⟨n, hn, hd⟩ := hcon a
  rw [AdicCompletion.evalₐ_mk, map_zero, Ideal.Quotient.eq_zero_iff_mem, mem_pI_pow]
  have := dvd_sub hd (seq_sub_dvd p x hn)
  simpa using this
instance charZero_completed_ring : CharZero (O0 p) := by
  refine charZero_of_inj_zero ?_
  intro n hn
  have h1 := congrArg (AdicCompletion.evalₐ (pI p) n) hn
  rw [map_natCast, map_zero, ← map_natCast (Ideal.Quotient.mk (pI p ^ n)),
    Ideal.Quotient.eq_zero_iff_mem, mem_pI_pow, natCast_pow_dvd_iff] at h1
  have h2 := h1 0
  have hc : (n : Lau p) = HahnSeries.C (n : ℤ_[p]) := by rw [map_natCast]
  rw [hc, HahnSeries.C_apply, HahnSeries.coeff_single_same] at h2
  have h3 : ((p : ℤ) ^ n) ∣ (n : ℤ) :=
    (PadicInt.pow_p_dvd_int_iff n (n : ℤ)).1 (by exact_mod_cast h2)
  have h4 : p ^ n ∣ n := by exact_mod_cast h3
  exact Nat.eq_zero_of_dvd_of_lt h4 (Nat.lt_pow_self hp.out.one_lt)
instance isDomain_completed_ring : IsDomain (O0 p) := by
  haveI : NoZeroDivisors (O0 p) := ⟨by
    intro x y hxy
    by_contra hcon
    push_neg at hcon
    obtain ⟨hx, hy⟩ := hcon
    obtain ⟨x, rfl⟩ := AdicCompletion.mk_surjective (pI p) (Lau p) x
    obtain ⟨y, rfl⟩ := AdicCompletion.mk_surjective (pI p) (Lau p) y
    obtain ⟨a, ha⟩ := exists_not_dvd p x hx
    obtain ⟨b, hb⟩ := exists_not_dvd p y hy
    have h1 := congrArg (AdicCompletion.evalₐ (pI p) (a + b)) hxy
    rw [map_mul, map_zero, AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem, mem_pI_pow, pow_dvd_iff_le_emultiplicity,
      emultiplicity_mul (prime_lau p)] at h1
    have h2 := ha (a + b) (Nat.le_add_right _ _)
    have h3 := hb (a + b) (Nat.le_add_left _ _)
    rw [pow_dvd_iff_le_emultiplicity, not_le] at h2 h3
    have h4 := ENat.add_lt_add h2 h3
    rw [← Nat.cast_add] at h4
    exact absurd h1 (not_le.2 h4)⟩
  exact NoZeroDivisors.to_isDomain _
end Ring
section Field
variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]
end Field
end GlobalTheory.K5.Basic


