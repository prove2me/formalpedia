-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_TwChrOne
-- name    : Formalism_PeriodIntegrals_TwChrOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:10:04.524455+00:00
-- url     : https://prove2.me/theorems/12d7958a-153a-459a-bb02-a6af2aefa8e4
-- title:
--   Tw Chr One
-- statement:
--   Definitions and structural lemmas for Tw Chr One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/TwChrOne.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
namespace PI.TwChrOne
section LocS
variable {R : Type*} [CommRing R]
def locS {W : Type*} [AddCommGroup W] [Module R W] (S : Submonoid R) (L : Submodule R W) :
    Submodule R W where
  carrier := {x | ∃ s ∈ S, s • x ∈ L}
  zero_mem' := ⟨1, S.one_mem, by simp⟩
  add_mem' := by
    rintro x y ⟨s, hs, hx⟩ ⟨t, ht, hy⟩
    refine ⟨s * t, S.mul_mem hs ht, ?_⟩
    have e : (s * t) • (x + y) = t • (s • x) + s • (t • y) := by
      rw [smul_add, mul_smul, smul_comm s t x, mul_smul]
    rw [e]
    exact L.add_mem (L.smul_mem t hx) (L.smul_mem s hy)
  smul_mem' := by
    rintro r x ⟨s, hs, hx⟩
    refine ⟨s, hs, ?_⟩
    rw [smul_comm]
    exact L.smul_mem r hx
def localization₂ {W : Type*} [AddCommGroup W] [Module R W] (p : Ideal R) [p.IsPrime] (L : Submodule R W) :
    Submodule R W :=
  locS p.primeCompl L
end LocS
abbrev Sp (E : Type) (n : ℕ) : Type := Fin n → E
section Red
variable {E : Type} [Field E] [NumberField E]
def redP (P : HeightOneSpectrum (𝓞 E)) (a : E) : 𝓞 E ⧸ P.asIdeal :=
  open Classical in
  if h : ∃ c : 𝓞 E ⧸ P.asIdeal, ∃ r s : 𝓞 E, s ∉ P.asIdeal ∧ algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r ∧
      Ideal.Quotient.mk P.asIdeal s * c = Ideal.Quotient.mk P.asIdeal r
  then h.choose else 0
def IntAt (P : HeightOneSpectrum (𝓞 E)) (a : E) : Prop :=
  ∃ r s : 𝓞 E, s ∉ P.asIdeal ∧ algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r
end Red
section Deco
variable (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ)
def stdLat : Submodule (𝓞 E) (Sp E n) := Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)
end Deco
section Frames
variable (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ)
def stabL (M : Submodule (𝓞 E) (Sp E n)) : Subgroup (Sp E n ≃ₗ[E] Sp E n) where
  carrier := {c | ∀ x, c x ∈ M ↔ x ∈ M}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := fun {a b} ha hb x => (ha (b x)).trans (hb x)
  inv_mem' := fun {a} ha x => by
    have h := ha (a⁻¹ x)
    rw [show a (a⁻¹ x) = x from LinearEquiv.apply_symm_apply a x] at h
    exact h.symm
def stdAt (P : HeightOneSpectrum (𝓞 E)) : Submodule (𝓞 E) (Sp E n) := localization₂ P.asIdeal (stdLat E n)
def GLint (P : HeightOneSpectrum (𝓞 E)) : Subgroup (Sp E n ≃ₗ[E] Sp E n) := stabL E n (stdAt E n P)
end Frames
namespace Loc
section Groups
variable (k : Type) [CommRing k] (n c : ℕ)
def atN {k : Type} [CommRing k] {N : ℕ} (v : Fin N → k) (i : ℕ) : k := if h : i < N then v ⟨i, h⟩ else 0
def eN (N i : ℕ) : Fin N → k := fun l => if l.1 = i then 1 else 0
def supp (N : ℕ) (s : Set ℕ) : Submodule k (Fin N → k) where
  carrier := {v | ∀ l : Fin N, l.1 ∉ s → v l = 0}
  add_mem' := fun {a b} ha hb l hl => by simp [ha l hl, hb l hl]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun r a ha l hl => by simp [ha l hl]
def Ufl (i : ℕ) : Submodule k (Fin (n + c) → k) := supp k (n + c) {l | l < n + i}
def inX : (Fin n → k) →ₗ[k] (Fin (n + c) → k) :=
  LinearMap.pi fun l => if h : l.1 < n then LinearMap.proj ⟨l.1, h⟩ else 0
def R1cond (r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) : Prop :=
  (∀ i, ∀ v ∈ Ufl k n c i, r v ∈ Ufl k n c i) ∧ r (eN k (n + c) n) = eN k (n + c) n ∧
    ∀ i, r (eN k (n + c) (n + i)) - eN k (n + c) (n + i) ∈ Ufl k n c i
variable {k n c} in
theorem R1cond.mul {r s : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : R1cond k n c r) (hs : R1cond k n c s) :
    R1cond k n c (r * s) := by
  refine ⟨fun i v hv => hr.1 i _ (hs.1 i v hv), ?_, fun i => ?_⟩
  · show r (s _) = _
    rw [hs.2.1, hr.2.1]
  · have h1 : (r * s) (eN k (n + c) (n + i)) - eN k (n + c) (n + i) =
        r (s (eN k (n + c) (n + i)) - eN k (n + c) (n + i)) + (r (eN k (n + c) (n + i)) - eN k (n + c) (n + i)) := by
      rw [map_sub]
      show r (s _) - _ = _
      abel
    rw [h1]
    exact add_mem (hr.1 i _ (hs.2.2 i)) (hr.2.2 i)
theorem R1cond_one : R1cond k n c 1 :=
  ⟨fun _ _ hv => hv, rfl, fun i => by
    show eN k (n + c) (n + i) - eN k (n + c) (n + i) ∈ _
    rw [sub_self]
    exact zero_mem _⟩
def R1 : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) where
  carrier := {r | R1cond k n c r ∧ R1cond k n c r⁻¹}
  one_mem' := ⟨R1cond_one k n c, by rw [inv_one]; exact R1cond_one k n c⟩
  mul_mem' := fun {a b} ha hb => ⟨ha.1.mul hb.1, by rw [mul_inv_rev]; exact hb.2.mul ha.2⟩
  inv_mem' := fun {a} ha => ⟨ha.2, by rw [inv_inv]; exact ha.1⟩
def fixX : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) where
  carrier := {r | ∀ x, r (inX k n c x) = inX k n c x}
  one_mem' := fun _ => rfl
  mul_mem' := fun {a b} ha hb x => by
    show a (b _) = _
    rw [hb, ha]
  inv_mem' := fun {a} ha x => by
    have h := ha x
    show a.symm _ = _
    rw [LinearEquiv.symm_apply_eq, h]
def N1 : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) := R1 k n c ⊓ fixX k n c
variable {k n c}
def n1Arg (r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) : k :=
  ∑ i ∈ Finset.range (c - 1), atN (r (eN k (n + c) (n + i + 1))) (n + i)
def Cbe (J : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k))) (h : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) :
    Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) :=
  R1 k n c ⊓ J.comap (MulAut.conj h⁻¹).toMonoidHom
def prX (C : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k))) : Subgroup ((Fin n → k) ≃ₗ[k] (Fin n → k)) where
  carrier := {g | ∃ r ∈ C, ∀ x, r (inX k n c x) = inX k n c (g x)}
  one_mem' := ⟨1, C.one_mem, fun _ => rfl⟩
  mul_mem' := by
    rintro a b ⟨r, hr, h1⟩ ⟨s, hs, h2⟩
    refine ⟨r * s, C.mul_mem hr hs, fun x => ?_⟩
    show r (s _) = _
    rw [h2, h1]
    rfl
  inv_mem' := by
    rintro a ⟨r, hr, h1⟩
    refine ⟨r⁻¹, C.inv_mem hr, fun x => ?_⟩
    show r.symm _ = _
    rw [LinearEquiv.symm_apply_eq, h1]
    show _ = inX k n c (a (a.symm x))
    rw [LinearEquiv.apply_symm_apply]
def volN (K : Type) [Field K] (C N1O : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k))) : K :=
  ((N1O.relIndex (C ⊓ N1 k n c) : ℕ) : K) / (((C ⊓ N1 k n c).relIndex N1O : ℕ) : K)
end Groups
end Loc
abbrev HomE (E : Type) [Field E] (a b : ℕ) : Type := Sp E a →ₗ[E] Sp E b
namespace LocE
open Loc
variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ)
def vP (a : E) : ℤ := Classical.epsilon fun z : ℤ => IsUnit (redP P (a / (q : E) ^ z))
variable {P} in
open Classical in

def unitV (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E) : K := if h : IsUnit (redP P a) then ((χ h.unit : Kˣ) : K) else 0
variable {P} in

def locChar (cq : K) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E) : K := cq ^ vP P q a * unitV χ (a / (q : E) ^ vP P q a)
def sclLat (N : ℕ) (e : ℕ → ℤ) : Submodule (𝓞 E) (Sp E N) :=
  (stdAt E N P).comap
    ((LinearMap.pi fun l : Fin N => ((q : E) ^ e l.1)⁻¹ • (LinearMap.proj l : Sp E N →ₗ[E] E)).restrictScalars (𝓞 E))
def fIdx (k₀ c n s : ℕ) : ℕ := if s < k₀ then s else if s < k₀ + c then n + (s - k₀) else s - c
def fPos (k₀ c n l : ℕ) : ℕ := if l < k₀ then l else if l < n then l + c else k₀ + (l - n)
def scE (n : ℕ) (ex : ℕ → ℕ) (l : ℕ) : ℤ := if l < n then 0 else (ex (l - n) : ℤ)
def lamY (n c : ℕ) (ex : ℕ → ℕ) : Submodule (𝓞 E) (Sp E (n + c)) := sclLat P q (n + c) (scE n ex)
section AtQ
variable (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
def parL (kj n c : ℕ) : Submodule (𝓞 E) (Sp E (n + c)) := sclLat P q (n + c) fun l => if kj ≤ l ∧ l < n then 1 else 0
def JQ (kj n c : ℕ) : Subgroup (Sp E (n + c) ≃ₗ[E] Sp E (n + c)) :=
  stabL E (n + c) (stdAt E (n + c) P) ⊓ stabL E (n + c) (parL P q kj n c)
variable {P}
def lamQB (kj n : ℕ) {N : ℕ} (h : HomE E N N) : K :=
  (unitV ξ (Matrix.det (Matrix.of fun s t : Fin (n - kj) => atN (h (eN E N (kj + t.1))) (kj + s.1))))⁻¹
end AtQ
end LocE
section Target
variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K]
def ChiL (P : HeightOneSpectrum (𝓞 E)) (psi : E → K) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (kj N c : ℕ)
    (h r : Sp E (N + c) ≃ₗ[E] Sp E (N + c)) : K :=
  (psi (Loc.n1Arg r))⁻¹ * LocE.lamQB ξ kj N ((h⁻¹ * r * h : Sp E (N + c) ≃ₗ[E] Sp E (N + c))).toLinearMap
def ChrOkL (P : HeightOneSpectrum (𝓞 E)) (psi : E → K) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (kj N c : ℕ)
    (h : Sp E (N + c) ≃ₗ[E] Sp E (N + c)) : Prop :=
  (∀ r ∈ Loc.Cbe (LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c) h, ChiL P psi ξ kj N c h r ≠ 0) ∧
  ∀ r ∈ Loc.Cbe (LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c) h, ∀ r' ∈ Loc.Cbe (LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c) h,
    ∀ r'' ∈ Loc.Cbe (LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c) h,
    (∀ x, r'' (Loc.inX E N c x) = r (r' (Loc.inX E N c x))) →
      ChiL P psi ξ kj N c h r'' = ChiL P psi ξ kj N c h r * ChiL P psi ξ kj N c h r'
end Target
def TwChrOne : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)) (psi : E → K)
    (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (kj N c : ℕ), (∀ x, IntAt P x → psi x = 1) → ChrOkL P psi ξ kj N c 1
end PI.TwChrOne


