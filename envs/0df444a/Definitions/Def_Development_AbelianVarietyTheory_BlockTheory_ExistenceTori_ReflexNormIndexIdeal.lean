-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ReflexNormIndexIdeal
-- name    : Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ReflexNormIndexIdeal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:45:20.417975+00:00
-- url     : https://prove2.me/theorems/ade542db-f13d-4e55-9a76-cd8ef9464b48
-- title:
--   Reflex Norm Index Ideal
-- statement:
--   Definitions and structural lemmas for Reflex Norm Index Ideal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/ReflexNormIndexIdeal.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_AdmissibleHarmonicLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
def indexIdeal (L' L : Submodule (𝓞 E) (Fin n → E)) : Ideal (𝓞 E) :=
  Ideal.span {a | ∃ g : (Fin n → E) →ₗ[E] (Fin n → E), (∀ x ∈ L', g x ∈ L) ∧ (a : E) = LinearMap.det g}
def latIdeal (Λ : Lat E n) : Ideal (𝓞 E) := indexIdeal Λ.L Λ.inter
def latNorm (Λ : Lat E n) (r : ℕ) : ℕ := Ideal.absNorm (latIdeal Λ) ^ r
omit [IsCMField E] in
theorem latIdeal_ne_bot (Λ : Lat E n) : latIdeal Λ ≠ ⊥ := by
  classical
  obtain ⟨S, hS⟩ := Λ.fg
  obtain ⟨k, hk⟩ := IsLocalization.exist_integer_multiples (𝓞 E)⁰ (S ×ˢ (Finset.univ : Finset (Fin n)))
    (fun t => (t.1 t.2 : E))
  have hL : ∀ x ∈ Λ.L, (k : 𝓞 E) • x ∈ stdMod E n := by
    have : Λ.L ≤ (stdMod E n).comap (LinearMap.lsmul (𝓞 E) (Fin n → E) (k : 𝓞 E)) := by
      rw [← hS, Submodule.span_le]
      intro x hx
      refine mem_stdMod.2 fun j => ?_
      obtain ⟨a, ha⟩ := hk (x, j) (by simpa using hx)
      exact ⟨a, ha⟩
    exact fun x hx => this hx
  intro h
  have hm : (k : 𝓞 E) ^ n ∈ latIdeal Λ := by
    refine Ideal.subset_span ⟨((k : 𝓞 E) : E) • LinearMap.id, fun x hx => ⟨hL x hx, Λ.L.smul_mem _ hx⟩, ?_⟩
    rw [LinearMap.det_smul]
    simp
  rw [h, Ideal.mem_bot] at hm
  exact pow_ne_zero n (nonZeroDivisors.coe_ne_zero k) hm
variable {H : Host E} (Dw : Datum H) {l : Level H} (c : Coeff l)
def reflexNorm (γ : E) : c.F := ∏ σ : E →+* ℂ, embF c σ γ ^ Dw.mult σ
def reflexIdeal (𝔞 : Ideal (𝓞 E)) : Ideal (𝓞 c.F) :=
  ∏ σ : E →+* ℂ, 𝔞.map (RingOfIntegers.mapRingHom (embF c σ)) ^ Dw.mult σ
def IsBe (𝔞 : Ideal (𝓞 E)) (β : c.F) : Prop :=
  (∃ b : 𝓞 c.F, (b : c.F) = β ∧ Ideal.span {b} = reflexIdeal Dw c 𝔞) ∧
    ∀ s : c.F →+* ℂ, ‖s β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ (Dw.p + Dw.q)
def IsBeLat (Λ : Lat E n) (β : c.F) : Prop := IsBe Dw c (latIdeal Λ) β
def ReflexLe : Prop := ∀ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ → ∃ β : c.F, IsBe Dw c 𝔞 β
def ReflexRoots : Prop :=
  ∀ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ → ∃ (h : ℕ) (γ : 𝓞 E) (ψ : c.F),
    0 < h ∧ 𝔞 ^ h = Ideal.span {γ} ∧ ψ ^ h = reflexNorm Dw c (γ : E)
def ReflexBasis : Prop :=
  ∃ (m : ℕ) (𝔠 : Fin m → (Ideal (𝓞 E))⁰) (h : Fin m → ℕ) (γ : Fin m → 𝓞 E) (ψ : Fin m → c.F),
    (∀ x : ClassGroup (𝓞 E), ∃! a : Fin m → ℕ, (∀ i, a i < h i) ∧ x = ∏ i, ClassGroup.mk0 (𝔠 i) ^ a i) ∧
    (∀ i, (𝔠 i : Ideal (𝓞 E)) ^ h i = Ideal.span {γ i}) ∧
    ∀ i, ψ i ^ h i = reflexNorm Dw c (γ i : E)
variable {Dw c}
open scoped Classical in

def beIdeal (hK : ReflexLe Dw c) (𝔞 : Ideal (𝓞 E)) (h𝔞 : 𝔞 ≠ ⊥) : c.F :=
  if 𝔞 = ⊤ then 1 else (hK 𝔞 h𝔞).choose
def be (hK : ReflexLe Dw c) (Λ : Lat E n) : c.F := beIdeal hK (latIdeal Λ) (latIdeal_ne_bot Λ)
variable (Dw c)
def BeExists : Prop :=
  ReflexBasis Dw c → ∀ (n : ℕ) (Λ : Lat E n), Λ.InGenus → ∃ β : c.F, IsBeLat Dw c Λ β
def ReflexForms : Prop := (ReflexBasis Dw c → ReflexLe Dw c) ∧ (ReflexRoots Dw c ↔ ReflexLe Dw c)
def ReflexFieldExists : Prop :=
  ∃ c' : Coeff l, c.F ≤ c'.F ∧ Module.finrank ℚ c'.F ≤ Module.finrank ℚ c.F * classNumber E ∧ ReflexBasis Dw c'
def BeUnique : Prop :=
  ∀ (𝔞 : Ideal (𝓞 E)) (β β' : c.F), 𝔞 ≠ ⊥ → IsBe Dw c 𝔞 β → IsBe Dw c 𝔞 β' →
    ∃ ζ : c.F, IsOfFinOrder ζ ∧ β' = ζ * β
def BePrincipal : Prop := ∀ γ : 𝓞 E, γ ≠ 0 → IsBe Dw c (Ideal.span {γ}) (reflexNorm Dw c (γ : E))
def BeUnitAt : Prop :=
  ∀ (n : ℕ) (Λ : Lat E n) (ℓ : ℕ) (b : 𝓞 c.F), ℓ.Prime → Λ.StdAt ℓ → IsBeLat Dw c Λ (b : c.F) →
    IsCoprime b (ℓ : 𝓞 c.F)
def LatIdealClaim (H : Host E) : Prop :=
  ∀ (n : ℕ) (Λ : Lat E n),
    Ideal.absNorm (latIdeal Λ) = Λ.inter.toAddSubgroup.relIndex Λ.L.toAddSubgroup ∧
    (Λ.SelfDual → indexIdeal (stdMod E n) Λ.inter = (latIdeal Λ).map (H.bar : 𝓞 E →+* 𝓞 E))
end GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal


