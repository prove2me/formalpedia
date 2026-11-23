-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
-- name    : Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:52:33.418809+00:00
-- url     : https://prove2.me/theorems/f2499454-02d8-4e3c-b2d8-49d6112a5ab8
-- title:
--   Conjugate Order Data
-- statement:
--   Definitions and structural lemmas for Conjugate Order Data, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/ConjugateOrderData.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Theorems.Thm_GlobalTheory_CMVal_algebraMap_mem_orderC
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub


set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal
namespace GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
section Val
variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type} [Field K] [Algebra O K] [IsFractionRing O K]
def ord_vw (x : K) : ℤ := -WithZero.log ((IsDiscreteValuationRing.maximalIdeal O).valuation K x)
open Classical in

def val_vp (l : ℕ) (x : K) : WithTop ℚ :=
  if x = 0 then ⊤ else (((ord_vw O x : ℚ) / (ord_vw O (l : K) : ℚ) : ℚ) : WithTop ℚ)
end Val
section Const
variable {E : Type} [Field E] [NumberField E]
def diffExp_vp (l : ℕ) (P : HeightOneSpectrum (𝓞 E)) : ℚ :=
  (multiplicity P.asIdeal (differentIdeal ℤ (𝓞 E)) : ℚ) / (multiplicity P.asIdeal (Ideal.span {(l : 𝓞 E)}) : ℚ)
def condExp (𝔣 : Ideal (OF E)) (l : ℕ) : ℕ :=
  sSup (expIn 𝔣 '' {v : HeightOneSpectrum (OF E) | (l : OF E) ∈ v.asIdeal})
open Classical in

def cNum_vp (𝔣 : Ideal (OF E)) (l : ℕ) (P : HeightOneSpectrum (𝓞 E)) : ℚ :=
  if ∃ v : HeightOneSpectrum (OF E), v.asIdeal ∣ 𝔣 ∧ (l : OF E) ∈ v.asIdeal then (condExp 𝔣 l : ℚ) else diffExp_vp l P
end Const
section Lin
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K]
def bar (σ : E →+* K) : E →+* K := σ.comp (IsCMField.complexConj E : E →+* E)
def IsCMTypeIn {I : Type} (φ : I → E →+* K) : Prop := ∀ σ : E →+* K, ∃! i, σ = φ i ∨ σ = bar (φ i)
def coordAt (O : Type) [CommRing O] [Algebra O K] (c : Ideal (OF E)) (σ : E →+* K) : orderC c ⊗[ℤ] O →ₐ[ℤ] K :=
  Algebra.TensorProduct.productMap (σ.comp (orderC c).subtype).toIntAlgHom (algebraMap O K).toIntAlgHom
open Classical in

def ClearsIdem (K : Type) [Field K] [Algebra O K] (c : Ideal (OF E)) (D : O) : Prop :=
  ∀ σ : E →+* K, ∃ t : orderC c ⊗[ℤ] O, ∀ σ' : E →+* K, coordAt O c σ' t = if σ' = σ then algebraMap O K D else 0
variable {H : Type} [AddCommGroup H] [Module O H] {c : Ideal (OF E)}
def eigK (ρ : orderC c →+* Module.End O H) (σ : E →+* K) : Submodule K (K ⊗[O] H) :=
  ⨅ a : orderC c, Module.End.eigenspace ((ρ a).baseChange K) (σ a)
def inK (K : Type) [Field K] [Algebra O K] (H : Type) [AddCommGroup H] [Module O H] : H →ₗ[O] K ⊗[O] H :=
  TensorProduct.mk O K H 1
def eigLat (ρ : orderC c →+* Module.End O H) (σ : E →+* K) : Submodule O H :=
  ((eigK ρ σ).restrictScalars O).comap (inK K H)
def IsSat (M : Submodule O H) : Prop := ∀ (x : O) (h : H), x ≠ 0 → x • h ∈ M → h ∈ M
def ofF (c : Ideal (OF E)) (a : OF E) : orderC c := ⟨algebraMap (OF E) E a, algebraMap_mem_orderC c a⟩
def IsCMLattice {I : Type} (φ : I → E →+* K) (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H)
    (B : LinearMap.BilinForm O H) : Prop :=
  Module.Free O H ∧ Module.Finite O H ∧ Module.finrank O H = Module.finrank ℚ E ∧
  (∀ σ : E →+* K, Module.finrank K (eigK ρ σ) = 1) ∧
  IsSat Fil ∧ Fil.baseChange K = ⨆ i, eigK ρ (φ i) ∧
  Function.Bijective B ∧ B.IsAlt ∧
  ∀ a b : orderC c, (b : E) = IsCMField.complexConj E a → ∀ h h' : H, B (ρ a h) h' = B h (ρ b h')
def IsGens {I : Type} (φ : I → E →+* K) (ρ : orderC c →+* Module.End O H) (e f : I → H) : Prop :=
  ∀ i, eigLat ρ (φ i) = O ∙ e i ∧ eigLat ρ (bar (φ i)) = O ∙ f i
def IsLower (ρ : orderC c →+* Module.End O H) (τ : E →+* K) (e f : H) (N : Module.End K (K ⊗[O] H)) : Prop :=
  N (inK K H e) = inK K H f ∧ ∀ σ : E →+* K, σ ≠ τ → ∀ x ∈ eigK ρ σ, N x = 0
def IsScaledRestr (D : O) (N : Module.End K (K ⊗[O] H)) (M : Module.End O H) : Prop :=
  ∀ h : H, inK K H (M h) = algebraMap O K D • N (inK K H h)
end Lin
def lPrime (l : ℕ) : ℕ := if l = 2 then 4 else l
def lPrimeExp (l : ℕ) : ℕ := if l = 2 then 2 else 1
def nilPart {O : Type} [CommRing O] {H : Type} [AddCommGroup H] [Module O H] {I : Type} [Fintype I] (l : ℕ)
    (M : I → Module.End O H) (R : Type) [CommRing R] [Algebra O R] (t : I → R) : Module.End R (R ⊗[O] H) :=
  (lPrime l : R) • ∑ i, t i • (M i).baseChange R
def ElementD : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (𝔣 : Ideal (OF E)), IsBaseCond 𝔣 →
  ∀ (l : ℕ), l.Prime →
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K]
    [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E →
    (∃ D : O, (∀ P : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ P.asIdeal →
        val_vp O l (algebraMap O K D) = (cNum_vp 𝔣 l P : ℚ)) ∧ ClearsIdem K 𝔣 D) ∧
    ∀ Q : Finset (HeightOneSpectrum (OF E)), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
      ∀ D : O, ClearsIdem K (condQ 𝔣 Q) D ↔ ClearsIdem K 𝔣 D
section Steps
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type} [Field K] [Algebra O K] [IsFractionRing O K]
variable {H : Type} [AddCommGroup H] [Module O H] {c : Ideal (OF E)} {I : Type} [Fintype I]
open Classical in

def EigenClaims (φ : I → E →+* K) (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H)
    (D : O) : Prop :=
  DirectSum.IsInternal (fun σ : E →+* K => eigK ρ σ) ∧
  (∀ σ : E →+* K, IsSat (eigLat ρ σ) ∧ (∃ g : H, g ≠ 0 ∧ eigLat ρ σ = O ∙ g) ∧
    Module.Free O (eigLat ρ σ) ∧ Module.finrank O (eigLat ρ σ) = 1 ∧ ∃ C : Submodule O H, IsCompl (eigLat ρ σ) C) ∧
  (iSupIndep (fun σ : E →+* K => eigLat ρ σ) ∧ ∀ h : H, D • h ∈ ⨆ σ : E →+* K, eigLat ρ σ) ∧
  (∀ i, Fil ⊓ eigLat ρ (φ i) = eigLat ρ (φ i)) ∧
  ∀ σ σ' : E →+* K, σ' ≠ bar σ → ∀ x ∈ eigK ρ σ, ∀ y ∈ eigK ρ σ', B.baseChange K x y = 0
def LowerClaims (l : ℕ) (φ : I → E →+* K) (ρ : orderC c →+* Module.End O H) (B : LinearMap.BilinForm O H) (D : O)
    (e f : I → H) : Prop :=
  (∀ i, ∃! N, IsLower ρ (φ i) (e i) (f i) N) ∧
  ∀ N : I → Module.End K (K ⊗[O] H), (∀ i, IsLower ρ (φ i) (e i) (f i) (N i)) →
    (∀ i, ∃! M : Module.End O H, IsScaledRestr D (N i) M) ∧
    (∀ i (a : OF E), Commute (N i) ((ρ (ofF c a)).baseChange K)) ∧
    (∀ i j, N i * N j = 0) ∧
    (∀ i x y, B.baseChange K (N i x) y + B.baseChange K x (N i y) = 0) ∧
    (∀ i j x y, B.baseChange K (N i x) (N j y) = 0) ∧
    ∀ M : I → Module.End O H, (∀ i, IsScaledRestr D (N i) (M i)) →
      ∀ (R : Type) [CommRing R] [Algebra O R] (t : I → R),
        (∀ x : R ⊗[O] H, ∃ y : R ⊗[O] H, (1 + nilPart l M R t) x = x + (lPrime l : R) • y) ∧
        ((1 + nilPart l M R t) * (1 - nilPart l M R t) = 1 ∧ (1 - nilPart l M R t) * (1 + nilPart l M R t) = 1) ∧
        (∀ a : OF E, Commute (1 + nilPart l M R t) ((ρ (ofF c a)).baseChange R)) ∧
        ∀ x y : R ⊗[O] H, B.baseChange R ((1 + nilPart l M R t) x) ((1 + nilPart l M R t) y) = B.baseChange R x y
def DetClaims (K : Type) [Field K] [Algebra O K] [IsFractionRing O K] (l : ℕ) (Fil : Submodule O H) (D : O) (e : I → H) :
    Prop :=
  Module.Free O Fil ∧ Module.finrank O Fil = Fintype.card I ∧ (∀ i, e i ∈ Fil) ∧
  (∃ ω : ⋀[O]^(Fintype.card I) Fil, O ∙ ω = ⊤) ∧
  ∀ ω : ⋀[O]^(Fintype.card I) Fil, O ∙ ω = ⊤ → ∀ (s : Fin (Fintype.card I) ≃ I) (e' : I → Fil), (∀ i, (e' i : H) = e i) →
    ∃ u : O, exteriorPower.ιMulti O (Fintype.card I) (fun j => e' (s j)) = u • ω ∧
      0 ≤ val_vp O l (algebraMap O K u) ∧
      val_vp O l (algebraMap O K u) ≤ Fintype.card I • val_vp O l (algebraMap O K D)
def FormClaims (l : ℕ) (φ : I → E →+* K) (ρ : orderC c →+* Module.End O H) (B : LinearMap.BilinForm O H) (D : O)
    (e f : I → H) : Prop :=
  (∃! ρE : E →+* Module.End K (K ⊗[O] H), ∀ a : orderC c, ρE a = (ρ a).baseChange K) ∧
  ∀ ρE : E →+* Module.End K (K ⊗[O] H), (∀ a : orderC c, ρE a = (ρ a).baseChange K) →
  ∀ (d : ℕ) (r ξ : E), d.Prime → r ^ 2 = -(d : E) → IsCMField.complexConj E ξ = -ξ → ξ ≠ 0 →
    (∀ σ : E →+* K, val_vp O l (σ ξ) ≤ 0) →
    (ξ * r ∈ maximalRealSubfield E ∧ ξ * r ≠ 0) ∧
    (∃! BF : LinearMap.BilinForm K (K ⊗[O] H), ∀ x y, B.baseChange K x y = BF x (ρE (ξ * r)⁻¹ y)) ∧
    ∀ BF : LinearMap.BilinForm K (K ⊗[O] H), (∀ x y, B.baseChange K x y = BF x (ρE (ξ * r)⁻¹ y)) → ∀ i,
      BF (inK K H (e i)) (inK K H (f i)) = φ i (ξ * r) * algebraMap O K (B (e i) (f i)) ∧
      BF (inK K H (e i)) (inK K H (f i)) ≠ 0 ∧
      val_vp O l (BF (inK K H (e i)) (inK K H (f i))) =
        val_vp O l (algebraMap O K (B (e i) (f i))) + val_vp O l (φ i ξ) + val_vp O l (φ i r) ∧
      val_vp O l (φ i r) = (((if l = d then 1 / 2 else 0 : ℚ)) : WithTop ℚ) ∧
      val_vp O l (BF (inK K H (e i)) (inK K H (f i))) ≤
        val_vp O l (algebraMap O K D) + (((if l = d then 1 / 2 else 0 : ℚ)) : WithTop ℚ)
end Steps
def LatticeClaims : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔣 : Ideal (OF E)), IsBaseCond 𝔣 →
  ∀ (l : ℕ), l.Prime →
  ∀ (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K]
    [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E →
  ∀ (D : O), D ≠ 0 → ClearsIdem K 𝔣 D →
  ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ →
  ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC (condQ 𝔣 Q) →+* Module.End O H) (Fil : Submodule O H)
    (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B →
    EigenClaims φ ρ Fil B D ∧
    ∀ e f : I → H, IsGens φ ρ e f →
      (∀ i, 0 ≤ val_vp O l (algebraMap O K (B (e i) (f i))) ∧
        val_vp O l (algebraMap O K (B (e i) (f i))) ≤ val_vp O l (algebraMap O K D)) ∧
      LowerClaims l φ ρ B D e f ∧ DetClaims K l Fil D e ∧ FormClaims l φ ρ B D e f
def DividedPowerClaims : Prop :=
  ∀ (l : ℕ), l.Prime →
  (∀ m : ℕ, (1 ≤ m → lPrimeExp l + padicValNat l m.factorial ≤ lPrimeExp l * m) ∧
    m + 2 * padicValNat l m.factorial ≤ 2 * (lPrimeExp l * m)) ∧
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O], (l : O) ∈ IsLocalRing.maximalIdeal O →
  ∀ (R : Type) [CommRing R] [Algebra O R], (∀ (k : ℕ) (x : R), k ≠ 0 → (k : R) * x = 0 → x = 0) →
    ∃ (γ : DividedPowers (Ideal.span {(lPrime l : R)})) (γ₀ : DividedPowers (Ideal.span {(l : R)})),
      (∀ m : ℕ, ∃ q : O, (m.factorial : O) * q = (lPrime l : O) ^ m ∧
        ∀ x : R, γ.dpow m ((lPrime l : R) * x) = algebraMap O R q * x ^ m) ∧
      (∀ (m : ℕ), ∀ y ∈ Ideal.span {(l : R)}, (m.factorial : R) * γ₀.dpow m y = y ^ m) ∧
      (∀ (m : ℕ), ∀ y ∈ Ideal.span {(lPrime l : R)}, γ.dpow m y = γ₀.dpow m y) ∧
      ∀ n : ℕ, 1 ≤ n →
        γ.IsSubDPIdeal (Ideal.span {(lPrime l : R) ^ n}) ∧
        ∀ (r : ℕ) (m : Fin r → ℕ) (x : Fin r → R), (∀ i, x i ∈ Ideal.span {(lPrime l : R)}) →
          2 * n * lPrimeExp l ≤ ∑ i, m i → ∏ i, γ.dpow (m i) (x i) ∈ Ideal.span {(lPrime l : R) ^ n}
def Statement : Prop := ElementD ∧ LatticeClaims ∧ DividedPowerClaims
example : lPrime 2 = 2 ^ lPrimeExp 2 ∧ lPrime 7 = 7 ^ lPrimeExp 7 := by decide
example (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] {K : Type} [Field K] [Algebra O K]
    [IsFractionRing O K] (l : ℕ) (hl : l ≠ 0) (h : (l : O) ∈ IsLocalRing.maximalIdeal O) : val_vp O l (l : K) = 1 := by
  have h0 : (l : K) ≠ 0 := by
    rw [← map_natCast (algebraMap O K)]
    exact (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 (Nat.cast_ne_zero.2 hl)
  have h1 : (IsDiscreteValuationRing.maximalIdeal O).valuation K (l : K) < 1 := by
    rw [← map_natCast (algebraMap O K), HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact h
  have h2 : (IsDiscreteValuationRing.maximalIdeal O).valuation K (l : K) ≠ 0 := by simpa using h0
  have h3 : ord_vw O (l : K) ≠ 0 := by
    unfold ord_vw
    intro h4
    have := WithZero.exp_log h2
    rw [neg_eq_zero.1 h4, WithZero.exp_zero] at this
    exact h1.ne this.symm
  rw [val_vp, if_neg h0, div_self (by exact_mod_cast h3)]
  rfl
example {E : Type} [Field E] [NumberField E] {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K] (c : Ideal (OF E))
    (σ : E →+* K) (a : orderC c) (x : O) : coordAt O c σ (a ⊗ₜ x) = σ a * algebraMap O K x := rfl
end GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations


