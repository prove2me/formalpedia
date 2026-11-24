-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_Divisibility_ConjugationAtDistinguishedPlace
-- name    : Formalism_LocalToGlobal_Divisibility_ConjugationAtDistinguishedPlace
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T19:57:05.655171+00:00
-- url     : https://prove2.me/theorems/faadbfaa-a27b-4c38-9d6e-f3dccc2ac885
-- title:
--   Conjugation At Distinguished Place
-- statement:
--   Definitions and structural lemmas for Conjugation At Distinguished Place, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ConjugationAtDistinguishedPlace.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_AdjoinCycZeta
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IotaABijective
import Definitions.Def_Formalism_QuotientMetricDivisors_RatHermLcvTwist
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickOrbit_key
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HC_HostRaw_conj_conj
import Theorems.Thm_Formalism_HC_HostRaw_jOf_coe
import Theorems.Thm_Formalism_L2_Host_algC_coe
import Theorems.Thm_Formalism_L2_Host_jOf_coe
import Theorems.Thm_Formalism_L2_Host_restr_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.HC.HostRaw.jOf_coe
attribute [local simp] Formalism.L2.Host.algC_coe
attribute [local simp] Formalism.L2.Host.jOf_coe
attribute [local simp] Formalism.L2.Host.restr_apply


set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
namespace Formalism.L2.DIV
open Formalism.L2.Host Formalism.DivisionValues
instance normalQb : Normal ℚ Qb :=
  haveI : IsAlgClosure ℚ Qb := ⟨inferInstance, AlgebraicClosure.isAlgebraic ℚ⟩
  IsAlgClosure.normal ℚ Qb
def conjQb (ι : Qb →+* ℂ) : Qb ≃ₐ[ℚ] Qb :=
  AlgEquiv.ofRingEquiv (f := (algC ((starRingEnd ℂ).comp ι)).trans (algC ι).symm) (fun r => by simp)
theorem conjQb_spec (ι : Qb →+* ℂ) (x : Qb) : ι (conjQb ι x) = starRingEnd ℂ (ι x) := by
  have key : conjQb ι x = (algC ι).symm (algC ((starRingEnd ℂ).comp ι) x) := rfl
  rw [key, ← algC_coe ι ((algC ι).symm (algC ((starRingEnd ℂ).comp ι) x)),
    RingEquiv.apply_symm_apply, algC_coe] <;> rfl
theorem conjQb_conjQb (ι : Qb →+* ℂ) (x : Qb) : conjQb ι (conjQb ι x) = x := by
  apply ι.injective
  rw [conjQb_spec, conjQb_spec, Complex.conj_conj]
def cLL (ι : Qb →+* ℂ) (LL : Fld) [Normal ℚ LL] : LL ≃ₐ[ℚ] LL := (conjQb ι).restrictNormal LL
theorem cLL_coe (ι : Qb →+* ℂ) (LL : Fld) [Normal ℚ LL] (x : LL) : ((cLL ι LL x : LL) : Qb) = conjQb ι x := by
  first
  | exact AlgEquiv.restrictNormal_commutes (conjQb ι) LL x
  | exact AlgEquiv.restrictNormal_commutes (conjQb ι) x
theorem cLL_cLL (ι : Qb →+* ℂ) (LL : Fld) [Normal ℚ LL] (x : LL) : cLL ι LL (cLL ι LL x) = x := by
  apply Subtype.ext
  rw [cLL_coe, cLL_coe, conjQb_conjQb]
@[reducible] def starLL (ι : Qb →+* ℂ) (LL : Fld) [Normal ℚ LL] : StarRing LL where
  star := cLL ι LL
  star_involutive := cLL_cLL ι LL
  star_mul a b := by rw [map_mul, mul_comm]
  star_add a b := map_add _ a b
def CoF (_ι : Qb →+* ℂ) (LL : Fld) : Type := LL
namespace CoF
variable (ι : Qb →+* ℂ) (LL : Fld)
instance : Field (CoF ι LL) := inferInstanceAs (Field LL)
instance [FiniteDimensional ℚ LL] : NumberField (CoF ι LL) where
  to_charZero := inferInstanceAs (CharZero LL)
  to_finiteDimensional := inferInstanceAs (FiniteDimensional ℚ LL)
instance [Normal ℚ LL] : StarRing (CoF ι LL) := starLL ι LL
def val : CoF ι LL →+* Qb := LL.val.toRingHom
def mk (x : Qb) (hx : x ∈ LL) : CoF ι LL := (⟨x, hx⟩ : LL)
@[simp] theorem val_mk (x : Qb) (hx : x ∈ LL) : val ι LL (mk ι LL x hx) = x := rfl
end CoF
def sig0 (ι : Qb →+* ℂ) (LL : Fld) : CoF ι LL →+* ℂ := ι.comp (CoF.val ι LL)
def v0 (ι : Qb →+* ℂ) (LL : Fld) : InfinitePlace (CoF ι LL) := InfinitePlace.mk (sig0 ι LL)
def K0 (ι : Qb →+* ℂ) (LL : Fld) [Normal ℚ LL] : Subfield (CoF ι LL) := cmMax (CoF ι LL)
def cmQb (ι : Qb →+* ℂ) : Fld where
  carrier := {a | ∀ τ : Qb →+* ℂ, τ (conjQb ι a) = starRingEnd ℂ (τ a)}
  mul_mem' := by
    intro a b ha hb τ
    rw [map_mul, map_mul, map_mul, map_mul, ha τ, hb τ]
  add_mem' := by
    intro a b ha hb τ
    rw [map_add, map_add, map_add, map_add, ha τ, hb τ]
  inv_mem' := by
    intro a ha τ
    rw [map_inv₀, map_inv₀, map_inv₀, map_inv₀, ha τ]
  algebraMap_mem' := by
    intro r τ
    rw [AlgEquiv.commutes]
    simp
def tauLL {L LL : Fld} [Normal ℚ LL] (h : L ≤ LL) (s : L →ₐ[ℚ] Qb) : L →ₐ[ℚ] LL :=
  ((s.liftNormal Qb).restrictNormal LL).comp (inclusion h)
def tauCo (ι : Qb →+* ℂ) {L LL : Fld} [Normal ℚ LL] (h : L ≤ LL) (s : L →ₐ[ℚ] Qb) : L →+* CoF ι LL :=
  (tauLL h s).toRingHom
structure IsCoeffField {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) (Ns : List ℕ) (S : Set Qb) (LL : Fld) : Prop where

  fin : FiniteDimensional ℚ LL

  normal : Normal ℚ LL

  host : H.EQ ≤ LL

  cyc : ∀ N ∈ Ns, cycQ N ≤ LL

  vals : S ⊆ (LL : Set Qb)
def coeffOrders (cG g₁ g₂ : ℕ) : List ℕ := [cG, g₁ * (g₁ - 1), g₂ * (g₂ - 1), 3 ^ 4, 5 ^ 4]
def coeffMin {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) (Ns : List ℕ) (S : Set Qb) : Fld :=
  normalClosure ℚ (H.EQ ⊔ adjoin ℚ ((⋃ N ∈ Ns, mus N) ∪ S) : Fld) Qb
def DistinguishedEmbeddingConjugation : Prop :=
  ∀ (ι : Qb →+* ℂ) (LL : Fld) [Normal ℚ LL] (x : CoF ι LL), sig0 ι LL (star x) = starRingEnd ℂ (sig0 ι LL x)
def DistinguishedEmbeddingConjugationUnique : Prop :=
  ∀ (ι : Qb →+* ℂ) (LL : Fld) [Normal ℚ LL] (c' : CoF ι LL →+* CoF ι LL),
    (∀ x, sig0 ι LL (c' x) = starRingEnd ℂ (sig0 ι LL x)) → ∀ x, c' x = star x
def ConjugationAtDistinguishedPlace : Prop :=
  ∀ (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL], IsConjAt (v0 ι LL)
def DistinguishedPlaceEmbedding : Prop :=
  ∀ (ι : Qb →+* ℂ) (LL : Fld), (v0 ι LL).embedding = sig0 ι LL ∨
    (v0 ι LL).embedding = (starRingEnd ℂ).comp (sig0 ι LL)
def MaxCMSubfieldConjugation : Prop :=
  ∀ (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL], IsCMSub (K0 ι LL)
def TotComplex : Prop :=
  ∀ (ι : Qb →+* ℂ) (LL : Fld) (d : ℕ), 0 < d → KQ d ≤ LL → IsTotallyComplex (CoF ι LL)
def MaxCMSubfieldMemIff : Prop :=
  ∀ (ι : Qb →+* ℂ) (LL : Fld) [Normal ℚ LL] (x : CoF ι LL), x ∈ K0 ι LL ↔ CoF.val ι LL x ∈ cmQb ι
def CmQbIndep : Prop :=
  ∀ ι ι' : Qb →+* ℂ, cmQb ι = cmQb ι' ∧ ∀ x ∈ cmQb ι, conjQb ι x = conjQb ι' x
def CmQbComm : Prop :=
  ∀ (ι : Qb →+* ℂ) (x : Qb), x ∈ cmQb ι ↔ ∀ σ : Qb ≃ₐ[ℚ] Qb, σ (conjQb ι x) = conjQb ι (σ x)
def CycLeCm : Prop := ∀ (ι : Qb →+* ℂ) (N : ℕ), 0 < N → cycQ N ≤ cmQb ι
def SqLeCm : Prop := ∀ (ι : Qb →+* ℂ) (m : ℤ), sqQ m ≤ cmQb ι
def HostLeCm : Prop :=
  ∀ (ι : Qb →+* ℂ) {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ), H.EQ ≤ cmQb ι
def HostFieldAndCyclotomicInMaxCM : Prop :=
  ∀ (ι : Qb →+* ℂ) (LL : Fld) [Normal ℚ LL] (x : CoF ι LL),
    ((∃ (φ : Formalism.HC.Frame) (H : Formalism.HC.HostRaw φ), CoF.val ι LL x ∈ H.EQ) ∨
      ∃ N : ℕ, 0 < N ∧ CoF.val ι LL x ∈ cycQ N) → x ∈ K0 ι LL
def ConjNeOne : Prop :=
  ∀ (ι : Qb →+* ℂ) (LL : Fld) [Normal ℚ LL] (d : ℕ), 0 < d → KQ d ≤ LL → ∃ a ∈ K0 ι LL, star a ≠ a
def CubeRootNotCm : Prop := ∀ (ι : Qb →+* ℂ) (x : Qb), x ^ 3 = 2 → x ∉ cmQb ι
def TauLLBij : Prop :=
  ∀ (L LL : Fld) [Normal ℚ LL] (h : L ≤ LL), Function.Bijective (tauLL h)
def TauStar : Prop :=
  ∀ (ι : Qb →+* ℂ) (L LL : Fld) [Normal ℚ LL] (h : L ≤ LL), L ≤ cmQb ι →
    ∀ (s : L →ₐ[ℚ] Qb) (x y : L), (y : Qb) = conjQb ι x → star (tauCo ι h s x) = tauCo ι h s y
def CoeffMinSpec : Prop :=
  ∀ {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) (Ns : List ℕ) (S : Set Qb),
    ((∀ N ∈ Ns, 0 < N) → FiniteDimensional ℚ (adjoin ℚ S) → IsCoeffField H Ns S (coeffMin H Ns S)) ∧
    ∀ LL : Fld, IsCoeffField H Ns S LL → coeffMin H Ns S ≤ LL
def NoCoeffFieldZero : Prop :=
  ∀ {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) (Ns : List ℕ) (S : Set Qb) (LL : Fld), 0 ∈ Ns → ¬ IsCoeffField H Ns S LL
def CoeffFieldIff : Prop :=
  ∀ {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) (Ns : List ℕ) (S : Set Qb),
    (∃ LL : Fld, IsCoeffField H Ns S LL) ↔ (∀ N ∈ Ns, 0 < N) ∧ FiniteDimensional ℚ (adjoin ℚ S)
def CoefficientFieldSetting : Prop :=
  ∀ (ι : Qb →+* ℂ) {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) (Ns : List ℕ) (S : Set Qb) (LL : Fld)
    (h : IsCoeffField H Ns S LL),
    haveI := h.fin
    haveI := h.normal
    IsTotallyComplex (CoF ι LL) ∧ IsCMSub (K0 ι LL) ∧ IsConjAt (v0 ι LL) ∧
      (∀ z (hz : z ∈ H.EQ), CoF.mk ι LL z (h.host hz) ∈ K0 ι LL) ∧
      ∀ N (hN : N ∈ Ns) z (hz : z ∈ cycQ N), CoF.mk ι LL z (h.cyc N hN hz) ∈ K0 ι LL
def CoeffFieldExists : Prop :=
  ∀ {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) (cG g₁ g₂ : ℕ) (S : Set Qb), 0 < cG → 2 ≤ g₁ → 2 ≤ g₂ → S.Finite →
    IsCoeffField H (coeffOrders cG g₁ g₂) S (coeffMin H (coeffOrders cG g₁ g₂) S)
end Formalism.L2.DIV


