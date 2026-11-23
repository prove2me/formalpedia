-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_EtaDualPairing
-- name    : Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_EtaDualPairing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:19:35.662843+00:00
-- url     : https://prove2.me/theorems/d0785a03-9cb4-4103-b68c-03e55e0fa372
-- title:
--   Eta Dual Pairing
-- statement:
--   Definitions and structural lemmas for Eta Dual Pairing, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/PoincareCuspForms/EtaDualPairing.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_SeriesState
import Theorems.Thm_ReciprocityTheory_PGsh_LHom_sqZero_of_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct ReciprocityTheory.PGsh
namespace GlobalTheory.IndefiniteRowSideFullHecke.EtaDualPairing
universe u
variable {R₀ : Type u} [CommRing R₀]
theorem isLocalRing_dualNumber (A : Type u) [CommRing A] [IsLocalRing A] :
    IsLocalRing (DualNumber A) := by
  haveI : Nontrivial (DualNumber A) := inferInstanceAs (Nontrivial (A × A))
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.isUnit_iff_isUnit_fst]
  simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self a.fst
def dual (R : LAlg R₀) : LAlg R₀ :=
  @LAlg.mk R₀ _ (DualNumber R) _ _ (isLocalRing_dualNumber R)
def eta (R : LAlg R₀) : dual R := (DualNumber.eps : DualNumber R)
def red (R : LAlg R₀) : LHom (dual R) R :=
  ⟨TrivSqZeroExt.fstHom R₀ R R,
    ⟨fun _ h => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 h⟩⟩
def incl (R : LAlg R₀) : LHom R (dual R) :=
  ⟨TrivSqZeroExt.inlAlgHom R₀ R R,
    ⟨fun _ h => TrivSqZeroExt.isUnit_inl_iff.1 h⟩⟩
theorem red_comp_incl (R : LAlg R₀) : (red R).comp (incl R) = LHom.id R :=
  Subtype.ext (AlgHom.ext fun _ => rfl)
theorem eta_mul_eta (R : LAlg R₀) : eta R * eta R = 0 := DualNumber.eps_mul_eps
theorem red_sqZero (R : LAlg R₀) : (red R).SqZero := by
  refine LHom.sqZero_of_span _ (eta R) (fun a => ⟨(incl R).1 a, rfl⟩) ?_ (eta_mul_eta R)
  ext x
  rw [RingHom.mem_ker, Ideal.mem_span_singleton']
  constructor
  · intro hx
    have key : ∀ b : DualNumber R, TrivSqZeroExt.fst b = 0 →
        (TrivSqZeroExt.inl (TrivSqZeroExt.snd b) : DualNumber R) * DualNumber.eps = b :=
      fun b hb => by ext <;> simp [hb]
    exact ⟨_, key x hx⟩
  · rintro ⟨a, rfl⟩
    have key : ∀ b : DualNumber R, TrivSqZeroExt.fst (b * DualNumber.eps) = 0 := fun b => by simp
    exact key a
def etaMul (R : LAlg R₀) : R →ₗ[R₀] (red R).ker :=
  LinearMap.codRestrict (red R).ker
    ((LinearMap.mulLeft R₀ (eta R)).comp (incl R).1.toLinearMap) (fun r => by
      change TrivSqZeroExt.fst
        ((DualNumber.eps : DualNumber R) * (TrivSqZeroExt.inl r : DualNumber R)) = 0
      simp)
def onePlusEta (R : LAlg R₀) (a : R) : (dual R)ˣ where
  val := 1 + eta R * (incl R).1 a
  inv := 1 - eta R * (incl R).1 a
  val_inv := by linear_combination (-((incl R).1 a) ^ 2) * eta_mul_eta R
  inv_val := by linear_combination (-((incl R).1 a) ^ 2) * eta_mul_eta R
variable (B : BX R₀)
abbrev om : Type u := Module.Dual R₀ B.gg
def pair (R : LAlg R₀) (v : B.gg ⊗[R₀] R) (h : om B ⊗[R₀] R) : R :=
  LinearMap.mul' R₀ R (LinearMap.rTensor R (dualTensorHom R₀ B.gg R h) v)
def etaPt (R : LAlg R₀) (v : B.gg ⊗[R₀] R) : B.G (dual R) :=
  B.tg (red R) (red_sqZero R) (LinearMap.lTensor B.gg (etaMul R) v)
def constPt (R : LAlg R₀) (y : B.G R) : B.G (dual R) := B.map (incl R) y
theorem red_etaPt (R : LAlg R₀) (v : B.gg ⊗[R₀] R) : B.map (red R) (etaPt B R v) = 0 :=
  (B.tg_ker _ (red_sqZero R) _).2 ⟨_, rfl⟩
theorem red_constPt (R : LAlg R₀) (y : B.G R) : B.map (red R) (constPt B R y) = y := by
  rw [constPt, ← B.map_comp, red_comp_incl, B.map_id]
theorem nsmul_etaPt {R : LAlg R₀} {N : ℕ} (hN : (N : R) = 0) (v : B.gg ⊗[R₀] R) :
    N • etaPt B R v = 0 := by
  have hv : N • v = 0 := by
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul g r =>
      have : N • r = 0 := by rw [nsmul_eq_mul, hN, zero_mul]
      rw [← TensorProduct.tmul_smul, this, TensorProduct.tmul_zero]
    | add a b ha hb => rw [nsmul_add, ha, hb, add_zero]
  rw [etaPt, ← map_nsmul, ← map_nsmul, hv, map_zero, map_zero]
theorem nsmul_constPt {R : LAlg R₀} {N : ℕ} {y : B.G R} (hy : N • y = 0) :
    N • constPt B R y = 0 := by
  rw [constPt, ← map_nsmul, hy, map_zero]
def IsHt {R : LAlg R₀} (N : ℕ) (y : B.G R) (h : om B ⊗[R₀] R) : Prop :=
  (N : R) = 0 ∧ N • y = 0 ∧
    ∀ v : B.gg ⊗[R₀] R,
      B.IsPairing N (etaPt B R v) (constPt B R y) (onePlusEta R (pair B R v h))
def ReducesToZero1 {R : LAlg R₀} (v : B.gg ⊗[R₀] R) (y : B.G R)
    (u : B.P (dual R) (etaPt B R v) (constPt B R y)) : Prop :=
  B.tr2 (red_constPt B R y) (B.tr1 (red_etaPt B R v) (B.pmap (red R) u)) = B.zero1 y
def HtStatement : Prop :=
  (∀ (R : LAlg R₀) (N : ℕ) (y : B.G R), (N : R) = 0 → N • y = 0 → ∃ h, IsHt B N y h) ∧
  (∀ (R : LAlg R₀) (N : ℕ) (y : B.G R) (h h' : om B ⊗[R₀] R),
    IsHt B N y h → IsHt B N y h' → h = h') ∧
  (∀ (R : LAlg R₀) (N : ℕ) (y y' : B.G R) (h h' : om B ⊗[R₀] R),
    IsHt B N y h → IsHt B N y' h' → IsHt B N (y + y') (h + h')) ∧
  (∀ (R : LAlg R₀) (N : ℕ) (hN : (N : R) = 0) (y : B.G R) (hy : N • y = 0)
    (h : om B ⊗[R₀] R), IsHt B N y h →
    ∀ (v : B.gg ⊗[R₀] R) (u : B.P (dual R) (etaPt B R v) (constPt B R y)),
      ReducesToZero1 B v y u →
      B.tr1 (nsmul_etaPt B hN v) (B.nsmul1 u N) = B.zero1 (constPt B R y) ∧
      B.tr2 (nsmul_constPt B hy) (B.nsmul2 u N) =
        B.smul (onePlusEta R (-pair B R v h)) (B.zero2 (etaPt B R v)))
example (R : LAlg R₀) (a : R) :
    (onePlusEta R (-a) : dual R) = 1 - eta R * (incl R).1 a := by
  simp [onePlusEta, sub_eq_add_neg]
example (R : LAlg R₀) : eta R ≠ 0 := fun h => by
  have := congrArg (fun x : DualNumber R => TrivSqZeroExt.snd x) h
  simp [eta] at this
  exact one_ne_zero (α := R) this
end GlobalTheory.IndefiniteRowSideFullHecke.EtaDualPairing


