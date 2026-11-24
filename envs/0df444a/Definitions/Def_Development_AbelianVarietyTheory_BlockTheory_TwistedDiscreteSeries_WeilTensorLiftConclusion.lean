-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_WeilTensorLiftConclusion
-- name    : Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_WeilTensorLiftConclusion
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T21:25:41.984571+00:00
-- url     : https://prove2.me/theorems/16daeecd-b400-4812-9c56-4ecb852b0ebb
-- title:
--   Weil Tensor Lift Conclusion
-- statement:
--   Definitions and structural lemmas for Weil Tensor Lift Conclusion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/WeilTensorLiftConclusion.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SmGL_inSupport_detRep
import Theorems.Thm_GlobalTheory_SmGL_isIrreducible_ofChar
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_ofChar_iff
import Theorems.Thm_GlobalTheory_SmGL_isUnitarisable_ofChar_iff
import Theorems.Thm_GlobalTheory_SplitWeil_om_mem_SB
import Theorems.Thm_GlobalTheory_SplitWeil_om_mul
import Theorems.Thm_GlobalTheory_SplitWeil_om_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix
namespace GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def weil (a b : ℕ) (μ : kˣ →* ℂˣ) :
    Representation ℂ (GL (Fin a) k × GL (Fin b) k) (SB (Matrix (Fin b) (Fin a) k)) where
  toFun gh :=
    { toFun := fun Φ => ⟨om μ⁻¹ gh.1 gh.2 Φ.1, om_mem_SB μ⁻¹ gh.1 gh.2 Φ.2⟩
      map_add' := fun Φ Ψ => by
        apply Subtype.ext; funext x; simp [om, mul_add]
      map_smul' := fun c Φ => by
        apply Subtype.ext; funext x; simp [om, mul_left_comm] }
  map_one' := by
    apply LinearMap.ext; intro Φ; apply Subtype.ext; exact om_one μ⁻¹ Φ.1
  map_mul' x y := by
    apply LinearMap.ext; intro Φ; apply Subtype.ext; exact om_mul μ⁻¹ x.1 y.1 x.2 y.2 Φ.1
def IsUnitaryCharacter (μ : kˣ →* ℂˣ) : Prop := IsSmoothChar μ ∧ IsUnitaryChar μ
def IsIrredUnitary {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) : Prop :=
  IsSmooth π ∧ π.IsIrreducible ∧ IsUnitarisable π
def SupportCondition {a : ℕ} (t : ℕ) (μ : kˣ →* ℂˣ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin a) k) V) : Prop :=
  ∀ j : ℕ, ¬ InSupport π (μ * absPow k (((t : ℂ) + 1) / 2 + j)) ∧
    ¬ InSupport π (μ * absPow k (-(((t : ℂ) + 1) / 2 + j)))
def LiftConclusion {a : ℕ} (t : ℕ) (μ : kˣ →* ℂˣ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin a) k) V) : Prop :=
  ∀ (V' : Type) [AddCommGroup V'] [Module ℂ V'] (π' : Representation ℂ (GL (Fin (a + t)) k) V'),
    IsSmooth π' → π'.IsIrreducible →
    (∃ q : (weil a (a + t) μ).IntertwiningMap (extTensor (contra π) π'), q ≠ 0) →
      Nonempty (π'.Equiv (prod₂ π (detRep (Fin t) μ))) ∧
      IsIrredUnitary (prod₂ π (detRep (Fin t) μ)) ∧
      Module.rank ℂ ((weil a (a + t) μ).IntertwiningMap (extTensor (contra π) π')) = 1
variable (k) in

def LiftUnderSupport : Prop :=
  ∀ (a t : ℕ), 1 ≤ a → 1 ≤ t → ∀ μ : kˣ →* ℂˣ, IsUnitaryCharacter μ →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin a) k) V),
      IsIrredUnitary π → SupportCondition t μ π → LiftConclusion t μ π
variable (k) in

def LiftForProducts : Prop :=
  ∀ (a t : ℕ), 1 ≤ a → 1 ≤ t → ∀ μ : kˣ →* ℂˣ, IsUnitaryCharacter μ →
    ∀ (u : ℕ) (d : Fin (u + 1) → ℕ) (hd : ∑ i, d i = a), d 0 ≤ t → (∀ i : Fin u, d i.succ ≤ t + 1) →
    ∀ (X : Fin (u + 1) → Type) [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
      (σ : ∀ i, Representation ℂ (GL (Fin (d i)) k) (X i)) (χ : Fin u → kˣ →* ℂˣ),
      IsIrredUnitary (σ 0) → (∀ i, IsUnitaryCharacter (χ i)) →
      (∀ i : Fin u, Nonempty ((σ i.succ).Equiv (detRep (Fin (d i.succ)) (χ i)))) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin a) k) V),
      Nonempty (π.Equiv (multiProd (finSigmaFinEquiv.trans (finCongr hd)) σ)) →
      LiftConclusion t μ π
def invTranspose (n : ℕ) (R : Type) [CommRing R] : GL (Fin n) R →* GL (Fin n) R where
  toFun h := ⟨(h⁻¹ : GL (Fin n) R).valᵀ, h.valᵀ,
    by rw [← transpose_mul, Units.mul_inv, transpose_one],
    by rw [← transpose_mul, Units.inv_mul, transpose_one]⟩
  map_one' := by
    apply Units.ext
    show ((1 : GL (Fin n) R)⁻¹ : GL (Fin n) R).valᵀ = 1
    rw [inv_one, Units.val_one, transpose_one]
  map_mul' x y := by
    apply Units.ext
    show ((x * y)⁻¹ : GL (Fin n) R).valᵀ = (x⁻¹ : GL (Fin n) R).valᵀ * (y⁻¹ : GL (Fin n) R).valᵀ
    rw [_root_.mul_inv_rev, Units.val_mul, transpose_mul]
def weilTensor (r n : ℕ) (χV χW : kˣ →* ℂˣ) :
    Representation ℂ (GL (Fin r) k × GL (Fin n) k) (SB (Matrix (Fin n) (Fin r) k)) :=
  (twist (weil r n χW) ((detChar (Fin r) (χW * χV⁻¹)).comp (MonoidHom.fst _ _))).comp
    ((invTranspose r k).prodMap (MonoidHom.id _))
variable (k) in

def MultiplicityOne : Prop :=
  ∀ (r t : ℕ), 1 ≤ r → r ≤ t → ∀ χV χW : kˣ →* ℂˣ, IsUnitaryCharacter χV → IsUnitaryCharacter χW →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin r) k) V),
      IsIrredUnitary σ →
    ∀ (V' : Type) [AddCommGroup V'] [Module ℂ V'] (π' : Representation ℂ (GL (Fin (r + t)) k) V'),
      IsSmooth π' → π'.IsIrreducible →
      Module.rank ℂ ((weilTensor r (r + t) χV χW).IntertwiningMap (extTensor σ π')) ≤ 1 ∧
      ((∃ q : (weilTensor r (r + t) χV χW).IntertwiningMap (extTensor σ π'), q ≠ 0) →
        Nonempty (π'.Equiv
          (prod₂ (twist σ (detChar (Fin r) (χW * χV⁻¹))) (detRep (Fin t) χW))))
def Statement : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    LiftUnderSupport k ∧ LiftForProducts k ∧ MultiplicityOne k
example (n : ℕ) {μ : kˣ →* ℂˣ} (h : IsUnitaryCharacter μ) : IsIrredUnitary (detRep (Fin n) μ) :=
  ⟨(isSmooth_ofChar_iff _).2 h.1.detChar, isIrreducible_ofChar _,
    (isUnitarisable_ofChar_iff _).2 fun _ => h.2 _⟩
example (t : ℕ) (μ : kˣ →* ℂˣ) : ¬ SupportCondition t μ (detRep (Fin (t + 2)) μ) := fun h => by
  refine (h 0).2 ?_
  have := inSupport_detRep (N := t + 2) μ 0
  convert this using 3
  simp
  ring
end GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion


