-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ObjBridge
-- name    : Formalism_SharpRestriction_GrowthBounds_ObjBridge
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:50:07.971977+00:00
-- url     : https://prove2.me/theorems/42c2b1ef-1010-4200-937c-d5150b2edd2b
-- title:
--   Obj Bridge
-- statement:
--   Definitions and structural lemmas for Obj Bridge, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/ObjBridge.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ObjPol
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace Formalism.MainNotions.G
def IsWittIdent {p n' : ℕ} [Fact p.Prime] {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] (σ : Qq ≃+* Qq)
    (φ : WF p n' ≃+* W) : Prop :=
  ∀ x : WF p n', σ (algebraMap W Qq (φ x)) = algebraMap W Qq (φ (WittVector.frobenius x))
def WittIdent : Prop :=
  ∀ (p n' : ℕ) [Fact p.Prime] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O),
    HidaSetting p n' W Qq O Kf ι σ j w → ∃ φ : WF p n' ≃+* W, IsWittIdent σ φ
@[reducible] def algOfIdent {p n' : ℕ} [Fact p.Prime] {W O : Type} [CommRing W] [CommRing O] (j : W →+* O)
    (φ : WF p n' ≃+* W) : Algebra (WF p n') O :=
  (j.comp (φ : WF p n' →+* W)).toAlgebra
def dvrOfStd {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} (h : UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w) :
    UniformizedDVR p O where
  w := w
  w_irr := h.2.1
  p_mem := by
    rw [← h.1.w_sq, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact h.2.1.not_isUnit ((isUnit_pow_iff two_ne_zero).1 hu)
  p_ne := by
    rw [← h.1.w_sq]
    exact pow_ne_zero 2 h.2.1.ne_zero
  complete := h.1.complete_O
def flatLetters {n' : ℕ} (vec : Fin n' → Bool) : LiftLetters (Fin n') where
  vec := vec
  pos := fun s => (s.val : ℤ)
def IsFlat {n' m : ℕ} (vec : Fin n' → Bool) (d : Fin n' → ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) : Prop :=
  ∀ s, lamAt lam0 s = if vec s then Pi.single 0 (d s : ℤ) else Pi.single (Fin.last m) (-(d s : ℤ))
def matQ {p n' : ℕ} [Fact p.Prime] {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] (φ : WF p n' ≃+* W) {k : ℕ}
    (g : Matrix (Fin k) (Fin k) (WF p n')) : Matrix (Fin k) (Fin k) Qq :=
  fun a b => algebraMap W Qq (φ (g a b))
def FlatTop : Prop :=
  ∀ (p n' : ℕ) [Fact p.Prime] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O),
    HidaSetting p n' W Qq O Kf ι σ j w → ∀ φ : WF p n' ≃+* W, IsWittIdent σ φ →
    ∀ (m r : ℕ) (vec : Fin n' → Bool) (d : Fin n' → ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ),
    1 ≤ r → r < m + 1 → IsFlat vec d lam0 →
    ∀ h : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq, IsUnit h.det →
    letI : Algebra (WF p n') O := algOfIdent j φ
    ∃ Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O) ≃ₗ[O] ↥(Vsp Kf lam0),
      (∀ F : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O),
        InA (O := O) (F : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) ↔
        Θ F ∈ HL (O := O) ι σ lam0 (colSpan W h)) ∧
      ∀ g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n'), IsGLW g →
        ∀ e : Edge W Qq (m + 1), IsEdgeBasis p r e (h * ((matQ φ g)⁻¹).transpose) →
          ∀ (F : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O)) (i : ℕ),
            InWjRg p n' O w r (flatLetters vec) g
              (F : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) i ↔
            Θ F ∈ scale (algebraMap O Kf w ^ (i : ℤ)) (Re p ι σ w r lam0 e)
def EdgePlane : Prop :=
  ∀ (p n' : ℕ) [Fact p.Prime] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O),
    HidaSetting p n' W Qq O Kf ι σ j w → ∀ φ : WF p n' ≃+* W, IsWittIdent σ φ →
    ∀ (m r : ℕ) (h : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq), IsUnit h.det →
    (∀ e : Edge W Qq (m + 1), IsEdge p n' r e → e.src = colSpan W h →
      ∃ g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n'), IsGLW g ∧
        IsEdgeBasis p r e (h * ((matQ φ g)⁻¹).transpose)) ∧
    (∀ (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')) (e : Edge W Qq (m + 1)), IsGLW g → r ≤ m + 1 →
      IsEdgeBasis p r e (h * ((matQ φ g)⁻¹).transpose) → IsEdge p n' r e ∧ e.src = colSpan W h) ∧
    ∀ (g g' : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')) (e e' : Edge W Qq (m + 1)), IsGLW g → IsGLW g' →
      IsEdgeBasis p r e (h * ((matQ φ g)⁻¹).transpose) → IsEdgeBasis p r e' (h * ((matQ φ g')⁻¹).transpose) →
      (e = e' ↔ ratPlane p n' r g = ratPlane p n' r g')
def DualHeightBasis : Prop :=
  ∀ (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O),
    HidaSetting p n' W Qq O Kf ι σ j w →
    ∀ (m r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ), IsDominant lam0 →
    ∀ e : Edge W Qq (m + 1), IsEdge p n' r e →
    ∃ (x : Module.Basis (Fin (dimV Kf lam0)) Kf ↥(Vsp Kf lam0)) (π : Fin (dimV Kf lam0) → ℤ),
      Submodule.span O (Set.range x) = HL ι σ lam0 e.src ∧
      Submodule.span O (Set.range fun i => ((p : Kf) ^ π i) • x i) = HL ι σ lam0 e.tgt ∧
      Submodule.span O (Set.range fun i => (algebraMap O Kf w ^ π i) • x i) = HLe p ι σ w lam0 e ∧
      (∀ i, 0 ≤ order r lam0 (π i)) ∧
      Submodule.span O (Set.range fun i => (algebraMap O Kf w ^ (-order r lam0 (π i))) • x i) =
        Re p ι σ w r lam0 e ∧
      Submodule.span O (Set.range fun i =>
          (algebraMap O Kf w ^ (-order r lam0 (π i)) * (p : Kf) ^ (-π i)) • x.coord i) =
        Re' p ι σ w r lam0 e
def DualHeightInclusion : Prop :=
  ∀ (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O),
    HidaSetting p n' W Qq O Kf ι σ j w →
    ∀ (m r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ), IsDominant lam0 →
    ∀ e : Edge W Qq (m + 1), IsEdge p n' r e →
      HL ι σ lam0 e.src ≤ Re p ι σ w r lam0 e ∧
      Formalism.GradedWeylDivisibility.dualLat O Kf (HL (O := O) ι σ lam0 e.tgt) ≤ Re' p ι σ w r lam0 e
def BePerfect : Prop :=
  ∀ (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O),
    HidaSetting p n' W Qq O Kf ι σ j w →
    ∀ (m r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ), IsDominant lam0 →
    ∀ e : Edge W Qq (m + 1), IsEdge p n' r e →
      (∀ G, G ∈ Re' p ι σ w r lam0 e ↔
        ∀ F ∈ Re p ι σ w r lam0 e, be p r lam0 F G ∈ Set.range (algebraMap O Kf)) ∧
      (∀ F, F ∈ Re p ι σ w r lam0 e ↔
        ∀ G ∈ Re' p ι σ w r lam0 e, be p r lam0 F G ∈ Set.range (algebraMap O Kf))
def HLSpans : Prop :=
  ∀ (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O),
    HidaSetting p n' W Qq O Kf ι σ j w →
    ∀ (m : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ), IsDominant lam0 →
    ∀ L : Submodule W (Fin (m + 1) → Qq), IsLattice W L →
    ∃ x : Module.Basis (Fin (dimV Kf lam0)) Kf ↥(Vsp Kf lam0),
      Submodule.span O (Set.range x) = HL ι σ lam0 L
def kap1 (p : ℕ) {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) : ℕ :=
  ∑ s, if ellWt (lamAt lam0 s) = 0 then 0 else N0 (m + 1) * deF p (m + 1) (ellWt (lamAt lam0 s))
def TestSide : Prop :=
  ∀ (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O),
    HidaSetting p n' W Qq O Kf ι σ j w →
    ∀ (m r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ), IsDominant lam0 →
    (∀ e : Edge W Qq (m + 1), IsEdge p n' r e → IsEdge p n' r e.dual ∧ e.dual.dual = e) ∧
    ∃ Ψ : Module.Dual Kf ↥(Vsp Kf lam0) ≃ₗ[Kf] ↥(Vsp Kf lam0),
      (∀ L : Submodule W (Fin (m + 1) → Qq), IsLattice W L →
        (Formalism.GradedWeylDivisibility.dualLat O Kf (HL (O := O) ι σ lam0 L)).map (Ψ.toLinearMap.restrictScalars O) ≤
                  HL ι σ lam0 (latDual L) ∧
        scale ((p : Kf) ^ (kap1 p lam0 : ℤ)) (HL (O := O) ι σ lam0 (latDual L)) ≤
          (Formalism.GradedWeylDivisibility.dualLat O Kf (HL (O := O) ι σ lam0 L)).map (Ψ.toLinearMap.restrictScalars O)) ∧
      ∀ e : Edge W Qq (m + 1), IsEdge p n' r e →
        (Re' p ι σ w r lam0 e).map (Ψ.toLinearMap.restrictScalars O) ≤ Re p ι σ w r lam0 e.dual ∧
        scale ((p : Kf) ^ (kap1 p lam0 : ℤ)) (Re p ι σ w r lam0 e.dual) ≤
          (Re' p ι σ w r lam0 e).map (Ψ.toLinearMap.restrictScalars O)
def LPOneEvery : Prop :=
  ∀ (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O),
    HidaSetting p n' W Qq O Kf ι σ j w →
    ∀ (m r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) (t D : ℕ) (κ : ℝ) (cStar : ℕ), IsDominant lam0 →
      LPprimeOne (W := W) p n' ι σ w r lam0 t D κ cStar → LPprime (W := W) p n' ι σ w r lam0 t D κ cStar
end Formalism.MainNotions.G


