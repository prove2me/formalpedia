-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
-- name    : Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:57:31.198211+00:00
-- url     : https://prove2.me/theorems/ebc0686b-7552-4021-83b3-35000cbe5664
-- title:
--   Norm Const
-- statement:
--   Definitions and structural lemmas for Norm Const, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ExistenceOfLattices/NormConst.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnifDom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FrameUnif
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
structure ModelsOf {g : ℕ} {ty : Fin g → (E →+* ℂ)} {σ' : KA l →+* ℂ} (F : FamilyUnif Xo σ' ty) (r : ℕ) : Type 1 where
  X : Fin F.n → Data E r
  φ : ∀ i, (F.Di i).La ≃ₗ[𝓞 E] (X i).Λ
structure ModelBase {g : ℕ} {ty : Fin g → (E →+* ℂ)} {σ' : KA l →+* ℂ} {F : FamilyUnif Xo σ' ty} (M : ModelsOf F r) :
    Prop where
  rank : r = Dw.p + Dw.q
  type : ∀ k, (M.X k).p0 = Dw.q ∧ ∀ τ : E →+* ℂ, τ ∈ (M.X k).Ψ ↔ τ (H.rt : E) = H.rt0
  chi : ∀ k la γ, (M.X k).χ la γ = 1
  ef : ∀ k a b, (((F.Di k).EF a b : ℤ) : ℚ) =
    Algebra.trace ℚ E (-(M.X k).ξ0 * herm (M.X k).Gm (M.φ k a : Fin r → E) (M.φ k b))
  gam : ∀ k (γ : GL (Fin r) E), γ ∈ (M.X k).Γ ↔ IsUStab (M.X k).Gm (M.X k).Λ γ ∧
    (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di k).La), ∃ b : (F.Di k).La,
      (γ : Matrix (Fin r) (Fin r) E).mulVec (M.φ k a : Fin r → E) =
        (M.φ k a : Fin r → E) + (l.M : ℕ) • (M.φ k b : Fin r → E)) ∧
    ∀ a : (F.Di k).La, ∃ b : (F.Di k).La,
      (γ : Matrix (Fin r) (Fin r) E).mulVec (M.φ k a : Fin r → E) = (M.φ k a : Fin r → E) + (l.A : ℕ) • (M.φ k b : Fin r → E)
  domStab : ∀ k, ∀ x ∈ (M.X k).dom, (∀ b ∈ Bor (M.X k).Ψ r, rmul x b ∈ (M.X k).dom) ∧
    ∀ γ ∈ (M.X k).Γ, lact γ x ∈ (M.X k).dom
def FrameOK {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) (k : Fin F.n) (x : (M.X k).dom) (y : FrPt Xo c (CAt σ)) : Prop :=
  ∃ Pm : (F.Di k).La →+ (Fin g → ℂ),
        (∀ a j, Pm a j = perFr (M.X k) x.1 (M.φ k a : Fin r → E) (relab c σ (e j).1) (e j).2) ∧
        IsPeriod (F.Di k) (fun j => relab c σ (e j).1) Pm ∧ y.x = F.u k Pm ∧
        (∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1)
          (y.u τ i)) ∧
        ((∀ τ' i', ‖dmin (M.X k).Gm x.1 τ' i'‖ = 1) →
          ∃ (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ)
            (θ : (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ)),
            Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
            (∀ a b, (hermForm Hm (Pm a) (Pm b)).im = (F.Di k).EF a b) ∧
            (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) ∧
            (∀ j z, ⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0) ∧
            (∀ j j' z, ⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
              fr j z = valAt' (F.ex k Pm z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
                (Xo.univ.t.PP.L.g j j').val * fr j' z) ∧
            (∀ j, ⊤ ≤ (F.ex k Pm 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
              fr j 0 = valAt' y.x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
                (Xo.univ.t.PP.rig.s (fun _ => j)).val) ∧
            (∀ a j z, ‖χl (Pm a)‖ = 1 ∧ (⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
              fr j z = χl (Pm a) * Complex.exp (Real.pi * hermForm Hm z (Pm a) +
                Real.pi / 2 * hermForm Hm (Pm a) (Pm a)) * fr j (z + Pm a))) ∧
            (∀ j z (pt : Sp ℂ ⟶ Gx y.x),
              pt ≫ gxFst y.x = (F.ex k Pm z).left →
              pt ≫ gxSnd y.x = 𝟙 (Sp ℂ) →
              ⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
              valAt' pt ((PPx y.x).U (fun _ => j)) (y.s.f (fun _ => j)) = θ z * fr j z) ∧
            MeasureTheory.IsAddFundamentalDomain Pm.range Fd MeasureTheory.volume ∧
            (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) /
              (MeasureTheory.volume Fd).toReal = 1)
def unfOf {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) : Unf Xo c σ r where
  Comp := Fin F.n
  X := M.X
  un := un
def FramesOK {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) : Prop :=
  (∀ k x, FrameOK e F M k x (un k x)) ∧
  (∀ k (x : (M.X k).dom) b (_hb : b ∈ Bor (M.X k).Ψ r) (h : rmul x.1 b ∈ (M.X k).dom),
    ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (un k x) (un k ⟨_, h⟩) ∧
      ∀ a n, Dom a n → toC (wchar (ex Dw a n) t) = bchar (laU (unfOf e F M un) a n k) b) ∧
  (∀ k, ∀ γ ∈ (M.X k).Γ, ∀ (x : (M.X k).dom) (h : lact γ x.1 ∈ (M.X k).dom),
    ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (un k x) (un k ⟨_, h⟩) ∧ ∀ a n, Dom a n → toC (wchar (ex Dw a n) t) = 1) ∧
  ∀ a n, Dom a n → ∀ f ∈ sec Xo c a n, ∀ k, DifferentiableOn ℂ (rdU (unfOf e F M un) f k) (M.X k).dom
def CoverTri {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) : Prop :=
  ∀ y : FrPt Xo c (CAt σ), ∃ k, ∃ x : (M.X k).dom, ∃ Pm : (F.Di k).La →+ (Fin g → ℂ),
    (∀ a j, Pm a j = perFr (M.X k) x.1 (M.φ k a : Fin r → E) (relab c σ (e j).1) (e j).2) ∧
    F.u k Pm = y.x ∧
    ∀ v : ∀ τ, Fin (Dw.mult τ) → (Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left),
      (∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (v τ i)) →
      ∀ τ (i : Fin (Dw.mult τ)), ∃ cf : Fin (Dw.mult τ) → CAt σ, IsUnit (cf i) ∧ (∀ j, i < j → cf j = 0) ∧
        IsCombAt y.x (v τ) cf (y.u τ i)
def FibTri {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) : Prop :=
  ∀ k k' (x : (M.X k).dom) (x' : (M.X k').dom) (Pm : (F.Di k).La →+ (Fin g → ℂ))
    (Pm' : (F.Di k').La →+ (Fin g → ℂ))
    (v v' : ∀ τ, Fin (Dw.mult τ) → (Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left)),
    (∀ a j, Pm a j = perFr (M.X k) x.1 (M.φ k a : Fin r → E) (relab c σ (e j).1) (e j).2) →
    (∀ a j, Pm' a j = perFr (M.X k') x'.1 (M.φ k' a : Fin r → E) (relab c σ (e j).1) (e j).2) →
    F.u k Pm = F.u k' Pm' →
    (∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (v τ i)) →
    (∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k' Pm' z).left) (Pi.single (e.symm ⟨τ, i⟩) 1)
      (v' τ i)) →
    (∀ τ (i : Fin (Dw.mult τ)), ∃ cf : Fin (Dw.mult τ) → CAt σ, IsUnit (cf i) ∧ (∀ j, i < j → cf j = 0) ∧
      IsCombAt (F.u k Pm) (v τ) cf (v' τ i)) →
    ∃ γ ∈ (M.X k).Γ, ∃ b ∈ Bor (M.X k).Ψ r, (⟨k', x'.1⟩ : Σ k, Frame (M.X k).Ψ r) = ⟨k, rmul (lact γ x.1) b⟩
def princ (l : Level H) (Gm : Matrix (Fin r) (Fin r) E) (Di : Datum H) (φ0 : Di.La →ₗ[𝓞 E] (Fin r → E)) :
    Subgroup (GL (Fin r) E) where
  carrier := {γ | IsUStab Gm (LinearMap.range φ0) γ ∧
    (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Di.La), ∃ b : Di.La,
      (γ : Matrix (Fin r) (Fin r) E) *ᵥ (φ0 a) = φ0 a + (l.M : ℕ) • φ0 b) ∧
    ∀ a : Di.La, ∃ b : Di.La, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (φ0 a) = φ0 a + (l.A : ℕ) • φ0 b}
  one_mem' := ⟨⟨fun x y => by simp, fun x => by simp⟩, fun a _ => ⟨0, by simp⟩, fun a => ⟨0, by simp⟩⟩
  mul_mem' := by
    intro γ γ' hγ hγ'
    have hΛ : ∀ b : Di.La, ∃ b', φ0 b' = (γ : Matrix (Fin r) (Fin r) E) *ᵥ φ0 b := fun b =>
      (hγ.1.2 (φ0 b)).1 (LinearMap.mem_range_self φ0 b)
    refine ⟨⟨fun x y => ?_, fun x => ?_⟩, fun a ha => ?_, fun a => ?_⟩
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hγ.1.1, hγ'.1.1]
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec]
      exact (hγ'.1.2 x).trans (hγ.1.2 _)
    · obtain ⟨b, hb⟩ := hγ'.2.1 a ha
      obtain ⟨b1, hb1⟩ := hγ.2.1 a ha
      obtain ⟨b2, hb2⟩ := hΛ b
      refine ⟨b1 + b2, ?_⟩
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, hb, Matrix.mulVec_add, Matrix.mulVec_smul, hb1, ← hb2,
        map_add, smul_add, add_assoc]
    · obtain ⟨b, hb⟩ := hγ'.2.2 a
      obtain ⟨b1, hb1⟩ := hγ.2.2 a
      obtain ⟨b2, hb2⟩ := hΛ b
      refine ⟨b1 + b2, ?_⟩
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, hb, Matrix.mulVec_add, Matrix.mulVec_smul, hb1, ← hb2,
        map_add, smul_add, add_assoc]
  inv_mem' := by
    intro γ hγ
    have hri : ∀ v, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) = v :=
      fun v => by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    have hli : ∀ v, ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = v :=
      fun v => by rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    have hΛ : ∀ b : Di.La, ∃ b', φ0 b' = ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ φ0 b := fun b =>
      (hγ.1.2 _).2 (by rw [hri]; exact LinearMap.mem_range_self φ0 b)
    refine ⟨⟨fun x y => ?_, fun x => ?_⟩, fun a ha => ?_, fun a => ?_⟩
    · rw [← hγ.1.1, hri, hri]
    · have := hγ.1.2 (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ x)
      rw [hri] at this
      exact this.symm
    · obtain ⟨b, hb⟩ := hγ.2.1 a ha
      obtain ⟨b', hb'⟩ := hΛ b
      refine ⟨-b', ?_⟩
      have e := hli (φ0 a)
      rw [hb, Matrix.mulVec_add, Matrix.mulVec_smul, ← hb'] at e
      rw [map_neg, smul_neg, ← sub_eq_add_neg, eq_sub_iff_add_eq, e]
    · obtain ⟨b, hb⟩ := hγ.2.2 a
      obtain ⟨b', hb'⟩ := hΛ b
      refine ⟨-b', ?_⟩
      have e := hli (φ0 a)
      rw [hb, Matrix.mulVec_add, Matrix.mulVec_smul, ← hb'] at e
      rw [map_neg, smul_neg, ← sub_eq_add_neg, eq_sub_iff_add_eq, e]
def LatModel (l : Level H) (Ψ : Finset (E →+* ℂ)) (Gm : Matrix (Fin r) (Fin r) E) (ξ₀ : E) (q : ℕ)
    (Di : Datum H) : Prop :=
  ∃ φ0 : Di.La →ₗ[𝓞 E] (Fin r → E), Function.Injective φ0 ∧
    (∀ a b, ((Di.EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ0 a) (φ0 b))) ∧
    Submodule.span E (LinearMap.range φ0 : Set (Fin r → E)) = ⊤ ∧
    (∃ den : 𝓞 E, den ≠ 0 ∧ ∀ x ∈ LinearMap.range φ0, ∀ y ∈ LinearMap.range φ0,
      IsIntegral ℤ ((den : E) * herm Gm x y)) ∧
    (∃ S : Finset (GL (Fin r) E), ∀ γ, IsUStab Gm (LinearMap.range φ0) γ → ∃ s ∈ S, s⁻¹ * γ ∈ princ l Gm Di φ0) ∧
    (∀ γ ∈ princ l Gm Di φ0, ∀ x ∈ GG Ψ Gm q, ∀ b ∈ Bor Ψ r, lact γ x = rmul x b → γ = 1) ∧
    ∃ m : ℕ, 0 < m ∧ ∀ κ0 : E, (κ0 = 2 * ξ₀ ∨ κ0 = -(2 * ξ₀)) →
      ∀ ξ ∈ LinearMap.range φ0, herm Gm ξ ξ = 0 → ∀ s : E, cc s = s → IsIntegral ℤ s →
        ∃ γ ∈ princ l Gm Di φ0, (γ : Matrix (Fin r) (Fin r) E) = transvMat Gm ξ ((m : E) * s * κ0)
def NegXi {g : ℕ} {ty : Fin g → (E →+* ℂ)} {σ' : KA l →+* ℂ} {F : FamilyUnif Xo σ' ty} (M : ModelsOf F r) : Prop :=
  ∀ k, ∀ τ ∈ (M.X k).Ψ, (τ (M.X k).ξ0).im < 0
def IsPerFr {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) (k : Fin F.n) (Pf : Frame (M.X k).Ψ r → ((F.Di k).La →+ (Fin g → ℂ))) : Prop :=
  ∀ x a j, Pf x a j = perFr (M.X k) x (M.φ k a : Fin r → E) (relab c σ (e j).1) (e j).2
structure ThetaData {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) (k : Fin F.n) : Type where
  Pf : Frame (M.X k).Ψ r → ((F.Di k).La →+ (Fin g → ℂ))
  per : IsPerFr e F M k Pf
  isPer : ∀ x ∈ (M.X k).dom, IsPeriod (F.Di k) (fun j => relab c σ (e j).1) (Pf x)
  m : ℕ
  co : (Fin m → ℂ) ≃L[ℂ] Frame (M.X k).Ψ r
  holPer : IsHolPeriods (F.Di k) (fun j => relab c σ (e j).1) (co ⁻¹' (M.X k).dom) (fun b => Pf (co b))
  bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (F.Di k).La
  sympl : ∀ a a', (F.Di k).EF (bas a) (bas a') = -omegaStd a a'
  adapt : (∀ i, ∃ v, H.w0 ^ 4 • bas (Pi.single (Sum.inl i) 1) = bas (Pi.single (Sum.inl i) 1) + (8 : ℕ) • v) ∧
    ∀ i, ∃ v, H.w0 ^ 4 • bas (Pi.single (Sum.inr i) 1) = (8 : ℕ) • v
  h : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ
  ta : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ
  norm : ∀ b ∈ co ⁻¹' (M.X k).dom, IsUnit (h b).det ∧ (ta b).IsSymm ∧ ((ta b).map Complex.im).PosDef ∧ ∀ i,
    h b *ᵥ Pf (co b) (bas (Pi.single (Sum.inl i) 1)) = Pi.single i 1 ∧
    h b *ᵥ Pf (co b) (bas (Pi.single (Sum.inr i) 1)) = ta b *ᵥ Pi.single i 1
  hol : ∀ i j, DifferentiableOn ℂ (fun b => h b i j) (co ⁻¹' (M.X k).dom) ∧
    DifferentiableOn ℂ (fun b => ta b i j) (co ⁻¹' (M.X k).dom)
  c₁ : Fin g → ℂ
  c₂ : Fin g → ℂ
  half₁ : ∀ i, c₁ i = 0 ∨ c₁ i = 1 / 2
  half₂ : ∀ i, c₂ i = 0 ∨ c₂ i = 1 / 2
  fr : Xo.univ.t.PP.L.ι → (Fin m → ℂ) × (Fin g → ℂ) → ℂ
  fr_hol : ∀ j, DifferentiableOn ℂ (fr j)
    {bz | bz.1 ∈ co ⁻¹' (M.X k).dom ∧ ⊤ ≤ (F.ex k (Pf (co bz.1)) bz.2).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}
  fr_ne : ∀ j b z, b ∈ co ⁻¹' (M.X k).dom → ⊤ ≤ (F.ex k (Pf (co b)) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j (b, z) ≠ 0
  fr_coc : ∀ j j' b z, b ∈ co ⁻¹' (M.X k).dom →
    ⊤ ≤ (F.ex k (Pf (co b)) z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
    fr j (b, z) = valAt' (F.ex k (Pf (co b)) z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
      (Xo.univ.t.PP.L.g j j').val * fr j' (b, z)
  fr_rig : ∀ j b, b ∈ co ⁻¹' (M.X k).dom → ⊤ ≤ (F.ex k (Pf (co b)) 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
    fr j (b, 0) = valAt' (F.u k (Pf (co b))) ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
      (Xo.univ.t.PP.rig.s (fun _ => j)).val
  fr_sec : ∀ b ∈ co ⁻¹' (M.X k).dom,
    ∃ s : (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom (F.u k (Pf (co b))))).Sec,
      ∀ j z (x : Sp ℂ ⟶ pullback Xo.univ.t.G.hom (F.u k (Pf (co b)))),
        x ≫ pullback.fst _ _ = (F.ex k (Pf (co b)) z).left → x ≫ pullback.snd _ _ = 𝟙 _ →
        ⊤ ≤ (F.ex k (Pf (co b)) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
        valAt' x ((Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom (F.u k (Pf (co b))))).U (fun _ => j))
          (s.f (fun _ => j)) = thetaChar (ta b) c₁ c₂ (h b *ᵥ z) * fr j (b, z)
def IsThetaPt {g : ℕ} {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
    {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
    {M : ModelsOf F r} {k : Fin F.n} (T : ThetaData e F M k) (b : Fin T.m → ℂ) (κ : ℂ)
    (y : FrPt Xo c (CAt σ)) : Prop :=
  y.x = F.u k (T.Pf (T.co b)) ∧
    (∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k (T.Pf (T.co b)) z).left) (Pi.single (e.symm ⟨τ, i⟩) 1)
      (y.u τ i)) ∧
    ∀ j z (pt : Sp ℂ ⟶ Gx y.x), pt ≫ gxFst y.x = (F.ex k (T.Pf (T.co b)) z).left → pt ≫ gxSnd y.x = 𝟙 (Sp ℂ) →
      ⊤ ≤ (F.ex k (T.Pf (T.co b)) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx y.x).U (fun _ => j)) (y.s.f (fun _ => j)) =
        κ * thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ z) * T.fr j (b, z)
def normConst {g : ℕ} (ty : Fin g → (E →+* ℂ)) (ξ₀ : E) : ℝ :=
  Real.sqrt (2 ^ g / ∏ j, (2 * ‖ty j ξ₀‖))
def IsNormUn {g : ℕ} {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
    {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
    {M : ModelsOf F r} {k : Fin F.n} (T : ThetaData e F M k) (un : (M.X k).dom → FrPt Xo c (CAt σ)) : Prop :=
  ∀ x : (M.X k).dom, ∃ κ : ℂ,
    κ ^ 2 = (normConst (fun j => relab c σ (e j).1) (M.X k).ξ0 : ℂ) * (T.h (T.co.symm x.1)).det ∧
      IsThetaPt T (T.co.symm x.1) κ (un x)
end GlobalTheory.FrameUnif


