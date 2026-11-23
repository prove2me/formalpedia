-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OpenRowsFree
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_OpenRowsFree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:25:03.981658+00:00
-- url     : https://prove2.me/theorems/c55df3cf-cc32-4c21-a0fe-323f9afcb440
-- title:
--   Open Rows Free
-- statement:
--   Definitions and structural lemmas for Open Rows Free, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/OpenRowsFree.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.PjFree.Rows
open Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open MeasureTheory Formalism.L2.PjFree
open scoped Matrix
section PerFr
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem perFr_add {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : Frame X.Ψ r) (v w : Fin r → E) (τ : E →+* ℂ)
    (i : ℕ) : perFr X x (v + w) τ i = perFr X x v τ i + perFr X x w τ i := by
  have he : ∀ τ' : E →+* ℂ, ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ' (v + w) =
      ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ' v + ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ' w := fun τ' => by
    funext a; simp [ReciprocityTheory.ChartRestriction.G.FD.Data.emb, map_add]
  unfold perFr
  split_ifs <;> simp [he, Matrix.mulVec_add, hermC, map_add, mul_add, Finset.sum_add_distrib]
theorem perFr_zero {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : Frame X.Ψ r) (τ : E →+* ℂ) (i : ℕ) :
    perFr X x 0 τ i = 0 := by
  have he : ∀ τ' : E →+* ℂ, ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ' (0 : Fin r → E) = 0 := fun τ' => by
    funext a; simp [ReciprocityTheory.ChartRestriction.G.FD.Data.emb]
  unfold perFr
  split_ifs <;> simp [he, hermC]
end PerFr
section Fam
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}
def letE (Dw : Datum H) : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ) :=
  (Fintype.equivFin _).symm
def tyOf (c : Coeff l) (σ : c.F →+* ℂ) (Dw : Datum H) : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) → (E →+* ℂ) :=
  fun i => relab c σ (letE Dw i).1
def RelabType (c : Coeff l) (σ : c.F →+* ℂ) (Dw : Datum H) : Prop := IsTypeFn H Dw.p Dw.q (tyOf c σ Dw)
variable {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
def famOf (hN : N1c) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (hpq : 1 ≤ Dw.p + Dw.q) (hσ : GoodEmb c σ)
    (hR : RelabType c σ Dw) :
    FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (letE Dw j).1) :=
  Classical.choice (hN E H Dw l Xo _ _ _ hpq hσ hR)
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
def eb {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) : Fin g → ℂ :=
  Pi.single (e.symm ⟨τ, i⟩) 1
def pmOf {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
    (M : ModelsOf F r) (k : Fin F.n) (x : Frame (M.X k).Ψ r) : (F.Di k).La →+ (Fin g → ℂ) where
  toFun a := fun j => perFr (M.X k) x (M.φ k a : Fin r → E) (relab c σ (e j).1) (e j).2
  map_zero' := by
    funext j
    simp [perFr_zero]
  map_add' a b := by
    funext j
    simp [perFr_add]
def ExpUniq {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) : Prop :=
  ∀ i (P P' : (F.Di i).La →+ (Fin g → ℂ)), IsPeriod (F.Di i) (fun j => relab c σ (e j).1) P →
    IsPeriod (F.Di i) (fun j => relab c σ (e j).1) P' →
    ∀ (gam : (F.Di i).La ≃ₗ[𝓞 E] (F.Di i).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      (∀ a b, (F.Di i).EF (gam a) (gam b) = (F.Di i).EF a b) →
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di i).La), ∃ b, gam a = a + l.M • b) →
      (∀ a, ∃ b, gam a = a + l.A • b) → (∀ a, P' (gam a) = h (P a)) →
      ∀ z, (F.ex i P' (h z)).left = (F.ex i P z).left
def ExpLin {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) : Prop :=
  ∀ i (P : (F.Di i).La →+ (Fin g → ℂ)), IsPeriod (F.Di i) (fun j => relab c σ (e j).1) P →
    ∀ (m : ℕ) (w : Fin m → (Fin g → ℂ)) (vs : Fin m → (Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left))
      (cf : Fin m → ℂ) (v : Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left),
      (∀ j, IsDerivAt0 (fun z => (F.ex i P z).left) (w j) (vs j)) →
      IsDerivAt0 (fun z => (F.ex i P z).left) (∑ j, cf j • w j) v → IsCombAt (F.u i P) vs cf v
def ExpTan {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) : Prop :=
  ∀ i (P : (F.Di i).La →+ (Fin g → ℂ)), IsPeriod (F.Di i) (fun j => relab c σ (e j).1) P →
    ∀ (w : Fin g → ℂ) (v : Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left),
      IsDerivAt0 (fun z => (F.ex i P z).left) w v →
      IsTanAt (F.u i P) v ∧ ∀ j, w = Pi.single j 1 → IsEigAt c (e j).1 v
def PerDom {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) : Prop :=
  ModelBase M → IsTypeFn H Dw.p Dw.q (fun j => relab c σ (e j).1) →
    ∀ k (x : Frame (M.X k).Ψ r), x ∈ (M.X k).dom → IsPeriod (F.Di k) (fun j => relab c σ (e j).1) (pmOf e M k x)
def PerOntoX {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) : Prop :=
  ModelBase M → IsTypeFn H Dw.p Dw.q (fun j => relab c σ (e j).1) →
    ∀ k (P : (F.Di k).La →+ (Fin g → ℂ)), IsPeriod (F.Di k) (fun j => relab c σ (e j).1) P →
      ∃ x ∈ (M.X k).dom, pmOf e M k x = P
def LieEig {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
      (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) : Prop :=
  ∀ i (P : (F.Di i).La →+ (Fin g → ℂ)), IsPeriod (F.Di i) (fun j => relab c σ (e j).1) P →
    ∀ τ (v : Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left), IsTanAt (S := CAt σ) (F.u i P) v → IsEigAt c τ v →
      ∃ a : Fin (Dw.mult τ) → ℂ, IsDerivAt0 (fun z => (F.ex i P z).left) (∑ j, a j • eb e τ j) v
def offZero {Comp : Type} (X : Comp → Data E r) : Submodule ℂ (FDSec X) where
  carrier := {P | ∀ k x, x ∉ (X k).dom → P k x = 0}
  zero_mem' _ _ _ := rfl
  add_mem' hP hQ k x hx := by simp [hP k x hx, hQ k x hx]
  smul_mem' a P hP k x hx := by simp [hP k x hx]
def holSub0 {Comp : Type} (X : Comp → Data E r) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) : Submodule ℂ (FDSec X) :=
  holSub X la ⊓ offZero X
end Fam
def XiSign {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type} (X : Comp → Data E r) : Prop :=
  ∀ k, ∀ τ ∈ (X k).Ψ, (τ (X k).ξ0).im < 0
def ExpUniqSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ), GoodEmb c σ →
    ∀ {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
      (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)), IsTypeFn H Dw.p Dw.q (fun j => relab c σ (e j).1) → ExpUniq e F
def ExpLinSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ), GoodEmb c σ →
    ∀ {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
      (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)), IsTypeFn H Dw.p Dw.q (fun j => relab c σ (e j).1) → ExpLin e F
def ExpTanSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ), GoodEmb c σ →
    ∀ {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
      (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)), IsTypeFn H Dw.p Dw.q (fun j => relab c σ (e j).1) → ExpTan e F
def LieEigSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ), GoodEmb c σ →
    ∀ {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
      (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)), IsTypeFn H Dw.p Dw.q (fun j => relab c σ (e j).1) → LieEig e F
def PerDomSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ), GoodEmb c σ →
    ∀ {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
      (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), XiSign M.X → PerDom e F M
def PerOntoXSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ), GoodEmb c σ →
    ∀ {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
      (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), XiSign M.X → PerOntoX e F M
def FramesExSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ), GoodEmb c σ →
    ∀ {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
      (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), IsTypeFn H Dw.p Dw.q (fun j => relab c σ (e j).1) → ModelBase M → XiSign M.X →
      ∃ un, FramesOK e F M un
def HolFinSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Comp : Type) [Fintype Comp]
    (X : Comp → Data E r) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r), FiniteDimensional ℂ (holSub0 X la)
end Formalism.L2.PjFree.Rows


