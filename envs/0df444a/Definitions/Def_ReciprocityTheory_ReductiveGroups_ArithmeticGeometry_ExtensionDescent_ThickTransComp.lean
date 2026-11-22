-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:25:01.002245+00:00
-- url     : https://prove2.me/theorems/edbefe5b-3f20-4848-bcf2-c6713ce44e9d
-- title:
--   Thick Trans Comp
-- statement:
--   Definitions and structural lemmas for Thick Trans Comp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ThickTransComp.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.Out
open Semi
def CLND (R : Type) [CommRing R] : Prop :=
  ∃ _ : IsLocalRing R, IsNoetherianRing R ∧ IsDomain R ∧ IsIntegrallyClosed R ∧
    IsAdicComplete (IsLocalRing.maximalIdeal R) R
def AdmBase (R : Type) [CommRing R] (I : Ideal R) : Prop :=
  IsNoetherianRing R ∧ IsDomain R ∧ IsIntegrallyClosed R ∧ IsAdicComplete I R
instance PolAV.isCommMonObj {S : Scheme.{0}} (P : PolAV S) : IsCommMonObj P.A := P.isAb.comm
section Points
variable (R : Type) [CommRing R] [IsDomain R]
abbrev jK : Spec (CommRingCat.of (FractionRing R)) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
abbrev TK : Over (Spec (CommRingCat.of R)) := Over.mk (jK R)
variable {R}
abbrev ptK {B : Over (Spec (CommRingCat.of R))} (x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ B) :
    (TK R).left ⟶ B.left :=
  (toUnit (TK R) ≫ x).left
end Points
structure DegPre (R : Type) [CommRing R] [IsDomain R] where
  P : PolAV (Spec (CommRingCat.of R))
  rig : LB.Gen (P.L.pull (eSec P.A))
  rig_gen : rig.IsGen
  cub : CubicalStr P.A ⟨P.L, rig, P.isLB, rig_gen⟩
  sym : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(ι[P.A]).left, 𝟙 P.A.left] ![1, -1])
  sym_gen : sym.IsGen
  sym_rig : LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ sym (eSec P.A)) (LB.oneGen P.L)
  X : Type
  [addX : AddCommGroup X]
  [freeX : Module.Free ℤ X]
  [finX : Module.Finite ℤ X]
  c : X → (𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ P.A)
  c_add : ∀ a b, c (a + b) = padd P.A (c a) (c b)
  psi : ∀ χ : X, LB.Gen (LB.LinComb P.L (K := PUnit) (fun _ => ptK (c χ)) (fun _ => -1))
  psi_gen : ∀ χ : X, (psi χ).IsGen
namespace DegPre
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
instance : AddCommGroup D.X := D.addX
instance : Module.Free ℤ D.X := D.freeX
instance : Module.Finite ℤ D.X := D.finX
abbrev rank : ℕ := Module.finrank ℤ D.X
abbrev xK (χ : D.X) : (TK R).left ⟶ D.P.A.left := ptK (D.c χ)
def rigK := LB.pullGen D.P.L _ _ D.rig (toUnit (TK R)).left
def tau (a b : D.X) :=
  LB.mulGen D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (D.psi (a + b)) (LB.invGen D.P.L _ _ (D.psi a)))
      (LB.invGen D.P.L _ _ (D.psi b)))
    (LB.invGen D.P.L _ _ D.rigK)
def io (y χ : D.X) := D.tau y χ
def pt3 (a a' b : D.X) : (TK R).left ⟶ (G3 D.P.A).left :=
  (lift (toUnit (TK R) ≫ D.c a) (lift (toUnit (TK R) ≫ D.c a') (toUnit (TK R) ≫ D.c b))).left
def PsiEven : Prop :=
  ∀ χ : D.X, LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (D.psi (-χ)) (LB.pullGen D.P.L _ _ D.sym (D.xK χ)))
    (D.psi χ)
def TauBimult : Prop :=
  ∀ a a' b : D.X, LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (D.tau (a + a') b)
      (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a' b)))
    (LB.mulGen D.P.L _ _ _ _ (D.tau a b) (D.tau a' b))
abbrev toOpen (V : (Spec (CommRingCat.of R)).Opens) : R →+* Γ(Spec (CommRingCat.of R), V) :=
  ((Spec (CommRingCat.of R)).presheaf.map (homOfLE le_top).op).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
def PsiIn (χ : D.X) (J : Ideal R) : Prop :=
  ∀ (j : PUnit → D.P.L.ι) (V : (Spec (CommRingCat.of R)).Opens), IsAffineOpen V →
    V ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (j PUnit.unit) →
    ∀ h : jK R ⁻¹ᵁ V ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U j,
      ∃ r ∈ J.map (toOpen V),
        ((jK R).app V).hom r = ((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi χ).s j).val
end DegPre
structure DegData (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) where
  toPre : DegPre R
  psi_even : toPre.PsiEven
  tau_bimult : toPre.TauBimult
  psi_pos : ∀ χ : toPre.X, χ ≠ 0 → toPre.PsiIn χ I
  psi_tendsto : ∀ n : ℕ, {χ : toPre.X | ¬ toPre.PsiIn χ (I ^ n)}.Finite
namespace GeneratorPullback
variable {X Y Y' : Scheme.{0}} (L : LB X) {K K₁ K₂ K₃ : Type} [Fintype K] [Fintype K₁] [Fintype K₂]
  [Fintype K₃]
def powGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (n : ℕ) :
    LB.Gen (LB.LinComb L φ (fun k => (n : ℤ) * ε k)) where
  s := fun j => t.s j ^ n
def SecRel (φ₁ : K₁ → (Y' ⟶ X)) (ε₁ : K₁ → ℤ) (s₁ : LB.Sec (LB.LinComb L φ₁ ε₁))
    (φ₂ : K₂ → (Y ⟶ X)) (ε₂ : K₂ → ℤ) (s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)) (h : Y' ⟶ Y)
    (φ₃ : K₃ → (Y' ⟶ X)) (ε₃ : K₃ → ℤ) (u : LB.Gen (LB.LinComb L φ₃ ε₃)) : Prop :=
  ∀ (j₁ : K₁ → L.ι) (j₂ : K₂ → L.ι) (j₃ : K₃ → L.ι),
    LB.Coh L (Sum.elim φ₁ (Sum.elim (fun k => h ≫ φ₂ k) φ₃)) (Sum.elim j₁ (Sum.elim j₂ j₃)) →
    (Y'.presheaf.map (homOfLE (inf_le_left.trans inf_le_left :
        LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ₂ k) j₂ ⊓ LB.wchart L φ₃ j₃ ≤
          LB.wchart L φ₁ j₁)).op).hom (s₁.f j₁) =
      (Y'.presheaf.map (homOfLE ((inf_le_left.trans inf_le_right).trans
        (fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k) :
        LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ₂ k) j₂ ⊓ LB.wchart L φ₃ j₃ ≤
          h ⁻¹ᵁ LB.wchart L φ₂ j₂)).op).hom ((h.app (LB.wchart L φ₂ j₂)).hom (s₂.f j₂)) *
      (Y'.presheaf.map (homOfLE (inf_le_right :
        LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ₂ k) j₂ ⊓ LB.wchart L φ₃ j₃ ≤
          LB.wchart L φ₃ j₃)).op).hom (u.s j₃).val
end GeneratorPullback
section Fam
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
variable (F : Type) [Field F] [Algebra (FractionRing R) F]
abbrev jFK : Spec (CommRingCat.of F) ⟶ (TK R).left :=
  Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F))
abbrev TF : Over (Spec (CommRingCat.of R)) := Over.mk (jFK (R := R) F ≫ jK R)
namespace DegPre
abbrev BF : Over (Spec (CommRingCat.of R)) := TF (R := R) F ⊗ D.P.A
abbrev prB : BF D F ⟶ D.P.A := snd _ _
def trF (mu : D.X) : BF D F ⟶ BF D F :=
  lift (fst _ _) (padd D.P.A (prB D F) (toUnit _ ≫ D.c mu))
def zF : TF (R := R) F ⟶ BF D F := lift (𝟙 _) (toUnit _ ≫ η[D.P.A])
def famφ (α : D.X) : Fin 4 → ((BF D F).left ⟶ D.P.A.left) :=
  ![(prB D F).left, (padd D.P.A (prB D F) (toUnit _ ≫ D.c α)).left, (toUnit _ ≫ D.c α).left,
    (toUnit _ ≫ η[D.P.A]).left]
def famε (k : ℕ) : Fin 4 → ℤ := ![(k : ℤ) - 1, 1, -1, 1]
def deltaφ (k : ℕ) (α mu : D.X) : Fin 4 ⊕ Fin 4 → ((BF D F).left ⟶ D.P.A.left) :=
  Sum.elim (famφ D F (α + k • mu)) (fun i => (trF D F mu).left ≫ famφ D F α i)
def deltaε (k : ℕ) : Fin 4 ⊕ Fin 4 → ℤ := Sum.elim (famε k) (fun i => - famε k i)
def famMult (k : ℕ) (mu α : D.X) :=
  LB.pullGen D.P.L _ _
    (LB.mulGen D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ (D.psi mu) k) (D.tau mu α))
      (GeneratorPullback.powGen D.P.L _ _ D.rigK k))
    (jFK (R := R) F)
def FamFE (k : ℕ) (s : ∀ α : D.X, LB.Sec (LB.LinComb D.P.L (famφ D F α) (famε k))) : Prop :=
  ∀ (mu α : D.X) (u : LB.Gen (LB.LinComb D.P.L (deltaφ D F k α mu) (deltaε k))), u.IsGen →
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zF D F).left) (famMult D F k mu α) →
    GeneratorPullback.SecRel D.P.L (famφ D F (α + k • mu)) (famε k) (s (α + k • mu))
      (famφ D F α) (famε k) (s α) (trF D F mu).left (deltaφ D F k α mu) (deltaε k) u
end DegPre
structure Fam (k : ℕ) where
  s : ∀ α : D.X, LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k))
  fe : DegPre.FamFE D F k s
end Fam
section Thick
variable (R : Type) [CommRing R] (I : Ideal R)
abbrev thick (e : ℕ) : Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1))))
abbrev thickTrans (e : ℕ) :
    Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1 + 1))) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)))))
abbrev thickObj (e : ℕ) (G : Over (Spec (CommRingCat.of R))) :
    Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) :=
  (Over.pullback (thick R I e)).obj G
open scoped CategoryTheory.Obj in

example (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] : GrpObj (thickObj R I e G) :=
  inferInstance
lemma thickTrans_comp (e : ℕ) : thickTrans R I e ≫ thick R I (e + 1) = thick R I e := by
  simp only [thick, thickTrans, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp_mk]
abbrev thickMap (e : ℕ) (G : Over (Spec (CommRingCat.of R))) :
    (thickObj R I e G).left ⟶ (thickObj R I (e + 1) G).left :=
  pullback.map G.hom (thick R I e) G.hom (thick R I (e + 1)) (𝟙 _) (thickTrans R I e) (𝟙 _)
    (by simp) (by simp [thickTrans_comp])
end Thick
end ReciprocityTheory.ChartRestriction.G.Out


