-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
-- name    : Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T22:03:21.962902+00:00
-- url     : https://prove2.me/theorems/7e2c5a23-1684-4cff-8945-5ae5f0cf88be
-- title:
--   H1 Commutes Base Change
-- statement:
--   Definitions and structural lemmas for H1 Commutes Base Change, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/TemperedRepresentationTheory/HodgeWedgeFields/H1CommutesBaseChange.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_cup
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_smul
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_toO
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_smul
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply


set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR
attribute [local instance] Over.cartesianMonoidalCategory
namespace MainStatements.Hodge
def VB (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (n : ℕ) : Prop :=
  Module.Finite R M ∧ Module.Projective R M ∧ ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = n
def QIsoAt {R A₀ A₁ A₂ B₀ B₁ B₂ : Type} [CommRing R] [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂]
    [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂] [Module R A₀] [Module R A₁] [Module R A₂] [Module R B₀]
    [Module R B₁] [Module R B₂] (a₀ : A₀ →ₗ[R] A₁) (a₁ : A₁ →ₗ[R] A₂) (b₀ : B₀ →ₗ[R] B₁) (b₁ : B₁ →ₗ[R] B₂)
    (f : A₁ →ₗ[R] B₁) : Prop :=
  (∀ x, a₁ x = 0 → (∃ y, b₀ y = f x) → ∃ y, a₀ y = x) ∧ ∀ z, b₁ z = 0 → ∃ x y, a₁ x = 0 ∧ f x - z = b₀ y
section Cochains
variable {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type} [Category.{0} C] [Category.{0} C']
def face {n : ℕ} (i : Fin (n + 2)) (c : Fin (n + 2) ⥤ C) : Fin (n + 1) ⥤ C :=
  (Fin.succAboveOrderEmb i).monotone.functor ⋙ c
variable (F : C ⥤ CommAlgCat.{0} R)
abbrev Cn (n : ℕ) : Type := ∀ c : Fin (n + 1) ⥤ C, F.obj (c.obj (Fin.last n))
def cof (n : ℕ) (i : Fin (n + 2)) : Cn F n →ₗ[R] Cn F (n + 1) :=
  LinearMap.pi fun c ↦ (mp F (c.map (homOfLE (Fin.le_last (i.succAbove (Fin.last n)))))).toLinearMap ∘ₗ
    LinearMap.proj (R := R) (φ := fun c : Fin (n + 1) ⥤ C ↦ (F.obj (c.obj (Fin.last n)) : Type)) (face i c)
def dn (n : ℕ) : Cn F n →ₗ[R] Cn F (n + 1) := ∑ i : Fin (n + 2), ((-1 : R) ^ (i : ℕ)) • cof F n i
abbrev Hs (n : ℕ) : Type :=
  LinearMap.ker (dn F (n + 1)) ⧸ (LinearMap.range (dn F n)).comap (LinearMap.ker (dn F (n + 1))).subtype
def d2 : C2 F →ₗ[R] C3 F := LinearMap.fst R _ _ ∘ₗ dTot2 F ∘ₗ LinearMap.inl R _ _
variable {F} in

def pulln {F' : C' ⥤ CommAlgCat.{0} R} (m : CoefMap (RingHom.id R) F F') (n : ℕ) : Cn F n →ₗ[R] Cn F' n where
  toFun f c := m.α (c.obj (Fin.last n)) (f (c ⋙ m.G))
  map_add' _ _ := funext fun _ ↦ map_add _ _ _
  map_smul' _ _ := funext fun _ ↦ m.smul _ _ _
variable {F} in

def AllQIso {F' : C' ⥤ CommAlgCat.{0} R} (m : CoefMap (RingHom.id R) F F') : Prop :=
  QIsoAt (0 : R →ₗ[R] Cn F 0) (dn F 0) (0 : R →ₗ[R] Cn F' 0) (dn F' 0) (pulln m 0) ∧
    ∀ n, QIsoAt (dn F n) (dn F (n + 1)) (dn F' n) (dn F' (n + 1)) (pulln m (n + 1))
def Stein : Prop :=
  Function.Exact (Algebra.linearMap R (C0 F)) (d0 F) ∧ Function.Injective (algebraMap R (C0 F))
def evForm (T : C) : Glob1 F →ₗ[R] Ω[F.obj T⁄R] := LinearMap.proj T ∘ₗ (Glob1 F).subtype
def Par : Prop := ∀ T : C, IsBaseChange (F.obj T) (evForm F T)
def Wedge : Prop :=
  ∃ e : ⋀[R]^2 (H1 F) ≃ₗ[R] H2 F, ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = cup F a b
def WedgeHyp : Prop :=
  ∃ e : ⋀[R]^2 (Hyp1 F) ≃ₗ[R] Hyp2 F, ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = cupHyp F a b
def Bi : Prop :=
  ∃ (D : Type) (_ : Category.{0} D) (G : D ⥤ CommAlgCat.{0} R) (m p q : CoefMap (RingHom.id R) F G),
    Stein G ∧ Par G ∧ Function.Bijective (fun x : H1 F × H1 F ↦ p.pull1 x.1 + q.pull1 x.2) ∧
    Function.Bijective (fun x : Glob1 F × Glob1 F ↦ pullGlob1 p x.1 + pullGlob1 q x.2) ∧
    (∀ c, m.pull1 c = p.pull1 c + q.pull1 c) ∧ (∀ ω, pullGlob1 m ω = pullGlob1 p ω + pullGlob1 q ω) ∧
    ∀ c, pullHyp1 m c = pullHyp1 p c + pullHyp1 q c
def Perf : Prop :=
  ∃ (P₀ P₁ P₂ P₃ : ModuleCat.{0} R) (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (a₂ : P₂ →ₗ[R] P₃)
    (ψ₀ : P₀ →ₗ[R] C0 F) (ψ₁ : P₁ →ₗ[R] C1 F) (ψ₂ : P₂ →ₗ[R] C2 F),
    (Module.Finite R P₀ ∧ Module.Projective R P₀) ∧ (Module.Finite R P₁ ∧ Module.Projective R P₁) ∧
    (Module.Finite R P₂ ∧ Module.Projective R P₂) ∧ (Module.Finite R P₃ ∧ Module.Projective R P₃) ∧
    a₁ ∘ₗ a₀ = 0 ∧ a₂ ∘ₗ a₁ = 0 ∧ ψ₁ ∘ₗ a₀ = d0 F ∘ₗ ψ₀ ∧ ψ₂ ∘ₗ a₁ = d1 F ∘ₗ ψ₁ ∧
    (∃ ψ₃ : P₃ →ₗ[R] C3 F, ψ₃ ∘ₗ a₂ = d2 F ∘ₗ ψ₂) ∧
    ∀ M : ModuleCat.{0} R,
      QIsoAt (0 : R →ₗ[R] M ⊗[R] P₀) (a₀.lTensor M) (0 : R →ₗ[R] M ⊗[R] C0 F) ((d0 F).lTensor M) (ψ₀.lTensor M) ∧
      QIsoAt (a₀.lTensor M) (a₁.lTensor M) ((d0 F).lTensor M) ((d1 F).lTensor M) (ψ₁.lTensor M) ∧
      QIsoAt (a₁.lTensor M) (a₂.lTensor M) ((d1 F).lTensor M) ((d2 F).lTensor M) (ψ₂.lTensor M)
structure BC [Algebra R R'] (F' : C ⥤ CommAlgCat.{0} R') where

  α : ∀ T : C, F.obj T →+* F'.obj T
  naturality : ∀ {T T' : C} (φ : T ⟶ T') (b : F.obj T), α T' (mp F φ b) = mp F' φ (α T b)
  smul : ∀ (T : C) (r : R) (b : F.obj T), α T (r • b) = algebraMap R R' r • α T b
  bij : ∀ T : C, ∃ e : R' ⊗[R] F.obj T ≃ₗ[R'] F'.obj T, ∀ b, e (1 ⊗ₜ b) = α T b
variable {F} in

def BC.coef [Algebra R R'] {F' : C ⥤ CommAlgCat.{0} R'} (m : BC F F') : CoefMap (algebraMap R R') F F' where
  G := 𝟭 C
  α := m.α
  naturality := m.naturality
  smul := m.smul
def H1CommutesBaseChange : Prop :=
  ∀ (R' : Type) [CommRing R'] [Algebra R R'] (F' : C ⥤ CommAlgCat.{0} R') (m : BC F F'),
    ∃ e : R' ⊗[R] H1 F ≃ₗ[R'] H1 F', ∀ c, e (1 ⊗ₜ c) = m.coef.pull1 c
@[reducible] def box : C × C ⥤ CommAlgCat.{0} R where
  obj T := CommAlgCat.of R (F.obj T.1 ⊗[R] F.obj T.2)
  map φ := CommAlgCat.ofHom (Algebra.TensorProduct.map (mp F φ.1) (mp F φ.2))
  map_id T := CommAlgCat.hom_ext (Algebra.TensorProduct.ext' fun a b ↦
    congrArg₂ (fun x y ↦ x ⊗ₜ[R] y) (mp_id F T.1 a) (mp_id F T.2 b))
  map_comp φ ψ := CommAlgCat.hom_ext (Algebra.TensorProduct.ext' fun a b ↦
    congrArg₂ (fun x y ↦ x ⊗ₜ[R] y) (mp_comp F φ.1 ψ.1 a) (mp_comp F φ.2 ψ.2 b))
def boxL : CoefMap (RingHom.id R) F (box F) where
  G := CategoryTheory.Prod.fst C C
  α T := (Algebra.TensorProduct.includeLeft : F.obj T.1 →ₐ[R] F.obj T.1 ⊗[R] F.obj T.2).toRingHom
  naturality {T T'} φ b := (congrArg (fun y ↦ mp F φ.1 b ⊗ₜ[R] y) (map_one (mp F φ.2))).symm
  smul T r b := map_smul (Algebra.TensorProduct.includeLeft : F.obj T.1 →ₐ[R] F.obj T.1 ⊗[R] F.obj T.2) r b
def boxR : CoefMap (RingHom.id R) F (box F) where
  G := CategoryTheory.Prod.snd C C
  α T := (Algebra.TensorProduct.includeRight : F.obj T.2 →ₐ[R] F.obj T.1 ⊗[R] F.obj T.2).toRingHom
  naturality {T T'} φ b := (congrArg (fun x ↦ x ⊗ₜ[R] mp F φ.2 b) (map_one (mp F φ.1))).symm
  smul T r b := map_smul (Algebra.TensorProduct.includeRight : F.obj T.2 →ₐ[R] F.obj T.1 ⊗[R] F.obj T.2) r b
def evL (T₀ T : C) (ε : F.obj T₀ →ₐ[R] R) : F.obj T₀ ⊗[R] F.obj T →ₐ[R] F.obj T :=
  Algebra.TensorProduct.lift ((Algebra.ofId R (F.obj T)).comp ε) (AlgHom.id R _) fun _ _ ↦ Commute.all _ _
def boxE (T₀ : C) (ε : F.obj T₀ →ₐ[R] R) : CoefMap (RingHom.id R) (box F) F where
  G := CategoryTheory.Prod.sectR T₀ C
  α T := (evL F T₀ T ε).toRingHom
  naturality {T T'} φ b := by
    have e : (evL F T₀ T' ε).comp (Algebra.TensorProduct.map (mp F (𝟙 T₀)) (mp F φ)) =
        (mp F φ).comp (evL F T₀ T ε) := Algebra.TensorProduct.ext' fun x y ↦ by
      simp [evL, mp_id, Algebra.ofId_apply]
    exact congrArg (fun t ↦ t b) e
  smul T r b := map_smul (evL F T₀ T ε) r b
def Hopf (b : Prop) : Prop :=
  ∃ (D : Type) (_ : Category.{0} D) (G : D ⥤ CommAlgCat.{0} R) (π : CoefMap (RingHom.id R) (box F) G)
    (m : CoefMap (RingHom.id R) F G), AllQIso π ∧
    (∀ c, m.pull1 c = π.pull1 ((boxL F).pull1 c + (boxR F).pull1 c)) ∧
    (b → ∃ (T₀ : C) (ε : F.obj T₀ →ₐ[R] R), ∀ y w, π.pull2 w = m.pull2 y → (boxE F T₀ ε).pull2 w = y)
end Cochains
structure Sys (X : Scheme.{0}) (P : Type) [SemilatticeInf P] where

  u : P → X.affineOpens
  map_inf : ∀ a b, (u (a ⊓ b)).1 = (u a).1 ⊓ (u b).1
  cover : ⨆ a, (u a).1 = ⊤
variable {X : Scheme.{0}} {P : Type} [SemilatticeInf P]
theorem Sys.mono (S : Sys X P) : Monotone S.u := fun a b h ↦ by
  have e := S.map_inf a b
  rw [inf_eq_left.2 h] at e
  exact (e.le.trans inf_le_right : (S.u a).1 ≤ (S.u b).1)
def Sys.fn (S : Sys X P) : Pᵒᵖ ⥤ AffOp X := S.mono.functor.op
abbrev OSys {R : Type} [CommRing R] (s : X ⟶ Sp R) (S : Sys X P) : Pᵒᵖ ⥤ CommAlgCat.{0} R := S.fn ⋙ OAff s
abbrev resSys {R : Type} [CommRing R] (s : X ⟶ Sp R) (S : Sys X P) : CoefMap (RingHom.id R) (OAff s) (OSys s S) :=
  CoefMap.restrict (OAff s) S.fn
theorem wOver {R : Type} [CommRing R] {Y Z : Over (Sp R)} (f : Y ⟶ Z) :
    f.left ≫ Z.hom = Y.hom ≫ spMap (RingHom.id R) := by
  rw [GlobalTheory.Cris.spMap_id, Category.comp_id]; exact Over.w f
def tsz {R B W M : Type} [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup W] [Module R W] [Module Rᵐᵒᵖ W]
    [IsCentralScalar R W] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module R M]
    [IsScalarTower R B M] (u : W →ₗ[R] M) : TrivSqZeroExt R W →+* TrivSqZeroExt B M where
  toFun c := TrivSqZeroExt.inl (algebraMap R B c.fst) + TrivSqZeroExt.inr (u c.snd)
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by ext <;> simp
def IsCot {R : Type} [CommRing R] (s : X ⟶ Sp R) (e : Sp R ⟶ X) (W : Type) [AddCommGroup W] [Module R W]
    [Module Rᵐᵒᵖ W] [IsCentralScalar R W] (y₀ : Sp (TrivSqZeroExt R W) ⟶ X) : Prop :=
  y₀ ≫ s = spMap (TrivSqZeroExt.inlHom R W) ∧ spMap (TrivSqZeroExt.fstHom R R W).toRingHom ≫ y₀ = e ∧
    ∀ (B : Type) [CommRing B] [Algebra R B] (M : Type) [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M]
      [IsCentralScalar B M] [Module R M] [IsScalarTower R B M] (y : Sp (TrivSqZeroExt B M) ⟶ X),
      y ≫ s = spMap ((TrivSqZeroExt.inlHom B M).comp (algebraMap R B)) →
      spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ y = spMap (algebraMap R B) ≫ e →
      ∃! u : W →ₗ[R] M, y = spMap (tsz u) ≫ y₀
def AllAb (Q : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], ℕ → Prop) : Prop :=
  ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → Q R A g
def CotSt : Prop :=
  ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (e : Sp R ⟶ X) (g : ℕ), e ≫ s = 𝟙 _ →
    SmoothOfRelativeDimension g s → ∃ (W : Type) (_ : AddCommGroup W) (_ : Module R W) (_ : Module Rᵐᵒᵖ W)
      (_ : IsCentralScalar R W) (y₀ : Sp (TrivSqZeroExt R W) ⟶ X), VB R W g ∧ IsCot s e W y₀
def DescentSt : Prop :=
  ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsSeparated s →
    ∀ (P : Type) [SemilatticeInf P] (S : Sys X P), AllQIso (resSys s S)
def LowSt : Prop :=
  ∀ (R : Type) [CommRing R] (C C' : Type) [Category.{0} C] [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R)
    (F' : C' ⥤ CommAlgCat.{0} R) (m : CoefMap (RingHom.id R) F F'), AllQIso m →
    Function.Bijective m.pull1 ∧ Function.Bijective m.pull2 ∧ (Stein F ↔ Stein F')
def SysBCSt : Prop :=
  ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R')
    (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap R R'))), IsSeparated s →
    ∀ (P : Type) [SemilatticeInf P] (S : Sys X P), ∃ (S' : Sys X' P) (m : BC (OSys s S) (OSys s' S')),
      ∀ c c', m.coef.pull1 ((resSys s S).pull1 c) = (resSys s' S').pull1 c' → IsPullO h.w c c'
def PerfSt : Prop :=
  ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), Smooth s → IsProper s →
    ∃ (P : Type) (_ : SemilatticeInf P) (_ : Finite P) (S : Sys X P), Perf (OSys s S)
def FinCohSt : Prop :=
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsProper s →
    ∀ (P : Type) [SemilatticeInf P] [Finite P] (S : Sys X P),
      Module.Finite R (LinearMap.ker (dn (OSys s S) 0)) ∧ ∀ n, Module.Finite R (Hs (OSys s S) n)
def SteinSt : Prop := AllAb fun _ _ A _ _ ↦ Stein (OAff A.hom)
def ParSt : Prop := AllAb fun R _ A _ g ↦ Par (OAff A.hom) ∧ VB R (GlobForm A.hom) g
def AxOSt : Prop := AllAb fun _ _ A _ _ ↦ ∀ c : HO1 (A ⊗ A).hom,
  IsPullO (wOver (lift (𝟙 A) (1 : A ⟶ A))) c 0 → IsPullO (wOver (lift (1 : A ⟶ A) (𝟙 A))) c 0 → c = 0
def AxFormSt : Prop := AllAb fun _ _ A _ _ ↦ ∀ c : GlobForm (A ⊗ A).hom,
  IsPullForm (wOver (lift (𝟙 A) (1 : A ⟶ A))) c 0 → IsPullForm (wOver (lift (1 : A ⟶ A) (𝟙 A))) c 0 → c = 0
def H1StructureBundle : Prop := AllAb fun R _ A _ g ↦ VB R (HO1 A.hom) g
def VanSt : Prop := AllAb fun R _ A _ g ↦ IsField R → ∀ (P : Type) [SemilatticeInf P] [Finite P] (S : Sys A.left P)
  (n : ℕ), g ≤ n → Function.Exact (dn (OSys A.hom S) n) (dn (OSys A.hom S) (n + 1))
def HopfSt : Prop := AllAb fun R _ A _ _ ↦ ∀ (P : Type) [SemilatticeInf P] [Finite P] (S : Sys A.left P),
  Hopf (OSys A.hom S) (IsField R)
def BiSt : Prop := AllAb fun _ _ A _ _ ↦ Bi (OAff A.hom)
def WedgeFieldSt : Prop := AllAb fun R _ A _ _ ↦ IsField R → Wedge (OAff A.hom)
def WedgeSt : Prop := AllAb fun _ _ A _ _ ↦ Wedge (OAff A.hom)
def OBCSt : Prop := AllAb fun R _ A _ _ ↦
  ∀ (R' : Type) [CommRing R'] [Algebra R R'] (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ A.left)
    (h : IsPullback φ s' A.hom (spMap (algebraMap R R'))),
    ∃ e : R' ⊗[R] HO1 A.hom ≃ₗ[R'] HO1 s', ∀ c, IsPullO h.w c (e (1 ⊗ₜ c))
def FormBCSt : Prop := AllAb fun R _ A _ _ ↦
  ∀ (R' : Type) [CommRing R'] [Algebra R R'] (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ A.left)
    (h : IsPullback φ s' A.hom (spMap (algebraMap R R'))),
    ∃ e : R' ⊗[R] GlobForm A.hom ≃ₗ[R'] GlobForm s', ∀ c, IsPullForm h.w c (e (1 ⊗ₜ c))
def DegenSt : Prop := AllAb fun _ _ A _ _ ↦ ClosedForm A.hom = ⊤ ∧ Function.Surjective (toHO1 A.hom)
def WedgeHypSt : Prop := AllAb fun _ _ A _ _ ↦ WedgeHyp (OAff A.hom)
def CmpSt : Prop :=
  ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsSeparated s →
    ∀ (P : Type) [SemilatticeInf P] [Finite P] (S : Sys X P),
      letI := GlobalTheory.algebraΓOfHom s
      Nonempty (LinearMap.ker (dn (OSys s S) 0) ≃ₗ[R] GlobalTheory.coh (GlobalTheory.structureModule X) 0) ∧
        ∀ n, Nonempty (Hs (OSys s S) n ≃ₗ[R] GlobalTheory.coh (GlobalTheory.structureModule X) (n + 1))
def AllF (Q : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C], (C ⥤ CommAlgCat.{0} R) → Prop) : Prop :=
  ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), Q R C F
def AllFin (Q : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C], (C ⥤ CommAlgCat.{0} R) → Prop) : Prop :=
  ∀ (R : Type) [CommRing R] (P : Type) [SemilatticeInf P] [Finite P] (F : Pᵒᵖ ⥤ CommAlgCat.{0} R), Q R Pᵒᵖ F
def Framed {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) : Prop :=
  Stein F ∧ Par F ∧ Module.Finite R (Glob1 F) ∧ Module.Projective R (Glob1 F)
def OneFormCohSt : Prop := AllF fun R _ C _ F ↦ Framed F →
  ∃ mu : Z1 F ⊗[R] Glob1 F →ₗ[R] A1 F, (∀ f ω T T' φ, mu (f ⊗ₜ ω) T T' φ = f.1 T T' φ • ω.1 T') ∧
    (∀ a : A1 F, (∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''),
      a T T'' (φ ≫ ψ) = p1 F ψ (a T T' φ) + a T' T'' ψ) → ∃ t, mu t = a) ∧
    ∀ (t : Z1 F ⊗[R] Glob1 F) (β : A0 F), (∀ T T' φ, mu t T T' φ = β T' - p1 F φ (β T)) →
      (H1.mk F).rTensor (Glob1 F) t = 0
def TwoFormCohSt : Prop := AllF fun R _ C _ F ↦ Framed F →
  ∃ ν : ⋀[R]^2 (Glob1 F) →ₗ[R] W0 F 2,
    (∀ a b T, ν (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T)) ∧ Function.Injective ν ∧
    ∀ w : W0 F 2, (∀ (T T' : C) (φ : T ⟶ T'), w T' = pOm F 2 φ (w T)) → ∃ t, ν t = w
def DictSt : Prop := AllF fun R _ C _ F ↦
  ∃ (e₀ : Cn F 0 ≃ₗ[R] C0 F) (e₁ : Cn F 1 ≃ₗ[R] C1 F) (e₂ : Cn F 2 ≃ₗ[R] C2 F) (e₃ : Cn F 3 ≃ₗ[R] C3 F),
    (∀ f T, e₀ f T = f (ComposableArrows.mk₀ T)) ∧ (∀ f T T' φ, e₁ f T T' φ = f (ComposableArrows.mk₁ φ)) ∧
    (∀ f T T' T'' φ ψ, e₂ f T T' T'' φ ψ = f (ComposableArrows.mk₂ φ ψ)) ∧
    (∀ f T T' T'' T''' φ ψ χ, e₃ f T T' T'' T''' φ ψ χ = f (ComposableArrows.mk₃ φ ψ χ)) ∧
    (∀ f, e₁ (dn F 0 f) = d0 F (e₀ f)) ∧ (∀ f, e₂ (dn F 1 f) = d1 F (e₁ f)) ∧ ∀ f, e₃ (dn F 2 f) = d2 F (e₂ f)
def CxSt : Prop := AllF fun R _ _ _ F ↦ (∀ n, dn F (n + 1) ∘ₗ dn F n = 0) ∧
  ∀ (D : Type) [Category.{0} D] (G : D ⥤ CommAlgCat.{0} R) (m : CoefMap (RingHom.id R) F G) (n : ℕ),
    pulln m (n + 1) ∘ₗ dn F n = dn G n ∘ₗ pulln m n
def HtpySt : Prop := AllF fun R _ _ _ F ↦
  ∀ (D : Type) [Category.{0} D] (G : D ⥤ CommAlgCat.{0} R) (m m' : CoefMap (RingHom.id R) F G) (θ : m.G ⟶ m'.G),
    (∀ T b, m'.α T (mp F (θ.app T) b) = m.α T b) →
    (∀ z, dn F 0 z = 0 → pulln m 0 z = pulln m' 0 z) ∧
      ∀ n z, dn F (n + 1) z = 0 → ∃ y, pulln m (n + 1) z - pulln m' (n + 1) z = dn G n y
def QCalcSt : Prop := AllF fun R _ _ _ F ↦
  ∀ (D E : Type) [Category.{0} D] [Category.{0} E] (G : D ⥤ CommAlgCat.{0} R) (H : E ⥤ CommAlgCat.{0} R)
    (m : CoefMap (RingHom.id R) F G) (n : CoefMap (RingHom.id R) G H) (k : CoefMap (RingHom.id R) F H),
    (∀ i z, pulln k i z = pulln n i (pulln m i z)) →
    (AllQIso m → AllQIso n → AllQIso k) ∧ (AllQIso m → AllQIso k → AllQIso n) ∧ (AllQIso n → AllQIso k → AllQIso m)
structure Proj {R : Type} [CommRing R] {C D : Type} [Category.{0} C] [Category.{0} D] (F : C ⥤ CommAlgCat.{0} R)
    (G : C × D ⥤ CommAlgCat.{0} R) where

  α : ∀ T : C × D, F.obj T.1 →ₐ[R] G.obj T
  naturality : ∀ {T T' : C × D} (φ : T ⟶ T') (b : F.obj T.1), α T' (mp F φ.1 b) = mp G φ (α T b)
def Proj.coef {R : Type} [CommRing R] {C D : Type} [Category.{0} C] [Category.{0} D] {F : C ⥤ CommAlgCat.{0} R}
    {G : C × D ⥤ CommAlgCat.{0} R} (m : Proj F G) : CoefMap (RingHom.id R) F G where
  G := CategoryTheory.Prod.fst C D
  α T := (m.α T).toRingHom
  naturality := m.naturality
  smul T r b := map_smul (m.α T) r b
def Proj.fib {R : Type} [CommRing R] {C D : Type} [Category.{0} C] [Category.{0} D] {F : C ⥤ CommAlgCat.{0} R}
    {G : C × D ⥤ CommAlgCat.{0} R} (m : Proj F G) (T : C) :
    F.obj T →ₗ[R] Cn (CategoryTheory.Prod.sectR T D ⋙ G) 0 :=
  LinearMap.pi fun c ↦ (m.α (T, c.obj (Fin.last 0))).toLinearMap
def FubiniSt : Prop := AllF fun R _ C _ F ↦
  ∀ (D : Type) [Category.{0} D] [Quiver.IsThin C] [Quiver.IsThin D] (G : C × D ⥤ CommAlgCat.{0} R) (m : Proj F G),
    (∀ T, Function.Injective (m.fib T) ∧ Function.Exact (m.fib T) (dn (CategoryTheory.Prod.sectR T D ⋙ G) 0) ∧
      ∀ n, Function.Exact (dn (CategoryTheory.Prod.sectR T D ⋙ G) n) (dn (CategoryTheory.Prod.sectR T D ⋙ G) (n + 1))) →
    AllQIso m.coef
def AffAcycSt : Prop :=
  ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (W : X.affineOpens) (P : Type) [SemilatticeInf P]
    [Finite P] (u : P →o X.affineOpens) (hle : ∀ a, (u a).1 ≤ W.1),
    (∀ a b, (u (a ⊓ b)).1 = (u a).1 ⊓ (u b).1) → ⨆ a, (u a).1 = W.1 →
    let F : Pᵒᵖ ⥤ CommAlgCat.{0} R := u.monotone.functor.op ⋙ OAff s
    let aug : Sec s W.1 →ₗ[R] Cn F 0 := LinearMap.pi fun c ↦ (Sec.res s (hle (c.obj (Fin.last 0)).unop)).toLinearMap
    Function.Injective aug ∧ Function.Exact aug (dn F 0) ∧ ∀ n, Function.Exact (dn F n) (dn F (n + 1))
def ClosedSt : Prop := AllF fun _ _ _ _ F ↦ Framed F → Bi F → Closed1 F = ⊤
def LiftSt : Prop := AllF fun _ _ _ _ F ↦ Framed F → Bi F → Closed1 F = ⊤ → Function.Surjective (toO F)
def AltSt : Prop := AllF fun _ _ _ _ F ↦ Framed F → Bi F → Closed1 F = ⊤ → Function.Surjective (toO F) →
  (∀ c, cup F c c = 0) → ∀ c, cupHyp F c c = 0
def H2FieldHypothesis : Prop := AllF fun R _ _ _ F ↦ Framed F → Module.Finite R (H1 F) → Module.Projective R (H1 F) →
  Closed1 F = ⊤ → Function.Surjective (toO F) → Wedge F → (∀ c, cupHyp F c c = 0) → WedgeHyp F
def PerfNoethSt : Prop := AllFin fun R _ _ _ F ↦ IsNoetherianRing R → (∀ T, Module.Flat R (F.obj T)) →
  Module.Finite R (LinearMap.ker (dn F 0)) → (∀ n, Module.Finite R (Hs F n)) → Perf F
def PerfBaseSt : Prop := AllFin fun R _ C _ F ↦ Perf F →
  ∀ (R' : Type) [CommRing R'] [Algebra R R'] (F' : C ⥤ CommAlgCat.{0} R'), BC F F' → Perf F'
def SteinU {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) : Prop :=
  ∀ (R' : Type) [CommRing R'] [Algebra R R'], ∃ (F' : C ⥤ CommAlgCat.{0} R') (_ : BC F F'), Stein F'
def PerfectH1BaseChange : Prop := AllFin fun R _ C _ F ↦ ∀ g : ℕ, Perf F → SteinU F → VB R (H1 F) g →
  (∀ (k : Type) [Field k] [Algebra R k], ∃ (F' : C ⥤ CommAlgCat.{0} k) (_ : BC F F'),
    Module.finrank k (H1 F') = g) → H1CommutesBaseChange F
def PerfectH2FromFibres : Prop := AllFin fun R _ C _ F ↦ ∀ g : ℕ, Perf F → SteinU F → VB R (H1 F) g → H1CommutesBaseChange F →
  (∀ (k : Type) [Field k] [Algebra R k], ∃ (F' : C ⥤ CommAlgCat.{0} k) (_ : BC F F'), Wedge F') →
  VB R (H2 F) (g.choose 2) ∧ Submodule.span R (Set.range fun x : H1 F × H1 F ↦ cup F x.1 x.2) = ⊤
def WedgeOfSt : Prop := AllFin fun R _ _ _ F ↦ ∀ g : ℕ, Hopf F False → VB R (H1 F) g → H1CommutesBaseChange F →
  VB R (H2 F) (g.choose 2) → Submodule.span R (Set.range fun x : H1 F × H1 F ↦ cup F x.1 x.2) = ⊤ → Wedge F
def HopfFieldSt : Prop := AllFin fun R _ _ _ F ↦ ∀ g : ℕ, IsField R → Stein F → VB R (H1 F) g →
  (∀ n, g ≤ n → Function.Exact (dn F n) (dn F (n + 1))) → Hopf F True → Wedge F
end MainStatements.Hodge


