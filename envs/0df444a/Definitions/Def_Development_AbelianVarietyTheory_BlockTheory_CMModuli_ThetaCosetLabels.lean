-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_ThetaCosetLabels
-- name    : Development_AbelianVarietyTheory_BlockTheory_CMModuli_ThetaCosetLabels
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:47:06.778893+00:00
-- url     : https://prove2.me/theorems/c78b42de-42f6-485b-8b47-b2371ae7a0e1
-- title:
--   Theta Coset Labels
-- statement:
--   Definitions and structural lemmas for Theta Coset Labels, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/ThetaCosetLabels.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
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
namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaCosetLabels
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] MvPolynomial.gradedAlgebra
def LevelShape (g n N' : ℕ) : Prop :=
  n.Prime ∧ Odd n ∧ ∃ k j : ℕ, 2 ≤ k ∧ 1 + 2 * (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2) < (((n ^ k) ^ 2 : ℕ) : ℝ) ∧
    N' = n ^ j * (n ^ k) ^ 2
def oRing (n : ℕ) (F : IntermediateField ℚ ℂ) : Subring ℂ :=
  Subring.closure ({x | x ∈ F ∧ IsIntegral ℤ x} ∪ {(n : ℂ)⁻¹})
def zetaO (n M : ℕ) (hM : M ≠ 0) (F : IntermediateField ℚ ℂ) (h : zeta M ∈ F) : (oRing n F)ˣ :=
  Units.ofPowEqOne
    (⟨zeta M, Subring.subset_closure (Or.inl ⟨h, (Complex.isPrimitiveRoot_exp M hM).isIntegral (Nat.pos_of_ne_zero hM)⟩)⟩ :
      oRing n F) M (Subtype.ext (by simpa [zeta] using (Complex.isPrimitiveRoot_exp M hM).pow_eq_one)) hM
abbrev Lab (g M : ℕ) : Type := Fin g ⊕ Fin g → ZMod M
def omegaLab {g M : ℕ} (a b : Lab g M) : ZMod M := ∑ i, (a (.inl i) * b (.inr i) - a (.inr i) * b (.inl i))
structure ThObj (g M : ℕ) (I : Type) {B : Type} [CommRing B] (ζ : Bˣ) {S : Scheme.{0}} (s : S ⟶ Sp B) where
  P : Out.PolAV S
  dim : P.g = g
  lev : Lab g M → (𝟙_ (Over S) ⟶ P.A)
  lev_add : ∀ a b, lev (a + b) = lev a * lev b
  geom : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : B →+* k), x ≫ s = spMap β →
    (∀ a b, toUnit (Over.mk x) ≫ lev a = toUnit (Over.mk x) ≫ lev b → a = b) ∧
    (∀ y : Over.mk x ⟶ P.A, y ^ M = 1 → ∃ a, toUnit (Over.mk x) ≫ lev a = y) ∧
    ∀ a b, Out.WeilIs P.A P.L M (toUnit (Over.mk x) ≫ lev a) (toUnit (Over.mk x) ≫ lev b)
      (unitOn (Units.map β.toMonoidHom ζ ^ (omegaLab a b).val))
  endo : I → (P.A ⟶ P.A)
  endo_hom : ∀ i, IsMonHom (endo i)
inductive EndTerm (I : Type) : Type
  | var : I → EndTerm I
  | one : EndTerm I
  | add : EndTerm I → EndTerm I → EndTerm I
  | neg : EndTerm I → EndTerm I
  | mul : EndTerm I → EndTerm I → EndTerm I
inductive EndRel (g M : ℕ) (I : Type) : Type
  | eq : EndTerm I → EndTerm I → EndRel g M I
  | adj : EndTerm I → EndTerm I → EndRel g M I
  | half : EndTerm I → EndRel g M I
  | lab : EndTerm I → Lab g M → Lab g M → EndRel g M I
section Obj
variable {g M : ℕ} {I : Type} {B : Type} [CommRing B] {ζ : Bˣ} {S S' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B}
noncomputable def ThObj.ev (X : ThObj g M I ζ s) (t : EndTerm I) : X.P.A ⟶ X.P.A :=
  EndTerm.rec (motive := fun _ => X.P.A ⟶ X.P.A) X.endo (𝟙 _) (fun _ _ f f' => f * f') (fun _ f => f⁻¹)
    (fun _ _ f f' => f' ≫ f) t
example (X : ThObj g M I ζ s) (i : I) (t t' : EndTerm I) :
    X.ev (.var i) = X.endo i ∧ X.ev .one = 𝟙 _ ∧ X.ev (.add t t') = X.ev t * X.ev t' ∧ X.ev (.neg t) = (X.ev t)⁻¹ ∧
      X.ev (.mul t t') = X.ev t' ≫ X.ev t := ⟨rfl, rfl, rfl, rfl, rfl⟩
def ThObj.Sat (X : ThObj g M I ζ s) : EndRel g M I → Prop
  | .eq t t' => X.ev t = X.ev t'
  | .adj t t' => Out.RosatiAdj X.P.A X.P.L (X.ev t) (X.ev t')
  | .half t => LBIso X.P.L (cubeLB X.P.A ![𝟙 X.P.A, X.ev t] X.P.L)
  | .lab t a b => X.lev a ≫ X.ev t = X.lev b
def IsPBVia (X' : ThObj g M I ζ s') (X : ThObj g M I ζ s) (f : S' ⟶ S) (φ : X'.P.A.left ⟶ X.P.A.left) : Prop :=
  f ≫ s = s' ∧ IsGrpPullback X'.P.A X.P.A f φ ∧ LBIso X'.P.L (X.P.L.pull φ) ∧
    ∀ a, (X'.lev a).left ≫ φ = f ≫ (X.lev a).left
def IsPB₀ (X' : ThObj g M I ζ s') (X : ThObj g M I ζ s) (f : S' ⟶ S) : Prop := ∃ φ, IsPBVia X' X f φ
def IsPB (X' : ThObj g M I ζ s') (X : ThObj g M I ζ s) (f : S' ⟶ S) : Prop :=
  ∃ φ, IsPBVia X' X f φ ∧ ∀ i, (X'.endo i).left ≫ φ = φ ≫ (X.endo i).left
end Obj
section Theta
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) {T : Over S}
def secT (y : T ⟶ A) : T.left ⟶ (T ⊗ A).left := (lift (𝟙 T) y).left
abbrev symLB (T : Over S) (M : ℤ) : LB (T ⊗ A).left :=
  LB.LinComb L (K := Fin 2) ![(snd T A).left, ((snd T A)⁻¹).left] ![M, -M]
abbrev mulLB (T : Over S) (m : ℕ) : LB (T ⊗ A).left :=
  LB.LinComb L (K := Fin 2) ![(snd T A).left, ((snd T A) ^ m).left] ![(m ^ 2 : ℕ), -1]
def IsHeis {g M : ℕ} (x : Lab g M → (T ⟶ A)) (φ : ∀ a, LB.Gen (Out.thetaLB A L M (x a))) : Prop :=
  (∀ a, (φ a).IsGen) ∧
  (∀ (a : Lab g M) (k : ℕ), LB.Gen.Corr L _ _ _ _
    (LB.mulGen L _ _ _ _ (φ a) (LB.pullGen L _ _ (φ (k • a)) (Out.translT A (x a)).left)) (φ ((k + 1) • a))) ∧
  ∃ σ : LB.Gen (symLB A L T M), σ.IsGen ∧ ∀ a, LB.Gen.Corr L _ _ _ _
    (LB.mulGen L _ _ _ _ (φ (-a)) (LB.pullGen L _ _ σ (Out.translT A (x (-a))).left))
    (LB.mulGen L _ _ _ _ σ (LB.pullGen L _ _ (φ a) (lift (fst T A) (snd T A)⁻¹).left))
variable {g : ℕ} {I : Type} {B : Type} [CommRing B] {ζ : Bˣ} {s : S ⟶ Sp B}
def IsThetaVec {N' : ℕ} (X : ThObj g (N' ^ 2) I ζ s) {R : Type} [CommRing R] (y : Sp R ⟶ S)
    (v : Lab g (N' ^ 2) → R) : Prop :=
  ∃ (θ : (X.P.L.pull (snd (Over.mk y) X.P.A).left).Sec)
    (ν : LB.Gen (mulLB X.P.A X.P.L (Over.mk y) N'))
    (r : LB.Gen (X.P.L.pull (1 : Over.mk y ⟶ X.P.A).left))
    (φ : ∀ a, LB.Gen (Out.thetaLB X.P.A X.P.L (N' ^ 2 : ℕ) (toUnit (Over.mk y) ≫ X.lev a))),
    (∀ p : Sp R, ∃ q : (Over.mk y ⊗ X.P.A).left, (fst (Over.mk y) X.P.A).left q = p ∧ q ∈ Out.nonzeroLocus θ) ∧
    ν.IsGen ∧ r.IsGen ∧ IsHeis X.P.A X.P.L (fun a => toUnit (Over.mk y) ≫ X.lev a) φ ∧
    ∀ (a : Lab g (N' ^ 2)) (V : (Over.mk y).left.Opens) (i₀ i₁ i₂ : X.P.L.ι)
      (h₀ : V ≤ (X.P.L.pull (1 : Over.mk y ⟶ X.P.A).left).U (fun _ => i₀))
      (h₁ : V ≤ secT X.P.A (1 : Over.mk y ⟶ X.P.A) ⁻¹ᵁ
        (Out.thetaLB X.P.A X.P.L (N' ^ 2 : ℕ) (toUnit (Over.mk y) ≫ X.lev a)).U ![i₀, i₁])
      (h₂ : V ≤ secT X.P.A (toUnit (Over.mk y) ≫ X.lev a) ⁻¹ᵁ (mulLB X.P.A X.P.L (Over.mk y) N').U ![i₁, i₂])
      (h₃ : V ≤ secT X.P.A ((toUnit (Over.mk y) ≫ X.lev a) ^ N') ⁻¹ᵁ
        (X.P.L.pull (snd (Over.mk y) X.P.A).left).U (fun _ => i₂)),
      ((secT X.P.A (1 : Over.mk y ⟶ X.P.A)).appLE _ V h₁).hom ((φ a).s ![i₀, i₁]).val *
        ((secT X.P.A (toUnit (Over.mk y) ≫ X.lev a)).appLE _ V h₂).hom (ν.s ![i₁, i₂]).val *
        ((secT X.P.A ((toUnit (Over.mk y) ≫ X.lev a) ^ N')).appLE _ V h₃).hom (θ.f (fun _ => i₂)) =
      constFn (R := R) (X := (Over.mk y).left) (𝟙 (Sp R)) V (v a) *
        resG (Over.mk y).left h₀ (r.s (fun _ => i₀)).val ^ (N' ^ 2)
end Theta
section Coset
variable {g : ℕ}
def SameCoset (n N' : ℕ) (a c : Lab g (N' ^ 2)) : Prop := n • N' • (a - c) = 0
def CosetUnit (n N' : ℕ) {R : Type} [CommRing R] (v : Lab g (N' ^ 2) → R) : Prop :=
  ∀ c, ∃ a, SameCoset n N' a c ∧ IsUnit (v a)
def CosetCond (n N' : ℕ) {R : Type} [CommRing R] (v : Lab g (N' ^ 2) → R) : Prop :=
  ∀ c, Ideal.span (v '' {a | SameCoset n N' a c}) = ⊤
def CritCond (n N' : ℕ) (V : Type) {K : Type} [CommRing V] [Field K] [Algebra V K] (w : Lab g (N' ^ 2) → K) : Prop :=
  ∃ (c : Kˣ) (v : Lab g (N' ^ 2) → V), (∀ a, algebraMap V K (v a) = c * w a) ∧ (∃ a, IsUnit (v a)) ∧ CosetUnit n N' v
end Coset
section Class
variable {g N' : ℕ} {I : Type} {B : Type} [CommRing B] {ζ : Bˣ} {e₀ : B →+* ℂ}
abbrev CClass (g N' : ℕ) (I : Type) {B : Type} [CommRing B] (ζ : Bˣ) (e₀ : B →+* ℂ) : Type 1 :=
  Set (ThObj g (N' ^ 2) I ζ (spMap e₀))
def thetaIdeal (C : CClass g N' I ζ e₀) : Ideal (MvPolynomial (Lab g (N' ^ 2)) B) :=
  ⨅ (Y : ThObj g (N' ^ 2) I ζ (spMap e₀)) (_ : Y ∈ C) (v : Lab g (N' ^ 2) → ℂ) (_ : IsThetaVec Y (𝟙 (Sp ℂ)) v),
    RingHom.ker (MvPolynomial.eval₂Hom e₀ v)
def InMM (n : ℕ) (C : CClass g N' I ζ e₀) {R : Type} [CommRing R] (β : B →+* R) (v : Lab g (N' ^ 2) → R) : Prop :=
  (∀ f ∈ thetaIdeal C, MvPolynomial.eval₂Hom β v f = 0) ∧ CosetCond n N' v
def ComesFrom (C : CClass g N' I ζ e₀) {k : Type} [Field k] {β : B →+* k} (X : ThObj g (N' ^ 2) I ζ (spMap β)) : Prop :=
  ∃ (k₀ : Type) (_ : Field k₀) (β₀ : B →+* k₀) (j : k₀ →+* k) (e : k₀ →+* ℂ) (X₀ : ThObj g (N' ^ 2) I ζ (spMap β₀))
    (Y : ThObj g (N' ^ 2) I ζ (spMap e₀)),
    j.comp β₀ = β ∧ e.comp β₀ = e₀ ∧ Y ∈ C ∧ IsPB X X₀ (spMap j) ∧ IsPB Y X₀ (spMap e)
def ThetaPointsInMM (n : ℕ) (C : CClass g N' I ζ e₀) : Prop :=
  ∀ (k : Type) [Field k] (β : B →+* k) (X : ThObj g (N' ^ 2) I ζ (spMap β)), ComesFrom C X →
    (∃ v, IsThetaVec X (𝟙 (Sp k)) v) ∧ ∀ v, IsThetaVec X (𝟙 (Sp k)) v → InMM n C β v
abbrev Lat (g : ℕ) : Type := Fin g ⊕ Fin g → ℤ
def IsTorusOf (Ef : LinearMap.BilinForm ℤ (Lat g)) (χ : Lat g → ℂ) (t : Lab g (N' ^ 2) → Lat g)
    (τ : I → (Lat g →ₗ[ℤ] Lat g)) (Pi0 : Lat g →+ (Fin g → ℂ)) (Y : ThObj g (N' ^ 2) I ζ (spMap e₀)) : Prop :=
  ∃ (u : HolUnif Y.P.A Y.P.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ' : u.Λ → ℂ),
    Function.Injective Pi0 ∧ (∀ z, z ∈ u.Λ ↔ ∃ l, z = Pi0 l) ∧ u.IsAH Hm χ' ∧
    (∀ (l : Lat g) (z : u.Λ), (z : Fin g → ℂ) = Pi0 l → χ' z = χ l) ∧
    (∀ l l', (hermForm Hm (Pi0 l) (Pi0 l')).im = (Ef l l' : ℝ)) ∧
    (∀ a, Y.lev a = u.ex (((N' ^ 2 : ℕ) : ℂ)⁻¹ • Pi0 (t a))) ∧
    ∀ i, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ z, u.ex (F z) = u.ex z ≫ Y.endo i) ∧ ∀ l, F (Pi0 l) = Pi0 (τ i l)
def IsHolFamily (D : CClass g N' I ζ e₀) : Prop :=
  ∃ (m : ℕ) (U : Set (Fin m → ℂ)) (Ef : LinearMap.BilinForm ℤ (Lat g)) (χ : Lat g → ℂ) (t : Lab g (N' ^ 2) → Lat g)
    (τ : I → (Lat g →ₗ[ℤ] Lat g)) (P : (Fin m → ℂ) → (Lat g →+ (Fin g → ℂ))),
    IsOpen U ∧ IsConnected U ∧ (∀ l, DifferentiableOn ℂ (fun b => P b l) U) ∧
    (∀ b ∈ U, ∃ Y : ThObj g (N' ^ 2) I ζ (spMap e₀), IsTorusOf Ef χ t τ (P b) Y) ∧
    ∀ Y, Y ∈ D ↔ ∃ b ∈ U, IsTorusOf Ef χ t τ (P b) Y
def IsGoodClass (C : CClass g N' I ζ e₀) : Prop :=
  Finite I ∧
  (∃ (r : ℕ) (D : Fin r → CClass g N' I ζ e₀), (∀ i, IsHolFamily (D i)) ∧ C = ⋃ i, D i) ∧
  (∀ i a, ∃ b, ∀ Y ∈ C, Y.Sat (.lab (.var i) a b)) ∧
  ∃ w, ∀ Y ∈ C, Y.Sat (.half w)
end Class
section Family
abbrev PJ (J B : Type) [CommRing B] : Scheme.{0} := Proj (MvPolynomial.homogeneousSubmodule J B)
def HasCoords {J B R : Type} [CommRing B] [CommRing R] (y : Sp R ⟶ PJ J B) (β : B →+* R) (v : J → R) : Prop :=
  ∃ h, y = Proj.fromOfGlobalSections (MvPolynomial.homogeneousSubmodule J B) (X := Sp R)
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp (MvPolynomial.eval₂Hom β v)) h
variable {g N' : ℕ} {I : Type} {B : Type} [CommRing B] {ζ : Bˣ} {e₀ : B →+* ℂ}
structure IsMMFamily (n : ℕ) (C : CClass g N' I ζ e₀) {X : Scheme.{0}} (s : X ⟶ Sp B)
    (ε : X ⟶ PJ (Lab g (N' ^ 2)) B) (𝒜 : ThObj g (N' ^ 2) I ζ s) : Prop where
  immersion : IsImmersion ε
  overBase : ε ≫ Proj.toSpecZero _ ≫
    spMap (algebraMap B ↥(MvPolynomial.homogeneousSubmodule (Lab g (N' ^ 2)) B 0)) = s
  reduced : IsReduced X

  points : ∀ (R : Type) [CommRing R] (β : B →+* R) (v : Lab g (N' ^ 2) → R) (y : Sp R ⟶ PJ (Lab g (N' ^ 2)) B),
    HasCoords y β v → ((∃ x : Sp R ⟶ X, x ≫ ε = y) ↔ InMM n C β v)

  axioms : ∀ r : EndRel g (N' ^ 2) I, (∀ Y ∈ C, Y.Sat r) → 𝒜.Sat r

  taut_ex : ∀ (R : Type) [CommRing R] [IsLocalRing R] (x : Sp R ⟶ X), ∃ v, IsThetaVec 𝒜 x v
  taut : ∀ (R : Type) [CommRing R] (β : B →+* R) (x : Sp R ⟶ X) (v : Lab g (N' ^ 2) → R),
    x ≫ s = spMap β → IsThetaVec 𝒜 x v → HasCoords (x ≫ ε) β v

  classify : ∀ (k : Type) [Field k] (β : B →+* k) (Y : ThObj g (N' ^ 2) I ζ (spMap β)), ComesFrom C Y →
    ∃ x : Sp k ⟶ X, IsPB Y 𝒜 x

  tan : ∀ (k : Type) [Field k] (x : Sp (DualNumber k) ⟶ X) (Y : ThObj g (N' ^ 2) I ζ (x ≫ s)),
    IsPB₀ Y 𝒜 x → IsPB₀ Y 𝒜 (constPt x) → x = constPt x
def MMFamilyExists (n : ℕ) (C : CClass g N' I ζ e₀) : Prop :=
  ∃ (X : Scheme.{0}) (s : X ⟶ Sp B) (ε : X ⟶ PJ (Lab g (N' ^ 2)) B) (𝒜 : ThObj g (N' ^ 2) I ζ s), IsMMFamily n C s ε 𝒜
end Family
example (g n N' : ℕ) : CosetUnit (g := g) n N' (fun _ => (1 : ℚ)) ∧ ¬ CosetUnit (g := g) n N' (fun _ => (0 : ℚ)) :=
  ⟨fun c => ⟨c, by simp [SameCoset], isUnit_one⟩, fun h => by obtain ⟨_, _, hu⟩ := h 0; exact not_isUnit_zero hu⟩
end GlobalTheory.IndefiniteRowSideFullHecke.ThetaCosetLabels


