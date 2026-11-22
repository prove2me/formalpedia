-- Prove2me | Definitions.Def_Formalism_CharacterColumnKernels_StatementN
-- name    : Formalism_CharacterColumnKernels_StatementN
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:21:44.554289+00:00
-- url     : https://prove2.me/theorems/c0e3151c-6972-4283-bb08-71f082ceaa9e
-- title:
--   Statement N
-- statement:
--   Definitions and structural lemmas for Statement N, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/StatementN.lean

import Definitions.Def_Formalism_CharacterColumnKernels_StatementG
import Definitions.Def_Formalism_CharacterColumnKernels_StatementX
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
namespace Formalism.NG
section Cong
variable {O : Type*} [CommRing O] {X : Type*}
def resOff (T : Subalgebra O (X → O)) (Z : Set X) : T →+* (↥Zᶜ → O) :=
  RingHom.pi fun x => (Pi.evalRingHom (fun _ : X => O) x.1).comp T.val.toRingHom
def ccIdeal (T : Subalgebra O (X → O)) (Z : Set X) : Ideal T := RingHom.ker (resOff T Z)
def vcc [IsDomain O] [IsDiscreteValuationRing O] (T : Subalgebra O (X → O)) (Z : Set X) (x : X) :
    ℕ∞ :=
  ⨅ c ∈ ccIdeal T Z, IsDiscreteValuationRing.addVal O ((c : X → O) x)
end Cong
def StatDescent : Prop :=
  ∀ (O : Type*) [CommRing O] (X X' : Type*) (T : Subalgebra O (X → O)) (T' : Subalgebra O (X' → O))
    (Z : Set X) (p : X' → X) (q : ℕ) (b : Fin q → (X' → O)),
    (∀ f' ∈ T', ∃ a : Fin q → (X → O), (∀ k, a k ∈ T) ∧ f' = ∑ k, (a k ∘ p) * b k) →
    (∀ x ∉ Z, ∀ a : Fin q → O, (∀ x', p x' = x → ∑ k, a k * b k x' = 0) → a = 0) →
    ∀ f' ∈ T', (∀ x', p x' ∉ Z → f' x' = 0) → ∀ π' : X',
      f' π' ∈ Ideal.span {y : O | ∃ c ∈ ccIdeal T Z, y = (c : X → O) (p π')}
def StatVccSpan : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (X : Type*)
    (T : Subalgebra O (X → O)) (Z : Set X) (x : X) (y : O),
    y ∈ Ideal.span {y : O | ∃ c ∈ ccIdeal T Z, y = (c : X → O) x} →
    vcc T Z x ≤ IsDiscreteValuationRing.addVal O y
section Eval
variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X' : Type*}
  (d : Type*) [Fintype d] [DecidableEq d]
def evalAt (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) (x' : X') :
    R' →+* Matrix d d (FractionRing O) :=
  (Pi.evalRingHom (fun _ : X' => Matrix d d (FractionRing O)) x').comp R'.val.toRingHom
def EvalSp (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) (_x' : X') : Type _ :=
  d → FractionRing O
variable (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) (x' : X')
instance : AddCommGroup (EvalSp O d R' x') := inferInstanceAs (AddCommGroup (d → FractionRing O))
instance : Module (FractionRing O) (EvalSp O d R' x') :=
  inferInstanceAs (Module (FractionRing O) (d → FractionRing O))
instance : Module R' (EvalSp O d R' x') :=
  Module.compHom (d → FractionRing O)
    ((matEnd (FractionRing O) (FractionRing O) d).comp (evalAt O d R' x'))
end Eval
def CharacterColumnGlobal : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (X X' : Type*)
    (T : Subalgebra O (X → O)) (T' : Subalgebra O (X' → O)) (Z : Set X) (p : X' → X) (q : ℕ)
    (b : Fin q → (X' → O)),
    (∀ f' ∈ T', ∃ a : Fin q → (X → O), (∀ k, a k ∈ T) ∧ f' = ∑ k, (a k ∘ p) * b k) →
    (∀ x ∉ Z, ∀ a : Fin q → O, (∀ x', p x' = x → ∑ k, a k * b k x' = 0) → a = 0) →
    ∀ (d : Type) [Fintype d] [DecidableEq d] (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
      (m g : Type) [Fintype m] [Fintype g] [DecidableEq g] (P : Matrix m g R'),
    (∀ Θ : Matrix g g R', ∃ f ∈ T', ∀ x', algebraMap O (FractionRing O) (f x') =
      (bigMat (fun r : R' => (r : X' → Matrix d d (FractionRing O)) x') Θ).det) →
    (∀ x', p x' ∉ Z → ∃ φ : Coker P →ₗ[R'] EvalSp O d R' x', φ ≠ 0) →
    ∀ (π' : X') (ρπ : R' →ₐ[O] Matrix d d O),
      (∀ r : R', (ρπ r).map (algebraMap O (FractionRing O)) = (r : X' → Matrix d d (FractionRing O)) π') →
    ∀ (α : Type) [LinearOrder α] [Fintype α] (bl : d → α), (∀ r, (ρπ r).BlockTriangular bl) →
    ∀ (ρk : ∀ k : α, R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O),
      (∀ k, Function.Surjective (ρk k)) → (∀ r k, (ρπ r).toSquareBlock bl k = ρk k r) →
      ((Fintype.card g * ∑ k : α, Fintype.card {a // bl a = k} : ℕ) : Cardinal) <
        Cardinal.mk (IsLocalRing.ResidueField O) →
      vcc T Z (p π') ≤
        ∑ k ∈ univ.image bl, Module.length O (LinearMap.ker (relMap O (KO O) (bigRect (ρk k) P)))
def StatBlockDet : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] (X' : Type*) (T' : Subalgebra O (X' → O))
    (d : Type) [Fintype d] [DecidableEq d] (R' : Subalgebra O (X' → Matrix d d (FractionRing O))),
    (∀ (m : ℕ) (r : Fin m → R') (s : Fin m →₀ ℕ), ∃ f ∈ T', ∀ x',
      algebraMap O (FractionRing O) (f x') =
        MvPolynomial.coeff s (Matrix.det (∑ i, (MvPolynomial.X i : MvPolynomial (Fin m) (FractionRing O)) •
          ((r i : X' → Matrix d d (FractionRing O)) x').map MvPolynomial.C))) →
    ∀ (g : Type) [Fintype g] [DecidableEq g] (Θ : Matrix g g R'), ∃ f ∈ T', ∀ x',
      algebraMap O (FractionRing O) (f x') =
        (bigMat (fun r : R' => (r : X' → Matrix d d (FractionRing O)) x') Θ).det
section Coc
variable {T' A : Type*} [CommRing T'] [Ring A] [Algebra T' A] {G : Type*} [Group G]
def ycoc (r : G →* A) (χ : G →* T'ˣ) (E : A) (g : G) : A :=
  ((((χ g)⁻¹ : T'ˣ) : T') • r g - 1) * E
def Ymod (r : G →* A) (χ : G →* T'ˣ) (E : A) : Submodule A A :=
  Submodule.span A (Set.range (ycoc r χ E))
end Coc
def StatCocycle : Prop :=
  ∀ (T' A : Type*) [CommRing T'] [Ring A] [Algebra T' A] (G : Type*) [Group G] (r : G →* A)
    (χ : G →* T'ˣ) (E : A) (g h : G),
    ycoc r χ E (g * h) = ycoc r χ E g + (((χ g)⁻¹ : T'ˣ) : T') • r g * ycoc r χ E h
def StatCocycleHom : Prop :=
  ∀ (T' A M : Type*) [CommRing T'] [Ring A] [Algebra T' A] [AddCommGroup M] [Module A M]
    [Module T' M] [IsScalarTower T' A M] (G : Type*) [Group G] (r : G →* A) (χ : G →* T'ˣ) (E : A),
    let y : G → Ymod r χ E := fun g => ⟨ycoc r χ E g, Submodule.subset_span ⟨g, rfl⟩⟩
    Function.Injective (fun (φ : Ymod r χ E →ₗ[A] M) (g : G) => φ (y g)) ∧
    ∀ (φ : Ymod r χ E →ₗ[A] M) (g h : G),
      φ (y (g * h)) = φ (y g) + (((χ g)⁻¹ : T'ˣ) : T') • (r g • φ (y h))
def StatCoboundaryKill : Prop :=
  ∀ (T' A W : Type*) [CommRing T'] [Ring A] [Algebra T' A] [AddCommGroup W] [Module A W]
    [Module T' W] [IsScalarTower T' A W] (G : Type*) [Group G] (r : G →* A) (χ : G →* T'ˣ)
    (E : A) (δ : T') (s : Finset G) (t : G → T'),
    E = ∑ g ∈ s, t g • r g → E * E = δ • E → (∀ w : W, E • w = 0) →
    (∀ w : W, (∑ g ∈ s, t g * ((χ g : T'ˣ) : T')) • w = δ • w) →
    ∀ (φ : Ymod r χ E →ₗ[A] W) (w : W),
      (∀ g, φ ⟨ycoc r χ E g, Submodule.subset_span ⟨g, rfl⟩⟩ =
        ((((χ g)⁻¹ : T'ˣ) : T') • r g - 1) • w) →
      (δ * δ) • w = 0
section Lat
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X : Type*}
  {V : Type*} [AddCommGroup V] [Module (FractionRing O) V]
def Vx (T : Subalgebra O (X → O)) (act : T →+* Module.End (FractionRing O) V) (x : X) :
    Submodule (FractionRing O) V :=
  ⨅ f : T, LinearMap.ker (act f - algebraMap O (FractionRing O) ((f : X → O) x) • LinearMap.id)
def VS (T : Subalgebra O (X → O)) (act : T →+* Module.End (FractionRing O) V) (S : Set X) :
    Submodule (FractionRing O) V :=
  ⨆ x ∈ S, Vx T act x
abbrev CongMod [Module O V] [IsScalarTower O (FractionRing O) V] (T : Subalgebra O (X → O))
    (act : T →+* Module.End (FractionRing O) V) (L : Submodule O V) (S : Set X) : Type _ :=
  L ⧸ (((VS T act S).restrictScalars O ⊓ L) ⊔ ((VS T act Sᶜ).restrictScalars O ⊓ L)).comap L.subtype
end Lat
def StatCongBound : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (X : Type*) [Finite X]
    (T : Subalgebra O (X → O)) [IsLocalRing T], (∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) →
    ∀ (V : Type*) [AddCommGroup V] [Module (FractionRing O) V] [FiniteDimensional (FractionRing O) V]
      [Module O V] [IsScalarTower O (FractionRing O) V]
      (act : T →+* Module.End (FractionRing O) V), (⨆ x, Vx T act x) = ⊤ →
    ∀ L : Submodule O V, L.FG → Submodule.span (FractionRing O) (L : Set V) = ⊤ →
      (∀ f : T, ∀ v ∈ L, act f v ∈ L) →
    ∀ Z : Finset X,
      Module.length O (CongMod T act L (Z : Set X)) ≤
        ∑ x ∈ Z, (Module.finrank (FractionRing O) (Vx T act x) : ℕ∞) * vcc T (Z : Set X) x
def StatCongBoundGood : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (X : Type*) [Finite X]
    (T : Subalgebra O (X → O)) [IsLocalRing T], (∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) →
    ∀ (V : Type*) [AddCommGroup V] [Module (FractionRing O) V] [FiniteDimensional (FractionRing O) V]
      [Module O V] [IsScalarTower O (FractionRing O) V]
      (act : T →+* Module.End (FractionRing O) V), (⨆ x, Vx T act x) = ⊤ →
    ∀ L : Submodule O V, L.FG → Submodule.span (FractionRing O) (L : Set V) = ⊤ →
      (∀ f : T, ∀ v ∈ L, act f v ∈ L) →
    ∀ (Z Zg : Finset X), Zg ⊆ Z → ∀ (a : Module.End (FractionRing O) V) (A : ℤ),
      (∀ v ∈ L, a v ∈ L) → (∀ f : T, a * act f = act f * a) →
      (∀ x ∈ Zg, ∀ v ∈ Vx T act x, a v = (A : FractionRing O) • v) →
      (∀ x ∈ Z, x ∉ Zg → ∀ v ∈ Vx T act x, a v = 0) →
      Module.length O (CongMod T act L (Zg : Set X)) ≤
        ∑ x ∈ Zg, (Module.finrank (FractionRing O) (Vx T act x) : ℕ∞) *
          (vcc T (Z : Set X) x + IsDiscreteValuationRing.addVal O (A : O))
def StatCongBoundLarge : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (X : Type*) [Finite X]
    (T : Subalgebra O (X → O)) [IsLocalRing T], (∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) →
    ∀ (V : Type*) [AddCommGroup V] [Module (FractionRing O) V] [FiniteDimensional (FractionRing O) V]
      [Module O V] [IsScalarTower O (FractionRing O) V]
      (act : T →+* Module.End (FractionRing O) V), (⨆ x, Vx T act x) = ⊤ →
    ∀ L : Submodule O V, L.FG → Submodule.span (FractionRing O) (L : Set V) = ⊤ →
      (∀ f : T, ∀ v ∈ L, act f v ∈ L) →
    ∀ Z : Finset X, (Z.card : Cardinal) ≤ Cardinal.mk (IsLocalRing.ResidueField O) →
      Module.length O (CongMod T act L (Z : Set X)) ≤
        ∑ x ∈ Z, (Module.finrank (FractionRing O) (Vx T act x) : ℕ∞) * vcc T (Z : Set X) x
def StatCongBoundGoodLarge : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (X : Type*) [Finite X]
    (T : Subalgebra O (X → O)) [IsLocalRing T], (∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) →
    ∀ (V : Type*) [AddCommGroup V] [Module (FractionRing O) V] [FiniteDimensional (FractionRing O) V]
      [Module O V] [IsScalarTower O (FractionRing O) V]
      (act : T →+* Module.End (FractionRing O) V), (⨆ x, Vx T act x) = ⊤ →
    ∀ L : Submodule O V, L.FG → Submodule.span (FractionRing O) (L : Set V) = ⊤ →
      (∀ f : T, ∀ v ∈ L, act f v ∈ L) →
    ∀ (Z Zg : Finset X), Zg ⊆ Z → (Z.card : Cardinal) ≤ Cardinal.mk (IsLocalRing.ResidueField O) → ∀ (a : Module.End (FractionRing O) V) (A : ℤ),
      (∀ v ∈ L, a v ∈ L) → (∀ f : T, a * act f = act f * a) →
      (∀ x ∈ Zg, ∀ v ∈ Vx T act x, a v = (A : FractionRing O) • v) →
      (∀ x ∈ Z, x ∉ Zg → ∀ v ∈ Vx T act x, a v = 0) →
      Module.length O (CongMod T act L (Zg : Set X)) ≤
        ∑ x ∈ Zg, (Module.finrank (FractionRing O) (Vx T act x) : ℕ∞) *
          (vcc T (Z : Set X) x + IsDiscreteValuationRing.addVal O (A : O))
end Formalism.NG


