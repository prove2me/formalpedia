-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_GoodClass
-- name    : Development_AbelianVarietyTheory_Definitions_ModuliSpaces_GoodClass
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:50:46.564635+00:00
-- url     : https://prove2.me/theorems/d1e0d8a8-5cd6-44ad-8368-baf86cd8fa12
-- title:
--   Good Class
-- statement:
--   Definitions and structural lemmas for Good Class, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ModuliSpaces/GoodClass.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
namespace GlobalTheory.ZM
abbrev Ix (g k : ℕ) : Type := Fin (2 * g) → ZMod k
structure TBase (o : Type) [CommRing o] (k : ℕ) where
  ζ : oˣ
  unit : IsUnit (k : o)
  prim : ∀ (K : Type) [Field K] (β : o →+* K), IsPrimitiveRoot (β ζ) k
variable {o : Type} [CommRing o] {S S' : Scheme.{0}}
def unitS (s : S ⟶ Sp o) (u : oˣ) : Γ(S, ⊤)ˣ := Units.map s.appTop.hom.toMonoidHom (unitOn u)
structure TObj (g k : ℕ) (J : Type) (b : TBase o k) (s : S ⟶ Sp o) where
  A : Over S
  [grp : GrpObj A]
  ab : IsAbelianScheme A
  dim : SmoothOfRelativeDimension g A.hom
  L : LB A.left
  isLB : L.IsLB
  rigid : Out.Rigidified A L
  sym : Out.Sym A L
  ample : Out.RelAmple A L
  ktriv : Out.KTriv A L
  pt : Fin (2 * g) → (Out.baseOver S ⟶ A)
  torsion : ∀ i, pt i ^ k = 1
  bij : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (y : Over.mk x ⟶ A), y ^ k = 1 →
    ∃! c : Ix g k, Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ pt i) (fun i => (c i).val) = y
  pairing : ∀ i j, Out.WeilIs A L k (pt i) (pt j) (unitS s b.ζ ^ Out.stdSymp g i j)
  act : J → (A ⟶ A)
  hom : ∀ j, IsMonHom (act j)
attribute [instance] TObj.grp
variable {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o} {s' : S' ⟶ Sp o}
def TObj.pol (t : TObj g k J b s) : Out.PolAV S :=
  { A := t.A, isAb := t.ab, g := g, smoothDim := t.dim, L := t.L, isLB := t.isLB, rigid := t.rigid, sym := t.sym, ample := t.ample, ktriv := t.ktriv }
def TObj.lab (t : TObj g k J b s) (a : Ix g k) : Out.baseOver S ⟶ t.A := Out.linComb t.pt (fun i => (a i).val)
def TMap (t' : TObj g k J b s') (t : TObj g k J b s) (f : S' ⟶ S) : Prop :=
  ∃ φ : t'.A.left ⟶ t.A.left, IsGrpPullback t'.A t.A f φ ∧ LBIso t'.L (t.L.pull φ) ∧
    (∀ i, (t'.pt i).left ≫ φ = f ≫ (t.pt i).left) ∧ ∀ j, (t'.act j).left ≫ φ = φ ≫ (t.act j).left
def TObj.HasTh {N' : ℕ} {b : TBase o (N' ^ 2)} (t : TObj g (N' ^ 2) J b s) {R : Type} [CommRing R] (x : Sp R ⟶ S)
    (v : Ix g (N' ^ 2) → R) : Prop :=
  Out.IsThetaPt t.pol N' (T := Over.mk x) (fun a => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ t.lab a)
    (fun a => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (v a))
def Coset (n N' : ℕ) {R : Type} [CommRing R] (v : Ix g (N' ^ 2) → R) (q : Ideal R) : Prop :=
  ∀ a, ∃ c, v (a + (N' / n) • c) ∉ q
def thIdeal {N' : ℕ} {b : TBase o (N' ^ 2)} (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) :
    Ideal (MvPolynomial (Ix g (N' ^ 2)) o) :=
  ⨅ (t : TObj g (N' ^ 2) J b (spMap em)) (v : Ix g (N' ^ 2) → ℂ) (_ : C t ∧ t.HasTh (𝟙 _) v), RingHom.ker (MvPolynomial.eval₂Hom em v)
def InMM (n N' : ℕ) (I : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)) {R : Type} [CommRing R] (β : o →+* R) (v : Ix g (N' ^ 2) → R) : Prop :=
  (∀ F ∈ I, MvPolynomial.eval₂ β v F = 0) ∧ ∀ q : Ideal R, q.IsPrime → Coset n N' v q
def FromC (em : o →+* ℂ) (C : TObj g k J b (spMap em) → Prop) (t : TObj g k J b s) {K : Type} [Field K] (x : Sp K ⟶ S) : Prop :=
  ∃ (K₀ : Type) (_ : Field K₀) (β : o →+* K₀) (i : K₀ →+* K) (j : K₀ →+* ℂ) (t₀ : TObj g k J b (spMap β))
    (tx : TObj g k J b (x ≫ s)) (tc : TObj g k J b (spMap em)),
    j.comp β = em ∧ x ≫ s = spMap i ≫ spMap β ∧ TMap tx t x ∧ TMap tx t₀ (spMap i) ∧ TMap tc t₀ (spMap j) ∧ C tc
def fromSet (em : o →+* ℂ) (C : TObj g k J b (spMap em) → Prop) (t : TObj g k J b s) : Set S :=
  {p | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ S), p ∈ Set.range x ∧ FromC em C t x}
def TObj.Prim (t : TObj g k J b s) (w w' : J) : Prop :=
  letI := t.ab.comm
  t.act w * t.act w' = 𝟙 t.A ∧
  LBIso (cubeLB t.A ![fst t.A t.A ≫ t.act w, snd t.A t.A] t.L) (cubeLB t.A ![fst t.A t.A, snd t.A t.A ≫ t.act w'] t.L) ∧
  LBIso t.L (cubeLB t.A ![𝟙 t.A, t.act w] t.L)
def TObj.Shape (t : TObj g k J b s) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) : Prop :=
  ∀ j, (∀ i, t.pt i ≫ t.act j = t.lab (fun i' => (Mat j i' i : ZMod k))) ∧
    Out.RelAmple t.A (LB.LinComb t.L (K := Fin 2) ![𝟙 t.A.left, (t.act j).left] ![(κ : ℤ), -1])
structure GoodClass {N' : ℕ} {b : TBase o (N' ^ 2)} (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop)
    (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (w w' : J) (d : ℕ) : Prop where
  iso : ∀ t t', C t → TMap t' t (𝟙 _) → C t'
  shape : ∀ t, C t → t.Shape Mat κ ∧ t.Prim w w'
  fam : ∃ (r : ℕ) (B : Fin r → Set (Fin d → ℂ)) (θ : Fin r → (Fin d → ℂ) → Ix g (N' ^ 2) → ℂ),
    (∀ i, IsOpen (B i) ∧ IsPreconnected (B i) ∧ (∀ a, DifferentiableOn ℂ (fun z => θ i z a) (B i)) ∧
      ∀ z ∈ B i, (∃ t, C t ∧ t.HasTh (𝟙 _) (θ i z)) ∧ {z' ∈ B i | ∃ c : ℂ, θ i z' = c • θ i z}.Countable) ∧
    ∀ t, C t → ∃ i, ∃ z ∈ B i, t.HasTh (𝟙 _) (θ i z)
structure ThetaFam (n : ℕ) {N' : ℕ} {b : TBase o (N' ^ 2)} (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) where
  MM : Scheme.{0}
  s : MM ⟶ Sp o
  qproj : IsQProjOver s
  flat : Flat s
  reduced : IsReduced MM
  univ : TObj g (N' ^ 2) J b s
  dense : Dense (fromSet em C univ)
  loc : ∀ (R : Type) [CommRing R] [IsLocalRing R] (β : o →+* R) (x : Sp R ⟶ MM), x ≫ s = spMap β →
    ∃ v, univ.HasTh x v ∧ InMM n N' (thIdeal em C) β v
  pts : ∀ (R : Type) [CommRing R] (β : o →+* R) (v : Ix g (N' ^ 2) → R), InMM n N' (thIdeal em C) β v →
    ∃! x : Sp R ⟶ MM, x ≫ s = spMap β ∧ univ.HasTh x v
  rep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s'), IsReduced S → Dense (fromSet em C t) →
    ∃! f : S ⟶ MM, f ≫ s = s' ∧ TMap t univ f
  unram : ∀ (K : Type) [Field K] (x : Sp (DualNumber K) ⟶ MM) (t : TObj g (N' ^ 2) J b (x ≫ s)),
    x ≫ s = constPt x ≫ s → TMap t univ x → TMap t univ (constPt x) → x = constPt x
def TBase.complex (k : ℕ) (hk : k ≠ 0) : TBase ℂ k where
  ζ := Units.mk0 (Complex.exp (2 * Real.pi * Complex.I / k)) (Complex.exp_ne_zero _)
  unit := (Nat.cast_ne_zero.2 hk : (k : ℂ) ≠ 0).isUnit
  prim := fun _ _ β => (Complex.isPrimitiveRoot_exp k hk).map_of_injective β.injective
def TObj.zero (k : ℕ) (J : Type) (b : TBase o k) (s : S ⟶ Sp o) : TObj 0 k J b s where
  A := (Out.Inh.zeroPolAV S).A
  grp := (Out.Inh.zeroPolAV S).grp
  ab := (Out.Inh.zeroPolAV S).isAb
  dim := (Out.Inh.zeroPolAV S).smoothDim
  L := (Out.Inh.zeroPolAV S).L
  isLB := (Out.Inh.zeroPolAV S).isLB
  rigid := (Out.Inh.zeroPolAV S).rigid
  sym := (Out.Inh.zeroPolAV S).sym
  ample := (Out.Inh.zeroPolAV S).ample
  ktriv := (Out.Inh.zeroPolAV S).ktriv
  pt := fun i => Fin.elim0 i
  torsion := fun i => Fin.elim0 i
  bij := fun _ _ _ _ _ _ => ⟨fun i => Fin.elim0 i, toUnit_unique _ _, fun _ _ => funext fun i => Fin.elim0 i⟩
  pairing := fun i => Fin.elim0 i
  act := fun _ => 𝟙 _
  hom := fun _ => inferInstance
example (k : ℕ) (J : Type) (b : TBase o k) (s : S ⟶ Sp o) : (TObj.zero k J b s).pol = Out.Inh.zeroPolAV S := rfl
example (t : TObj g k J b s) (w w' : J) (h : t.Prim w w') : lift (t.act w) (t.act w') ≫ μ[t.A] = 𝟙 t.A := h.1
example (n N' : ℕ) {R : Type} [CommRing R] (q : Ideal R) (hq : q ≠ ⊤) : Coset (g := g) n N' (fun _ => (1 : R)) q :=
  fun _ => ⟨0, fun h => hq ((Ideal.eq_top_iff_one q).2 h)⟩
example (n N' : ℕ) {R : Type} [CommRing R] (q : Ideal R) : ¬ Coset (g := g) n N' (fun _ => (0 : R)) q :=
  fun h => (h 0).elim fun _ hc => hc q.zero_mem
end GlobalTheory.ZM
end


