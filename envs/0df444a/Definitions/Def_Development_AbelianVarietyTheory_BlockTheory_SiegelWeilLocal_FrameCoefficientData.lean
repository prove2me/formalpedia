-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelWeilLocal_FrameCoefficientData
-- name    : Development_AbelianVarietyTheory_BlockTheory_SiegelWeilLocal_FrameCoefficientData
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:09:36.404745+00:00
-- url     : https://prove2.me/theorems/cb1c4857-a824-40be-a64b-9332a6512de1
-- title:
--   Frame Coefficient Data
-- statement:
--   Definitions and structural lemmas for Frame Coefficient Data, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/SiegelWeilLocal/FrameCoefficientData.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.FrameCoefficientData
section Groups
variable {E V : Type} [CommRing E] [AddCommGroup V] [Module E V]
def Carries (g : V ≃ₗ[E] V) (A B : Set V) : Prop := ∀ v, g v ∈ B ↔ v ∈ A
def trivOn (E : Type) [CommRing E] [Module E V] (A : Set V) (B : AddSubgroup V) :
    Subgroup (V ≃ₗ[E] V) where
  carrier := {g | (∀ v, g v ∈ B ↔ v ∈ B) ∧ ∀ v ∈ A, g v - v ∈ B}
  one_mem' := ⟨fun _ => Iff.rfl, fun v _ => by simp⟩
  mul_mem' := by
    rintro g g' ⟨h1, h2⟩ ⟨h3, h4⟩
    refine ⟨fun v => (h1 (g' v)).trans (h3 v), fun v hv => ?_⟩
    have : (g * g') v - v = g (g' v - v) + (g v - v) := by
      simp [LinearEquiv.mul_apply]
    rw [this]
    exact B.add_mem ((h1 _).2 (h4 v hv)) (h2 v hv)
  inv_mem' := by
    rintro g ⟨h1, h2⟩
    have k : ∀ v, g (g⁻¹ v) = v := fun v => g.apply_symm_apply v
    refine ⟨fun v => by rw [← h1 (g⁻¹ v), k], fun v hv => ?_⟩
    rw [← h1, map_sub, k, ← neg_sub]
    exact B.neg_mem (h2 v hv)
def stab (E : Type) [CommRing E] [Module E V] (B : AddSubgroup V) : Subgroup (V ≃ₗ[E] V) :=
  trivOn E ∅ B
def stabRel (E : Type) [CommRing E] [Module E V] (R : Set (V × V)) : Subgroup (V ≃ₗ[E] V) where
  carrier := {g | ∀ v w, (g v, g w) ∈ R ↔ (v, w) ∈ R}
  one_mem' := fun _ _ => Iff.rfl
  mul_mem' := fun {g g'} h1 h2 v w => (h1 (g' v) (g' w)).trans (h2 v w)
  inv_mem' := by
    intro g h1 v w
    have k : ∀ v, g (g⁻¹ v) = v := fun v => g.apply_symm_apply v
    rw [← h1 (g⁻¹ v), k, k]
def isom [StarRing E] (h : V →ₗ[E] V →ₛₗ[starRingEnd E] E) : Subgroup (V ≃ₗ[E] V) where
  carrier := {g | ∀ v w, h (g v) (g w) = h v w}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {g g'} h1 h2 v w => (h1 (g' v) (g' w)).trans (h2 v w)
  inv_mem' := by
    intro g h1 v w
    have k : ∀ v, g (g⁻¹ v) = v := fun v => g.apply_symm_apply v
    rw [← h1 (g⁻¹ v), k, k]
end Groups
def invVol {G : Type} [Group G] (K₀ K : Subgroup G) : ℝ≥0∞ :=
  (K.relIndex K₀ : ℝ≥0∞) / (K₀.relIndex K : ℝ≥0∞)
section Local
variable (o F E : Type) [CommRing o] [IsDomain o] [IsDiscreteValuationRing o]
  [Field F] [Algebra o F] [IsFractionRing o F]
  [CommRing E] [StarRing E] [Algebra F E] [Algebra o E]
def ord_vw (x : F) : ℤ :=
  - WithZero.log ((IsDiscreteValuationRing.maximalIdeal o).valuation F x)
def resNorm : ℕ := Nat.card (IsLocalRing.ResidueField o)
abbrev MaxOrd : Subalgebra o E := integralClosure o E
def IsUnramifiedQuadratic : Prop :=
  Module.finrank F E = 2 ∧ (∀ x : F, star (algebraMap F E x) = algebraMap F E x) ∧
    ∃ w ∈ MaxOrd o E, ∃ u ∈ MaxOrd o E, (w - star w) * u = 1
def IsStdChar (ψ : AddChar E Circle) : Prop :=
  (∀ y ∈ MaxOrd o E, ψ y = 1) ∧ (∀ y, (∀ c ∈ MaxOrd o E, ψ (c * y) = 1) → y ∈ MaxOrd o E) ∧
    ∀ y, ψ (star y) = ψ y
end Local
structure Frame (F V : Type) (r : ℕ) where
  f : Fin (r + 1) → V
  y : Fin r → V
  T : F
structure Data (o F E V : Type) [CommRing o] [Field F] [CommRing E] [StarRing E] [Algebra o E]
    [AddCommGroup V] [Module E V] (r : ℕ) where
  h : V →ₗ[E] V →ₛₗ[starRingEnd E] E
  ψ : AddChar E Circle
  θ : F
  A : Frame F V r
  B : Frame F V r
  blocks : Composition (r + 1)
  t : Fin blocks.length → Eˣ
  ref : Submodule (MaxOrd o E) V
section Main
variable {o F E V : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o]
  [Field F] [Algebra o F] [IsFractionRing o F]
  [CommRing E] [StarRing E] [Algebra F E] [Algebra o E]
  [AddCommGroup V] [Module E V] {r : ℕ}
def perp (h : V →ₗ[E] V →ₛₗ[starRingEnd E] E) (S : Set V) : Set V := {v | ∀ w ∈ S, h v w = 0}
namespace Frame
variable (E) (A : Frame F V r)
def z : V := A.f (Fin.last r)
def X (j : ℕ) : Submodule E V := Submodule.span E (A.f '' {i | (i : ℕ) < j})
variable {E}
def IsFrame (h : V →ₗ[E] V →ₛₗ[starRingEnd E] E) : Prop :=
  (∀ (i : Fin r) (b : Fin (r + 1)), h (A.f b) (A.f i.castSucc) = 0) ∧
    h A.z A.z = algebraMap F E (-A.T) ∧ A.T ≠ 0 ∧
    (∀ i j : Fin r, h (A.y j) (A.f i.castSucc) = if i = j then 1 else 0) ∧
    (∀ i j : Fin r, h (A.y i) (A.y j) = 0) ∧ ∀ j : Fin r, h (A.y j) A.z = 0
def N (h : V →ₗ[E] V →ₛₗ[starRingEnd E] E) : Subgroup (V ≃ₗ[E] V) :=
  isom h ⊓ (⨅ j : Fin r, trivOn E (A.X E (j + 1) : Set V) (A.X E j).toAddSubgroup) ⊓
    trivOn E (perp h (A.X E r)) (A.X E r).toAddSubgroup
def coeffSum (h : V →ₗ[E] V →ₛₗ[starRingEnd E] E) (g : V ≃ₗ[E] V) : E :=
  ∑ j : Fin r, h (g (A.f j.succ)) (A.y j)
def IsInnerLattice (h : V →ₗ[E] V →ₛₗ[starRingEnd E] E) (L : Submodule (MaxOrd o E) V) : Prop :=
  (∃ s : Finset V, L = (A.X E r).restrictScalars (MaxOrd o E) ⊔
      Submodule.span (MaxOrd o E) (s : Set V)) ∧
    (∀ v, v ∈ L ↔ v ∈ perp h (A.X E r) ∧ ∀ w ∈ L, h v w ∈ MaxOrd o E) ∧
    A.z ∈ L ∧ ∀ c : E, c • A.z ∈ L → c ∈ MaxOrd o E
def stdLattice (h : V →ₗ[E] V →ₛₗ[starRingEnd E] E) (L : Submodule (MaxOrd o E) V) :
    Submodule (MaxOrd o E) V :=
  Submodule.span (MaxOrd o E) (Set.range (fun i : Fin r => A.f i.castSucc) ∪
    ((L : Set V) ∩ perp h (Set.range A.y)) ∪ Set.range A.y)
end Frame
namespace Data
variable {k : ℕ} (D : Data o F E V r)
def θinv : E := algebraMap F E D.θ⁻¹
def Zhat : Matrix (Fin (r + 1)) (Fin (r + 1)) E := fun a b => D.h (D.A.f a) (D.B.f b)
def minor (l : ℕ) (hl : l ≤ r + 1) : E :=
  (D.Zhat.submatrix (Fin.castLE hl) (Fin.castLE hl)).det
def G : F :=
  Algebra.norm F (D.minor (r + 1) le_rfl) -
    D.A.T * D.B.T * Algebra.norm F (D.minor r (Nat.le_succ r))
def Relevant : Prop :=
  ∀ a b : Fin (r + 1), D.Zhat a b =
    if (a : ℕ) + b + 1 = D.blocks.sizeUpTo (D.blocks.index a) +
        D.blocks.sizeUpTo (D.blocks.index a + 1)
    then (D.t (D.blocks.index a) : E) * (-1) ^ (r - (b : ℕ)) else 0
def psi (g : V ≃ₗ[E] V) : Circle := D.ψ (D.θinv * D.A.coeffSum D.h g)
def psi' (g : V ≃ₗ[E] V) : Circle := D.ψ (D.θinv * D.B.coeffSum D.h g)
def St : Subgroup (V ≃ₗ[E] V) := D.A.N D.h ⊓ D.B.N D.h
def StInt : Subgroup (V ≃ₗ[E] V) :=
  D.St ⊓ stab E (Submodule.span (MaxOrd o E) (Set.range D.A.f)).toAddSubgroup ⊓
    stab E (Submodule.span (MaxOrd o E) (Set.range D.B.f)).toAddSubgroup
def ME : Submodule E V := Submodule.span E (Set.range D.A.f ∪ Set.range D.B.f)
def W0 : Set V := perp D.h D.ME
def H0 : Subgroup (V ≃ₗ[E] V) := isom D.h ⊓ trivOn E (D.ME : Set V) ⊥
def minorOrd : ℤ :=
  ∑ i : Fin D.blocks.length,
    ord_vw o F (Algebra.norm F (D.minor (D.blocks.sizeUpTo (i + 1)) (D.blocks.sizeUpTo_le _)))
def aExp : ℤ := ord_vw o F D.G - 2 * (r + 1) * ord_vw o F D.θ
def Ht : ℝ≥0∞ := (resNorm o : ℝ≥0∞) ^ (ord_vw o F D.θ + D.aExp + D.minorOrd)
def Hyp (k : ℕ) : Prop :=
  IsUnramifiedQuadratic o F E ∧ IsStdChar o E D.ψ ∧
    Module.finrank E V = k + 2 * r + 1 ∧
    (∀ v w, D.h w v = star (D.h v w)) ∧ (∀ v, (∀ w, D.h v w = 0) → v = 0) ∧
    (D.θ = 1 ∨ (D.θ ≠ 0 ∧ ord_vw o F D.θ = 1 ∧ ¬ IsField E ∧
      ord_vw o F D.A.T = 0 ∧ ord_vw o F D.B.T = 0)) ∧
    D.A.IsFrame D.h ∧ D.B.IsFrame D.h ∧ D.Relevant ∧
    4 * r + 7 ≤ k ∧ D.G ≠ 0 ∧ (∀ g ∈ D.St, D.psi g = D.psi' g) ∧
    D.ref.FG ∧ Submodule.span E (D.ref : Set V) = ⊤
structure InnerDatum where
  L : Submodule (MaxOrd o E) V
  L' : Submodule (MaxOrd o E) V
  Γ : Submodule (MaxOrd o E) (V × V)
  hL : D.A.IsInnerLattice D.h L
  hL' : D.B.IsInnerLattice D.h L'
  mem : ∀ p ∈ Γ, p.1 ∈ L' ∧ p.2 ∈ L
  total : ∀ w' ∈ L', ∃ w, (w', w) ∈ Γ
  onto : ∀ w ∈ L, ∃ w', (w', w) ∈ Γ
  ker_left : ∀ w', (w', (0 : V)) ∈ Γ ↔ D.θinv • w' ∈ L'
  ker_right : ∀ w, ((0 : V), w) ∈ Γ ↔ D.θinv • w ∈ L
  base : (D.B.z, D.A.z) ∈ Γ
  isometric : ∀ p ∈ Γ, ∀ p' ∈ Γ, D.θinv * (D.h p.1 p'.1 - D.h p.2 p'.2) ∈ MaxOrd o E
variable {D}
def InnerDatum.Rel (d d' : D.InnerDatum) : Prop :=
  ∃ g ∈ D.H0, Carries g d.L d'.L ∧ Carries g d.L' d'.L' ∧
    ∀ v w, (g v, g w) ∈ d'.Γ ↔ (v, w) ∈ d.Γ
def InnerDatum.stabiliser (d : D.InnerDatum) : Subgroup (V ≃ₗ[E] V) :=
  D.H0 ⊓ stab E d.L.toAddSubgroup ⊓ stab E d.L'.toAddSubgroup ⊓ stabRel E (d.Γ : Set (V × V))
def InnerDatum.weight (d : D.InnerDatum) : ℝ≥0∞ :=
  invVol (D.H0 ⊓ stab E D.ref.toAddSubgroup) d.stabiliser
def dataSum (φ : D.InnerDatum → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' c : Quot (InnerDatum.Rel (D := D)), c.out.weight * φ c.out
def Serves (d : D.InnerDatum) (Λ : Submodule (MaxOrd o E) V) (n n' : V ≃ₗ[E] V) : Prop :=
  n ∈ D.A.N D.h ∧ n' ∈ D.B.N D.h ∧
    Carries n (D.A.stdLattice D.h d.L) Λ ∧ Carries n' (D.B.stdLattice D.h d.L') Λ ∧
    (∀ b, D.θinv • (n' (D.B.f b) - n (D.A.f b)) ∈ Λ) ∧
    ∀ w' w, (w', w) ∈ d.Γ ↔
      w' ∈ perp D.h (D.B.X E r) ∧ w ∈ perp D.h (D.A.X E r) ∧
        ∃ x ∈ D.A.X E r, ∃ x' ∈ D.B.X E r, w + x ∈ Λ ∧ w' + x' ∈ Λ ∧
          D.θinv • ((w' + x') - (w + x)) ∈ Λ
def Term (d : D.InnerDatum) : Type :=
  {Λ : Submodule (MaxOrd o E) V // ∃ p : (V ≃ₗ[E] V) × (V ≃ₗ[E] V), Serves d Λ p.1 p.2}
namespace Term
variable {d : D.InnerDatum} (Λ : Term d)
def pair : (V ≃ₗ[E] V) × (V ≃ₗ[E] V) := Classical.choose Λ.2
def om : Circle := D.psi Λ.pair.1 * (D.psi' Λ.pair.2)⁻¹
def mu : ℝ≥0∞ := invVol D.StInt (D.St ⊓ stab E Λ.1.toAddSubgroup)
def M : Submodule (MaxOrd o E) V :=
  Submodule.span (MaxOrd o E) (Set.range (fun b => Λ.pair.1 (D.A.f b)) ∪
    Set.range (fun b => D.θinv • (Λ.pair.2 (D.B.f b) - Λ.pair.1 (D.A.f b))))
def satM : Submodule (MaxOrd o E) V := Λ.1 ⊓ D.ME.restrictScalars (MaxOrd o E)
def defect : ℕ := Λ.M.toAddSubgroup.relIndex Λ.satM.toAddSubgroup
def tauImage : Submodule (MaxOrd o E) V :=
  Λ.M ⊔ Submodule.span (MaxOrd o E)
    {v | ∃ w ∈ D.W0, w ∈ d.L ∧ w ∈ d.L' ∧ (w, w) ∈ d.Γ ∧
      ∃ x ∈ D.A.X E r, ∃ x' ∈ D.B.X E r, w + x ∈ Λ.1 ∧ w + x' ∈ Λ.1 ∧
        D.θinv • (x' - x) ∈ Λ.1 ∧ v = D.θinv • (x' - x)}
def tauCard : ℕ := Λ.M.toAddSubgroup.relIndex Λ.tauImage.toAddSubgroup
def Rel (Λ Λ' : Term d) : Prop := ∃ g ∈ D.St, Carries g Λ.1 Λ'.1
def HasFrames (u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Prop :=
  ∃ n n', Serves d Λ.1 n n' ∧ (∀ b, n (D.A.f b) = ∑ a, u a b • D.A.f a) ∧
    ∀ b, n' (D.B.f b) = ∑ a, u' a b • D.B.f a
end Term
open Classical in

def mass (d : D.InnerDatum) (S : Term d → Prop) : ℝ≥0∞ :=
  ∑' c : Quot (Term.Rel (d := d)), if S c.out then c.out.mu else 0
open Classical in

def amp (d : D.InnerDatum) (S : Term d → Prop) : ℂ :=
  ∑' c : Quot (Term.Rel (d := d)),
    if S c.out then (c.out.mu.toReal : ℂ) * (c.out.om : ℂ) else 0
def count (d : D.InnerDatum) (u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (S : Term d → Prop) : ℝ≥0∞ :=
  ((Set.encard {Λ : Term d | S Λ ∧ Λ.HasFrames u u'} : ℕ∞) : ℝ≥0∞)
variable (D)
def totalMass : ℝ≥0∞ := dataSum fun d : D.InnerDatum => mass d fun _ => True
def ampSq (S : ∀ d : D.InnerDatum, Term d → Prop) : ℝ≥0∞ :=
  dataSum fun d : D.InnerDatum => ENNReal.ofReal (‖amp d (S d)‖ ^ 2)
def Finiteness : Prop :=
  (∀ d : D.InnerDatum, Subgroup.Commensurable (D.H0 ⊓ stab E D.ref.toAddSubgroup) d.stabiliser) ∧
    (∀ (d : D.InnerDatum) (Λ : Term d),
      Subgroup.Commensurable D.StInt (D.St ⊓ stab E Λ.1.toAddSubgroup) ∧
        Λ.defect ≠ 0 ∧ Λ.tauCard ≠ 0) ∧
    D.totalMass ≠ ⊤
def AmplitudeBounds (k : ℕ) : Prop :=
  D.ampSq (fun _ Λ => Λ.satM ≠ Λ.M) ≤
      D.Ht ^ (39 * (r + 1) ^ 2) * (resNorm o : ℝ≥0∞) ^ (-((k : ℤ) - 2 * r - 5)) * D.totalMass ∧
    (D.ampSq (fun _ Λ => Λ.satM = Λ.M) ≤ D.Ht ^ (39 * (r + 1) ^ 2) * D.totalMass ∧
      D.ampSq (fun _ _ => True) ≤ D.Ht ^ (39 * (r + 1) ^ 2) * D.totalMass) ∧
    (ord_vw o F D.θ = 0 → ord_vw o F D.G = 0 →
      (∀ i : Fin D.blocks.length, ord_vw o F (Algebra.norm F
        (D.minor (D.blocks.sizeUpTo (i + 1)) (D.blocks.sizeUpTo_le _))) = 0) →
      (∀ (d : D.InnerDatum) (Λ : Term d), Λ.satM = Λ.M) ∧ D.Ht = 1 ∧
        D.ampSq (fun _ _ => True) = D.totalMass)
def IsUnitriangular (u : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Prop :=
  (∀ a, u a a = 1) ∧ ∀ a b, b < a → u a b = 0
def ShareBound (k : ℕ) : Prop :=
  ∀ β : ℕ, 1 ≤ β →
    (∀ u u', IsUnitriangular u → IsUnitriangular u' →
      dataSum (fun d : D.InnerDatum => count d u u' fun Λ => Λ.defect = β) ≤
        4 * (resNorm o : ℝ≥0∞) ^ (2 * D.aExp * (2 * r + 2)) * ((β : ℝ≥0∞) ^ (k - 1))⁻¹ *
          dataSum (fun d : D.InnerDatum => count d u u' fun Λ => Λ.satM = Λ.M)) ∧
    dataSum (fun d : D.InnerDatum => mass d fun Λ => Λ.defect = β) ≤
      4 * (resNorm o : ℝ≥0∞) ^ (2 * D.aExp * (2 * r + 2)) * ((β : ℝ≥0∞) ^ (k - 1))⁻¹ *
        dataSum (fun d : D.InnerDatum => mass d fun Λ => Λ.satM = Λ.M) ∧
    dataSum (fun d : D.InnerDatum => mass d fun Λ => Λ.defect = β) ≤
      4 * D.Ht ^ (4 * (r + 1)) * ((β : ℝ≥0∞) ^ (k - 1))⁻¹ * D.totalMass
def FibreBound (k : ℕ) : Prop :=
  ∀ (d : D.InnerDatum) (j : ℕ), 1 ≤ j →
    (∀ u u', IsUnitriangular u → IsUnitriangular u' →
      count d u u' (fun Λ => Λ.tauCard = j) ≤
          (resNorm o : ℝ≥0∞) ^ (6 * D.aExp * (2 * r + 2)) * (j : ℝ≥0∞) ^ (k - 1) ∧
        count d u u' (fun Λ => Λ.tauCard = j) ≤
          D.Ht ^ (12 * (r + 1)) * (j : ℝ≥0∞) ^ (k - 1)) ∧
    mass d (fun Λ => Λ.tauCard = j) ≤
      D.Ht ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (j : ℝ≥0∞) ^ (k - 1)
end Data
end Main
def NonGenericLocal : Prop :=
  ∀ (o F E V : Type) [CommRing o] [IsDomain o] [IsDiscreteValuationRing o]
    [IsAdicComplete (IsLocalRing.maximalIdeal o) o] [Finite (IsLocalRing.ResidueField o)]
    [Field F] [CharZero F] [Algebra o F] [IsFractionRing o F]
    [CommRing E] [StarRing E] [Algebra F E] [Algebra o E] [IsScalarTower o F E]
    [AddCommGroup V] [Module E V] [Module.Free E V] [Module.Finite E V]
    (r k : ℕ) (D : Data o F E V r), D.Hyp k →
    D.Finiteness ∧ D.AmplitudeBounds k ∧ D.ShareBound k ∧ D.FibreBound k
section Examples
variable {o F E V : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o]
  [Field F] [Algebra o F] [IsFractionRing o F]
  [CommRing E] [StarRing E] [Algebra F E] [Algebra o E]
  [AddCommGroup V] [Module E V] {r : ℕ}
def Data.InnerDatum.ofUnit (D : Data o F E V r) (hθ : D.θ = 1)
    (L L' : Submodule (MaxOrd o E) V) (hL : D.A.IsInnerLattice D.h L)
    (hL' : D.B.IsInnerLattice D.h L') (hs : ∀ p ∈ L, ∀ p' ∈ L, D.h p p' ∈ MaxOrd o E)
    (hs' : ∀ p ∈ L', ∀ p' ∈ L', D.h p p' ∈ MaxOrd o E) : D.InnerDatum where
  L := L
  L' := L'
  Γ := L'.prod L
  hL := hL
  hL' := hL'
  mem := fun _ hp => hp
  total := fun _ hw => ⟨0, hw, L.zero_mem⟩
  onto := fun _ hw => ⟨0, L'.zero_mem, hw⟩
  ker_left := fun w => by simp [Data.θinv, hθ]
  ker_right := fun w => by simp [Data.θinv, hθ]
  base := ⟨hL'.2.2.1, hL.2.2.1⟩
  isometric := fun p hp p' hp' => by
    simpa [Data.θinv, hθ] using
      (MaxOrd o E).sub_mem (hs' _ hp.1 _ hp'.1) (hs _ hp.2 _ hp'.2)
def negStd (E : Type) [CommRing E] [StarRing E] (n : ℕ) :
    (Fin n → E) →ₗ[E] (Fin n → E) →ₛₗ[starRingEnd E] E :=
  LinearMap.mk₂'ₛₗ (RingHom.id E) (starRingEnd E) (fun x y => -∑ i, x i * star (y i))
    (fun x x' y => by simp [add_mul, Finset.sum_add_distrib, add_comm])
    (fun c x y => by simp [Finset.mul_sum, mul_assoc])
    (fun x y y' => by simp [mul_add, Finset.sum_add_distrib, add_comm])
    (fun c x y => by simp [Finset.mul_sum, mul_left_comm, mul_comm, mul_assoc, starRingEnd_apply])
end Examples
end GlobalTheory.IndefiniteRowSideFullHecke.FrameCoefficientData


