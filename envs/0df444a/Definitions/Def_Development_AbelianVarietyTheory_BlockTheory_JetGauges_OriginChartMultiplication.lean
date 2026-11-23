-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_OriginChartMultiplication
-- name    : Development_AbelianVarietyTheory_BlockTheory_JetGauges_OriginChartMultiplication
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:07:59.245336+00:00
-- url     : https://prove2.me/theorems/58535204-5148-4efc-81ec-a8571215ca8b
-- title:
--   Origin Chart Multiplication
-- statement:
--   Definitions and structural lemmas for Origin Chart Multiplication, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/OriginChartMultiplication.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegUnif
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LawsChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
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
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.IndefiniteRowSideFullHecke.OriginChartMultiplication
def jetOfSeries {R : Type} [CommRing R] {κ : Type} [Finite κ] (m : ℕ) (f : MvPowerSeries κ R) :
    JetR R κ m :=
  Ideal.Quotient.mk _ (MvPowerSeries.truncTotal (m + 1) f)
def IsOriginChart {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] {d : ℕ}
    (x : ∀ m : ℕ, algOver R (JetR R (Fin d) m) ⟶ G) (F : FGLaw R d) : Prop :=
  (∀ m, algOverHom (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m) ∧
  (∀ m, algOverHom (jetZeroR R (Fin d) m) ≫ x m = toUnit _ ≫ η[G]) ∧
  (∀ (κ : Type) (m : ℕ) (y : algOver R (JetR R κ m) ⟶ G),
    algOverHom (jetZeroR R κ m) ≫ y = toUnit _ ≫ η[G] →
    ∃! ψ : JetR R (Fin d) m →ₐ[R] JetR R κ m,
      (∀ j, jetZeroR R κ m (ψ (zR m j)) = 0) ∧ y = algOverHom ψ ≫ x m) ∧
  (∀ m, ∃ ψ₀ ψ₁ ψ : JetR R (Fin d) m →ₐ[R] JetR R (Fin 2 × Fin d) m,
    (∀ j, ψ₀ (zR m j) = zR m ((0 : Fin 2), j)) ∧ (∀ j, ψ₁ (zR m j) = zR m ((1 : Fin 2), j)) ∧
    (∀ j, ψ (zR m j) = jetOfSeries m (F.F j)) ∧
    lift (algOverHom ψ₀ ≫ x m) (algOverHom ψ₁ ≫ x m) ≫ μ[G] = algOverHom ψ ≫ x m)
def mulSeries {R : Type} [CommRing R] {d : ℕ} (F : FGLaw R d) (n : ℕ) : Pt R 1 d :=
  Nat.rec (motive := fun _ => Pt R 1 d) 0 (fun _ a => F.add a (pt R d 0)) n
theorem mulSeries_one {R : Type} [CommRing R] {d : ℕ} (F : FGLaw R d) :
    mulSeries F 1 = pt R d 0 := by
  funext i
  exact F.unit i
def torsionIdeal {T O : Type} [CommRing T] [CommRing O] (f : T →+* O) {d : ℕ} (F : FGLaw T d)
    (n : ℕ) : Ideal (PS O 1 d) :=
  Ideal.span (Set.range fun i : Fin d => MvPowerSeries.map f (mulSeries F n i))
abbrev TorsionRing {T O : Type} [CommRing T] [CommRing O] (f : T →+* O) {d : ℕ} (F : FGLaw T d)
    (n : ℕ) : Type :=
  PS O 1 d ⧸ torsionIdeal f F n
def FiniteFreeReducedSeparated (O C Q : Type) [CommRing O] [Field C] [Algebra O C]
    [CommRing Q] [Algebra O Q] : Prop :=
  Module.Finite O Q ∧ Module.Free O Q ∧ IsReduced (C ⊗[O] Q) ∧
    ∀ a b : Q, (∀ φ : Q →ₐ[O] O, φ a = φ b) → a = b
def TorsionFiniteFreeAlongIdeal : Prop :=
  ∀ (p : ℕ), p.Prime →
  ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [IsNoetherianRing T] [CharZero T]
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T], ¬ IsUnit (p : T) →
  ∀ (I : Ideal T), I ≠ ⊤ →
  ∀ (D : DegData T I) (A : PolAV (Spec (CommRingCat.of (FractionRing T))))
    (G : Over (Spec (CommRingCat.of T))) [GrpObj G] [IsCommMonObj G], Nonempty (UnifPre I D A G) →
  ∀ (d : ℕ) (x : ∀ m : ℕ, algOver T (JetR T (Fin d) m) ⟶ G) (F : FGLaw T d),
    IsOriginChart G x F →
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
    (O : Type) [CommRing O] [Algebra O C], v.Integers O →
    IsAdicComplete (Ideal.span {(p : O)}) O →
  ∀ (f : T →+* O), IsLocalHom f →
  ∀ m : ℕ, FiniteFreeReducedSeparated O C (TorsionRing f F (p ^ m))
def TorsionFiniteFree : Prop :=
  ∀ (p : ℕ), p.Prime →
  ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [IsNoetherianRing T] [CharZero T]
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T], ¬ IsUnit (p : T) →
  ∀ (D : DegData T (IsLocalRing.maximalIdeal T))
    (A : PolAV (Spec (CommRingCat.of (FractionRing T))))
    (G : Over (Spec (CommRingCat.of T))) [GrpObj G] [IsCommMonObj G],
    Nonempty (UnifPre (IsLocalRing.maximalIdeal T) D A G) →
  ∀ (d : ℕ) (x : ∀ m : ℕ, algOver T (JetR T (Fin d) m) ⟶ G) (F : FGLaw T d),
    IsOriginChart G x F →
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
    (O : Type) [CommRing O] [Algebra O C], v.Integers O →
    IsAdicComplete (Ideal.span {(p : O)}) O →
  ∀ (f : T →+* O), IsLocalHom f →
  ∀ m : ℕ, FiniteFreeReducedSeparated O C (TorsionRing f F (p ^ m))
example {T O : Type} [CommRing T] [CommRing O] (f : T →+* O) {d : ℕ} (F : FGLaw T d) :
    torsionIdeal f F 1 = Ideal.span (Set.range (pt O d (0 : Fin 1))) := by
  unfold torsionIdeal
  rw [mulSeries_one]
  unfold pt
  simp
end GlobalTheory.IndefiniteRowSideFullHecke.OriginChartMultiplication


