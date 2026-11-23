-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ChartPointCongruence_InChartSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ChartPointCongruence_InChartSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:07:22.359311+00:00
-- url     : https://prove2.me/theorems/7fa43670-68e9-4fe6-a4b0-8d9b2a378230
-- title:
--   In Chart St
-- statement:
--   Definitions and structural lemmas for In Chart St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/ChartPointCongruence/InChartSt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_UnivChartLoc
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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open MvPowerSeries
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
namespace ReciprocityTheory.ChartRestriction.G.Pdiv.ChPt
attribute [local instance] Over.cartesianMonoidalCategory
example : @JetR = @ReciprocityTheory.ChartRestriction.G.Chart.JetR := rfl
example : @zR = @ReciprocityTheory.ChartRestriction.G.Chart.zR := rfl
def NilSt : Prop :=
  ∀ (p : ℕ), p ≠ 0 → ∀ (C : Type) [Field C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O]
    [Algebra O C], v.Integers O → ∀ [IsLocalRing O], ¬ IsUnit (p : O) →
    ∀ c ∈ maximalIdeal O, ∀ n : ℕ, ∃ N : ℕ, c ^ N ∈ Ideal.span {(p : O) ^ n}
def JetSt : Prop :=
  ∀ (T B : Type) [CommRing T] [CommRing B] [Algebra T B] (κ : Type) [Finite κ] (b : κ → B),
    (∀ j, IsNilpotent (b j)) → ∃ k₀ : ℕ, ∀ k ≥ k₀,
      ∃! ψ : JetR T κ k →ₐ[T] B, ∀ j, ψ (zR k j) = b j
def EvalSt : Prop :=
  ∀ (T O : Type) [CommRing T] [CommRing O] [Algebra T O] (I : Ideal O) (m d k : ℕ)
    (χ : JetR T (Fin m × Fin d) k →ₐ[T] O ⧸ I) (c : Fin m → Fin d → O),
    (∀ q, χ (zR k q) = Ideal.Quotient.mk I (c q.1 q.2)) → ∀ f : PS T m d,
      χ (psJet k f) = Ideal.Quotient.mk I (MvPolynomial.eval (fun q : Fin m × Fin d => c q.1 q.2)
        (MvPowerSeries.trunc O (Finsupp.equivFunOnFinite.symm fun _ => k + 1) (MvPowerSeries.map (algebraMap T O) f)))
def InChartSt : Prop :=
  ∀ (T : Type) [CommRing T] [IsLocalRing T] (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G]
    (d : ℕ) (F : FGLaw T d) (x : ∀ m : ℕ, algOver T (JetR T (Fin 1 × Fin d) m) ⟶ G), IsChartJ G F x →
    ∀ Cc : ReciprocityTheory.ChartRestriction.G.Chart.Chart G,
    ∃ φ : ∀ k : ℕ, Γ(G.left, Cc.U) →ₐ[T] JetR T (Fin 1 × Fin d) k,
      (∀ k, x k = ReciprocityTheory.ChartRestriction.G.Chart.pt Cc (φ k)) ∧
      (∀ k, (ReciprocityTheory.ChartRestriction.G.Chart.jetTruncR T (Fin 1 × Fin d) k).comp (φ (k + 1)) = φ k) ∧
      ∀ k, (ReciprocityTheory.ChartRestriction.G.Chart.jetAug T (Fin 1 × Fin d) k).comp (φ k) = ReciprocityTheory.ChartRestriction.G.Chart.eps Cc
def SurjSt : Prop :=
  ∀ (T : Type) [CommRing T] [IsLocalRing T] (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G], Smooth G.hom →
    ∀ (d : ℕ) (F : FGLaw T d) (x : ∀ m : ℕ, algOver T (JetR T (Fin 1 × Fin d) m) ⟶ G), IsChartJ G F x →
    ∀ (Cc : ReciprocityTheory.ChartRestriction.G.Chart.Chart G) (k : ℕ) (φ : Γ(G.left, Cc.U) →ₐ[T] JetR T (Fin 1 × Fin d) k),
      x k = ReciprocityTheory.ChartRestriction.G.Chart.pt Cc φ → Function.Surjective φ
def LocSt : Prop :=
  ∀ (T O : Type) [CommRing T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    (G : Over (Sp T)) [GrpObj G] (Cc : ReciprocityTheory.ChartRestriction.G.Chart.Chart G) (p : O), p ∈ maximalIdeal O →
    ∀ (Q : algOver T O ⟶ G) (h : Γ(G.left, Cc.U) →ₐ[T] O ⧸ Ideal.span {p}),
      algOverHom (Ideal.Quotient.mkₐ T (Ideal.span {p})) ≫ Q = ReciprocityTheory.ChartRestriction.G.Chart.pt Cc h →
      ∃ h' : Γ(G.left, Cc.U) →ₐ[T] O, Q = ReciprocityTheory.ChartRestriction.G.Chart.pt Cc h'
def SepSt : Prop :=
  ∀ (T A O : Type) [CommRing T] [CommRing A] [Algebra T A] [CommRing O] [Algebra T O] (p : O),
    IsHausdorff (Ideal.span {p}) O → ∀ h h' : A →ₐ[T] O,
      (∀ n : ℕ, (Ideal.Quotient.mkₐ T (Ideal.span {p ^ n})).comp h = (Ideal.Quotient.mkₐ T _).comp h') → h = h'
def AlgLimSt : Prop :=
  ∀ (T A O : Type) [CommRing T] [CommRing A] [Algebra T A] [CommRing O] [Algebra T O] (p : O),
    IsAdicComplete (Ideal.span {p}) O → ∀ a : ∀ n : ℕ, A →ₐ[T] O ⧸ Ideal.span {p ^ n},
      (∀ (n : ℕ) (z : A) (y : O), Ideal.Quotient.mk _ y = a (n + 1) z → Ideal.Quotient.mk _ y = a n z) →
      ∃ h : A →ₐ[T] O, ∀ n, (Ideal.Quotient.mkₐ T (Ideal.span {p ^ n})).comp h = a n
def LawSt : Prop :=
  ∀ (T : Type) [CommRing T] (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G]
    (d : ℕ) (F : FGLaw T d) (x : ∀ m : ℕ, algOver T (JetR T (Fin 1 × Fin d) m) ⟶ G), IsChartJ G F x →
    ∀ (B : Type) [CommRing B] [Algebra T B] (k : ℕ) (χ : JetR T (Fin 2 × Fin d) k →ₐ[T] B),
      algOverHom (χ.comp (substJ k F.F F.const)) ≫ x k =
        (algOverHom (χ.comp (jetPt (d := d) (0 : Fin 2) k)) ≫ x k) *
          (algOverHom (χ.comp (jetPt (d := d) (1 : Fin 2) k)) ≫ x k)
end ReciprocityTheory.ChartRestriction.G.Pdiv.ChPt


