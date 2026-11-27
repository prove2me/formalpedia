-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullbackValuationInvarianceOf
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullbackValuationInvarianceOf
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-27T06:29:51.403337+00:00
-- url     : https://prove2.me/theorems/9e9f7bf7-0d54-43dd-8f90-0bc51cf43f65
-- title:
--   Pullback Valuation Invariance Of
-- statement:
--   Definitions and structural lemmas for Pullback Valuation Invariance Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PullbackValuationInvarianceOf.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_BOfNsmulLeft
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
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
namespace ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing
section Move2
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)}
end Move2
end ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
namespace ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing QForm
def PullReflStatement : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F]
      (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
    ∀ (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (a : O) (N : ℕ),
      1 ≤ N → a * star a = (N : O) → star a * a = (N : O) →
      ∀ k : ℕ, 1 ≤ k → ∀ (s : Fam D.toPre F k) (s' : Fam D.toPre F (k * N)),
        PullAl D F oa a k N s s' → ∀ (χ : D.toPre.X) (q : ℚ),
          VGe D F v (k * N) (star a • χ) (s'.s (star a • χ)) q → VGe D F v k χ (s.s χ) q
def PullGenStatement : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F]
      (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
    ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (w0 : O),
      TraceFormTwistIso D.toPre oa w0 → ∀ (a : O) (N : ℕ),
      1 ≤ N → a * star a = (N : O) → star a * a = (N : O) →
      ∀ k : ℕ, 1 ≤ k → ∀ (χ : D.toPre.X)
        (u : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a χ) (pullε k N))), u.IsGen →
        LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (DegPre.zF D.toPre F).left)
          (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1)))
            (jFK (R := V) F)) →
        ∃ (m : ℕ) (ψ : Fin m → (D.toPre.P.A.left ⟶ D.toPre.P.A.left)) (δ : Fin m → ℤ)
          (eB : LB.Gen (LB.LinComb D.toPre.P.L ψ δ)), eB.IsGen ∧
          FormEq (Sum.elim (fun i => (oa.onB.act a).left ≫ D.toPre.famφB χ i) ψ)
            (Sum.elim (DegPre.famε k) δ) (D.toPre.famφB (star a • χ)) (DegPre.famε (k * N)) ∧
          ∃ c : F, (0 : WithTop ℚ) ≤ v c ∧
            ∀ (y : (DegPre.BF D.toPre F).left)
              (J : ((DegPre.BF D.toPre F).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι),
              Good D.toPre.P.L y J →
              (val u (𝟙 _) y J).val = gs (𝟙 _) y ⊤ (gF D.toPre F c) *
                (val eB (DegPre.prB D.toPre F).left y J).val
def QAlStatement : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), IsQ D.toPre ϖ Q →
    ∀ (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (_oa : D.toPre.OAct O) (a : O) (N : ℕ),
      a * star a = (N : O) → star a * a = (N : O) → ∀ χ : D.toPre.X, Q (star a • χ) = N * Q χ
def PullbackValuationInvariance : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), IsQ D.toPre ϖ Q →
    ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
    ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (w0 : O),
      TraceFormTwistIso D.toPre oa w0 → ∀ (a : O) (N : ℕ),
      1 ≤ N → a * star a = (N : O) → star a * a = (N : O) →
      ∀ k : ℕ, 1 ≤ k → ∀ (s : Fam D.toPre F k) (s' : Fam D.toPre F (k * N)),
        PullAl D F oa a k N s s' → ∀ r : ℚ, NuGe D Q F v k s r ↔ NuGe D Q F v (k * N) s' r
def PullbackValuationForwardBound : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), IsQ D.toPre ϖ Q →
    ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
    ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (w0 : O),
      TraceFormTwistIso D.toPre oa w0 → ∀ (a : O) (N : ℕ),
      1 ≤ N → a * star a = (N : O) → star a * a = (N : O) →
      ∀ k : ℕ, 1 ≤ k → ∀ (s : Fam D.toPre F k) (s' : Fam D.toPre F (k * N)),
        PullAl D F oa a k N s s' → ∀ r : ℚ, NuGe D Q F v k s r → NuGe D Q F v (k * N) s' r
end ReciprocityTheory.ChartRestriction.G.DVR


