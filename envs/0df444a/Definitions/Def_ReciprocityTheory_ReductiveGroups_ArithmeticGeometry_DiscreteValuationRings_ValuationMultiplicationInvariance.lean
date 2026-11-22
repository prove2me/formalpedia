-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:15:42.151962+00:00
-- url     : https://prove2.me/theorems/0c1a92f4-fc91-4e23-911f-974a22e10b2e
-- title:
--   Valuation Multiplication Invariance
-- statement:
--   Definitions and structural lemmas for Valuation Multiplication Invariance, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ValuationMultiplicationInvariance.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegOUnif
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
namespace ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing QForm
def ValOver {V : Type} [CommRing V] [IsDomain V] (ϖ : V) (F : Type) [Field F]
    [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)) : Prop :=
  ∀ (c : FractionRing V) (n : ℤ), HasVal ϖ c n → v (algebraMap (FractionRing V) F c) = ((n : ℚ) : WithTop ℚ)
section Defs
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ)
  (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ))
def VGe (k : ℕ) (α : D.toPre.X)
    (s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))) (r : ℚ) : Prop :=
  ∃ (n : ℕ) (a : Fin n → F) (σ : Fin n → D.toPre.SecB k α)
    (σF : Fin n → LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))),
    (∀ i, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (σF i)
        (D.toPre.famφB α) (DegPre.famε k) (σ i) (DegPre.prB D.toPre F).left 1) ∧
    (∀ i, ((r : ℚ) : WithTop ℚ) ≤ v (a i)) ∧
    ∀ j, s.f j = ∑ i, DegPre.constBF D.toPre F (a i) _ * (σF i).f j
def NuGe (k : ℕ) (s : Fam D.toPre F k) (r : ℚ) : Prop :=
  ∀ χ : D.toPre.X, VGe D F v k χ (s.s χ) (r + (Q χ : ℚ) / k)
variable {O : Type} [Ring O] [StarRing O] [Module O D.toPre.X]
def aF (oa : D.toPre.OAct O) (a : O) : DegPre.BF D.toPre F ⟶ DegPre.BF D.toPre F :=
  lift (fst _ _) (DegPre.prB D.toPre F ≫ oa.onB.act a)
def pullφ (oa : D.toPre.OAct O) (a : O) (χ : D.toPre.X) :
    Fin 4 ⊕ Fin 4 → ((DegPre.BF D.toPre F).left ⟶ D.toPre.P.A.left) :=
  Sum.elim (DegPre.famφ D.toPre F (star a • χ)) (fun i => (aF D F oa a).left ≫ DegPre.famφ D.toPre F χ i)
def pullε (k N : ℕ) : Fin 4 ⊕ Fin 4 → ℤ :=
  Sum.elim (DegPre.famε (k * N)) (fun i => - DegPre.famε k i)
def PullAl (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (s : Fam D.toPre F k)
    (s' : Fam D.toPre F (k * N)) : Prop :=
  (∀ χ : D.toPre.X, ∃ u : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a χ) (pullε k N)), u.IsGen ∧
    LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (DegPre.zF D.toPre F).left)
      (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1)))
        (jFK (R := V) F)) ∧
    GeneratorPullback.SecRel D.toPre.P.L (DegPre.famφ D.toPre F (star a • χ)) (DegPre.famε (k * N))
      (s'.s (star a • χ)) (DegPre.famφ D.toPre F χ) (DegPre.famε k) (s.s χ) (aF D F oa a).left
      (pullφ D F oa a χ) (pullε k N) u) ∧
  ∀ β : D.toPre.X, (∀ χ, β ≠ star a • χ) → ∀ j, (s'.s β).f j = 0
def FinOrd (k : ℕ) (p : QkPt D.toPre F k)
    (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))) (ζ : F) :
    Prop :=
  ∃ M : ℕ, 1 ≤ M ∧ ∀ (ss : Fin (M + 1) → Fam D.toPre F k) (ts : Fin M → Fam D.toPre F k),
    (∀ i : Fin M, PhiRel D.toPre F k p w (ss i.castSucc) (ts i) ∧
      Fam.IsSmul D.toPre F ζ (ts i) (ss i.succ)) →
    ∀ α j, ((ss (Fin.last M)).s α).f j = ((ss 0).s α).f j
def Val0 (k : ℕ) (α : D.toPre.X)
    (s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))) (x : F) : Prop :=
  ∃ τ : LB.Gen (LB.LinComb D.toPre.P.L
      (fun i => (DegPre.zF D.toPre F).left ≫ DegPre.famφ D.toPre F α i) (DegPre.famε k)),
    τ.IsGen ∧
    LB.Gen.Corr D.toPre.P.L _ _ _ _ τ
      (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK k) (jFK (R := V) F)) ∧
    ∀ j, ((TF (R := V) F).left.presheaf.map (homOfLE
        ((fun _ hy => Set.mem_iInter.2 fun i => Set.mem_iInter.1 hy i) :
          LB.wchart D.toPre.P.L (fun i => (DegPre.zF D.toPre F).left ≫ DegPre.famφ D.toPre F α i) j ≤
            (DegPre.zF D.toPre F).left ⁻¹ᵁ LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F α) j)).op).hom
        (((DegPre.zF D.toPre F).left.app _).hom (s.f j)) =
      ((TF (R := V) F).left.presheaf.map (homOfLE le_top).op).hom
          ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom x) * (τ.s j).val
def SumTo (x : D.toPre.X → F) (w : F) : Prop :=
  ∀ q : ℚ, ∃ S : Finset D.toPre.X, ∀ T : Finset D.toPre.X, S ⊆ T →
    ((q : ℚ) : WithTop ℚ) ≤ v (w - ∑ α ∈ T, x α)
def ValAt0 (k : ℕ) (s : Fam D.toPre F k) (w : F) : Prop :=
  ∃ x : D.toPre.X → F, (∀ α, Val0 D F k α (s.s α) (x α)) ∧ SumTo D F v x w
def FamIsAdd {k : ℕ} (s s' s'' : Fam D.toPre F k) : Prop :=
  ∀ (α : D.toPre.X) (j : Fin 4 → D.toPre.P.L.ι), (s''.s α).f j = (s.s α).f j + (s'.s α).f j
end Defs
def ValuationMinRepresentatives : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), IsQ D.toPre ϖ Q →
    ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
    ∀ k : ℕ, 1 ≤ k → ∀ S : Finset D.toPre.X, (∀ χ : D.toPre.X, ∃ α ∈ S, ∃ m0, χ = α + k • m0) →
      ∀ (s : Fam D.toPre F k) (r : ℚ),
        NuGe D Q F v k s r ↔ ∀ α ∈ S, VGe D F v k α (s.s α) (r + (Q α : ℚ) / k)
def PositiveValuationMaximalIdeal : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), IsQ D.toPre ϖ Q →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)),
    ValOver ϖ F v →
    ∀ k : ℕ, 1 ≤ k → ∀ s : Fam D.toPre F k, NuGe D Q F v k s 0 →
      ((∃ r : ℚ, 0 < r ∧ NuGe D Q F v k s r) ↔
        ∃ (ζ : F) (s' : Fam D.toPre F k), (0 : WithTop ℚ) < v ζ ∧ NuGe D Q F v k s' 0 ∧
          Fam.IsSmul D.toPre F ζ s' s)
def ThetaSectionValuationZero : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), IsQ D.toPre ϖ Q →
    ∀ (vK : AddValuation (FractionRing V) (WithTop ℚ)), ValOver ϖ (FractionRing V) vK →
    ∀ (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V)))
      [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G) (ϑ : H0 U.LG.L 1), IsTheta U ϑ →
      ∀ s : U.SecK 1,
        GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (fun _ => ((1 : ℕ) : ℤ)) s
          (fun _ : Fin 1 => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ)) ϑ (pullback.fst G.hom (jK V)) 1 →
      ∀ E : Fam D.toPre (FractionRing V) 1, U.Expands 1 s E →
        NuGe D Q (FractionRing V) vK 1 E 0 ∧ ¬ ∃ r : ℚ, 0 < r ∧ NuGe D Q (FractionRing V) vK 1 E r
def ValuationMultiplicationInvariance : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), IsQ D.toPre ϖ Q →
    ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
    ∀ (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (a : O) (N : ℕ),
      1 ≤ N → a * star a = (N : O) → star a * a = (N : O) →
      ∀ k : ℕ, 1 ≤ k → ∀ (s : Fam D.toPre F k) (s' : Fam D.toPre F (k * N)),
        PullAl D F oa a k N s s' → ∀ r : ℚ, NuGe D Q F v k s r ↔ NuGe D Q F v (k * N) s' r
def FiniteOrderValuationInvariance : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), IsQ D.toPre ϖ Q →
    ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
    ∀ k : ℕ, 1 ≤ k → ∀ (p : QkPt D.toPre F k)
      (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))),
      w.IsGen → ∀ ζ : F, ζ ≠ 0 → FinOrd D F k p w ζ →
      ∀ s t s' : Fam D.toPre F k, PhiRel D.toPre F k p w s t → Fam.IsSmul D.toPre F ζ t s' →
        ∀ r : ℚ, NuGe D Q F v k s r ↔ NuGe D Q F v k s' r
def ValuationBoundAtZero : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), IsQ D.toPre ϖ Q →
    ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
    ∀ m : ℕ, 1 ≤ m → ∀ (R' : ℕ) (β : D.toPre.X) (s : Fam D.toPre F m),
      (∀ α : D.toPre.X, (∀ z : D.toPre.X, α ≠ β + R' • z) → ∀ j, (s.s α).f j = 0) →
      NuGe D Q F v m s 0 → ∀ w : F, ValAt0 D F v m s w →
      ∀ q : ℚ, (∀ z : D.toPre.X, q ≤ (Q (β + R' • z) : ℚ) / m) → ((q : ℚ) : WithTop ℚ) ≤ v w
def NuAddStatement : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ)
    (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)) (k : ℕ)
    (s s' s'' : Fam D.toPre F k) (r : ℚ), FamIsAdd D F s s' s'' →
      NuGe D Q F v k s r → NuGe D Q F v k s' r → NuGe D Q F v k s'' r
def NuSmulStatement : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ)
    (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)) (k : ℕ)
    (ζ : F) (q r : ℚ) (s s' : Fam D.toPre F k), ((q : ℚ) : WithTop ℚ) ≤ v ζ →
      Fam.IsSmul D.toPre F ζ s s' → NuGe D Q F v k s r → NuGe D Q F v k s' (r + q)
def GermIntegrality : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), IsQ D.toPre ϖ Q →
    ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)) (k : ℕ)
      (s : Fam D.toPre F k), NuGe D Q F v k s 0 → ∀ χ, VGe D F v k χ (s.s χ) 0
def UUStatement : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), IsQ D.toPre ϖ Q →
    ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
    (IsAlgClosed F ∨ ∃ d : ℕ, 1 ≤ d ∧ ∀ x : F, x ≠ 0 → ∃ n : ℤ, v x = (((n : ℚ) / d : ℚ) : WithTop ℚ)) →
    ∀ k : ℕ, 1 ≤ k → ∃ b : Fin (k ^ (D.toPre.rank + D.toPre.P.g)) → Fam D.toPre F k,
      LinearIndependent F b ∧ (∀ i, NuGe D Q F v k (b i) 0) ∧
      ∀ s : Fam D.toPre F k, NuGe D Q F v k s 0 ↔
        ∃ c : Fin (k ^ (D.toPre.rank + D.toPre.P.g)) → F, (∀ i, (0 : WithTop ℚ) ≤ v (c i)) ∧
          s = ∑ i, c i • b i
end ReciprocityTheory.ChartRestriction.G.DVR


