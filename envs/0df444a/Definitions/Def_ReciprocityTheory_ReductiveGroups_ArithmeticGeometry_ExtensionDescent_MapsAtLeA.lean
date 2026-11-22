-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:38:29.844805+00:00
-- url     : https://prove2.me/theorems/dac78f0d-7623-42e4-80cd-c6f3370a301a
-- title:
--   Maps At Le A
-- statement:
--   Definitions and structural lemmas for Maps At Le A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/MapsAtLeA.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
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
namespace GeneratorPullback
variable {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
def finProdGen {J : Type} [Fintype J] (φ : J → K → (Y ⟶ X)) (ε : J → K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i))) :
    LB.Gen (LB.LinComb L (K := J × K) (fun p => φ p.1 p.2) (fun p => ε p.1 p.2)) where
  s := fun j => ∏ i, res ((fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (i, k)) :
      LB.wchart L (fun p : J × K => φ p.1 p.2) j ≤ LB.wchart L (φ i) (fun k => j (i, k)))
    ((t i).s _)
variable {X' : Scheme.{0}} (L' : LB X') {J : Type} [Fintype J]
lemma mapsAt_le_b (pr : J → (X' ⟶ X)) (p : Y ⟶ X') (jN : J → L.ι) (jL : L'.ι) :
    p ⁻¹ᵁ (LB.div (LB.LinComb L pr (fun _ => 1)) L').U (jN, jL) ≤
      LB.wchart L (fun i => p ≫ pr i) jN := by
  intro x hx
  first
  | exact Set.mem_iInter.2 fun i => Set.mem_iInter.1 hx.2 i
  | exact Set.mem_iInter.2 fun i => Set.mem_iInter.1 hx.1 i
lemma mapsAt_le_a (pr : J → (X' ⟶ X)) (p : Y ⟶ X') (jN : J → L.ι) (jL : L'.ι) :
    p ⁻¹ᵁ (LB.div (LB.LinComb L pr (fun _ => 1)) L').U (jN, jL) ≤
      LB.wchart L' (fun _ : PUnit => p) (fun _ => jL) := by
  intro x hx
  first
  | exact Set.mem_iInter.2 fun _ => hx.1
  | exact Set.mem_iInter.2 fun _ => hx.2
def MapsAt (pr : J → (X' ⟶ X)) (w : LB.Iso L' (LB.LinComb L pr (fun _ => 1))) (p : Y ⟶ X') (n : ℤ)
    (a : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => p) (fun _ => n)))
    (b : LB.Gen (LB.LinComb L (K := J) (fun i => p ≫ pr i) (fun _ => n))) : Prop :=
  ∀ (jN : J → L.ι) (jL : L'.ι),
    res (mapsAt_le_b L L' pr p jN jL) (b.s jN) =
      (pullU p _ (w.s (jN, jL))) ^ n * res (mapsAt_le_a L L' pr p jN jL) (a.s (fun _ => jL))
end GeneratorPullback
section Pow
variable {S : Scheme.{0}}
structure IsPowPolAV (P' P : PolAV S) (j : ℕ) extends IsPowGrp P'.A P.A j where
  w : LB.Iso P'.L (boxLB P.L pr)
  w_gen : w.IsGen
end Pow
section PowDeg
variable {R : Type} [CommRing R] [IsDomain R]
structure IsPowDeg (D' D : DegPre R) (j : ℕ) where
  pw : IsPowGrp D'.P.A D.P.A j
  w : LB.Iso D'.P.L (boxLB D.P.L pw.pr)
  w_gen : w.IsGen
  w_rig : ∃ b : LB.Gen (LB.LinComb D.P.L (K := Fin j)
      (fun i => eSec D'.P.A ≫ (pw.pr i).left) (fun _ => 1)),
    GeneratorPullback.MapsAt D.P.L D'.P.L (fun i => (pw.pr i).left) w (eSec D'.P.A) 1 D'.rig b ∧
    LB.Gen.Corr D.P.L _ _ _ _ b
      (GeneratorPullback.finProdGen D.P.L (J := Fin j) (fun _ _ => eSec D.P.A) (fun _ _ => 1) (fun _ => D.rig))
  xe : D'.X ≃+ (Fin j → D.X)
  c_pr : ∀ (x : D'.X) (i : Fin j), D'.c x ≫ pw.pr i = D.c (xe x i)
  w_psi : ∀ x : D'.X, ∃ b : LB.Gen (LB.LinComb D.P.L (K := Fin j)
      (fun i => D'.xK x ≫ (pw.pr i).left) (fun _ => -1)),
    GeneratorPullback.MapsAt D.P.L D'.P.L (fun i => (pw.pr i).left) w (D'.xK x) (-1) (D'.psi x) b ∧
    LB.Gen.Corr D.P.L _ _ _ _ b
      (GeneratorPullback.finProdGen D.P.L (J := Fin j) (fun i _ => D.xK (xe x i)) (fun _ _ => -1)
        (fun i => D.psi (xe x i)))
end PowDeg
section UnifPow
open scoped CategoryTheory.Obj
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
structure UnifPowOf {j : ℕ} {D D' : DegData R I}
    {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j)
    (pG : IsPowGrp G' G j) (U' : Unif I D' A' G') (U : Unif I D A G) where
  gen_pr : ∀ i, U'.gen.hom ≫ pA.pr i = (Over.pullback (jK R)).map (pG.pr i) ≫ U.gen.hom
  wL : LB.Iso U'.LG.L (boxLB U.LG.L pG.pr)
  wL_gen : wL.IsGen
  wL_rig : ∃ b : LB.Gen (LB.LinComb U.LG.L (K := Fin j)
      (fun i => eSec G' ≫ (pG.pr i).left) (fun _ => 1)),
    GeneratorPullback.MapsAt U.LG.L U'.LG.L (fun i => (pG.pr i).left) wL (eSec G') 1 U'.LG.rig b ∧
    LB.Gen.Corr U.LG.L _ _ _ _ b
      (GeneratorPullback.finProdGen U.LG.L (J := Fin j) (fun _ _ => eSec G) (fun _ _ => 1) (fun _ => U.LG.rig))
  q_pr : ∀ (e : ℕ) (i : Fin j),
    (U'.gt e).q ≫ (Over.pullback (thick R I e)).map (pD.pw.pr i) =
      (Over.pullback (thick R I e)).map (pG.pr i) ≫ (U.gt e).q
def UnifPowSt : Prop :=
  ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R))))
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) (j : ℕ)
    (D' : DegData R I) (A' : PolAV (Spec (CommRingCat.of (FractionRing R))))
    (G' : Over (Spec (CommRingCat.of R))) [GrpObj G'] [IsCommMonObj G']
    (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j),
    ∃ U' : Unif I D' A' G', Nonempty (UnifPowOf pD pA pG U' U)
end UnifPow
end ReciprocityTheory.ChartRestriction.G.Out


