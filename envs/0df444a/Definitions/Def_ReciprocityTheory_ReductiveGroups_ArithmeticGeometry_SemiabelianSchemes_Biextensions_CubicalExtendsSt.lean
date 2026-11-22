-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:22:29.051893+00:00
-- url     : https://prove2.me/theorems/ac43ddca-66a5-4fdb-9d23-80551af82f53
-- title:
--   Cubical Extends St
-- statement:
--   Definitions and structural lemmas for Cubical Extends St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/Biextensions/CubicalExtendsSt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.Semi
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
universe u
attribute [local instance] Over.cartesianMonoidalCategory
def lam_isBiextSt : Prop :=
  ∀ (S : Scheme.{u}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (_c : CubicalStr G L),
    Nonempty (IsBiext G (abelian₂ G L.L))
def extendGenSt : Prop :=
  ∀ (V : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (K : Type u) [Field K] [Algebra V K] [IsFractionRing V K]
    (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] [GeometricallyConnected G.hom]
    (eA : Spec (CommRingCat.of K) ⟶ genA V K G), eA ≫ jA V K G = eK V K G →
    ∀ (N : RigLB G) (r : LB.Gen (N.L.pull (jA V K G))), r.IsGen →
    LB.Gen.Corr N.L _ _ _ _ (LB.pullGen N.L _ _ r eA) (LB.pullGen N.L _ _ N.rig (etaK V K)) →
    ∃! r' : LB.Gen N.L, r'.IsGen ∧ LB.genPull N.L r' (jA V K G) = r
def extend_existsSt : Prop :=
  ∀ (V : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (K : Type u) [Field K] [Algebra V K] [IsFractionRing V K]
    (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] [GeometricallyConnected G.hom]
    (eA : Spec (CommRingCat.of K) ⟶ genA V K G), eA ≫ jA V K G = eK V K G →
    ∀ (L : LB (genA V K G)), L.IsLB → ∀ (ρ : LB.Gen (L.pull eA)), ρ.IsGen →
    ∃ (L' : RigLB G) (φ : LB.Iso (L'.L.pull (jA V K G)) L), φ.IsGen
def cubical_extendsSt : Prop :=
  ∀ (V : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (K : Type u) [Field K] [Algebra V K] [IsFractionRing V K]
    (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] [GeometricallyConnected G.hom]
    (selfLieBasisVector : Spec (CommRingCat.of K) ⟶ pullback (G3 G).hom (etaK V K)),
    selfLieBasisVector ≫ genericFiberCubeInclusion V K G = etaK V K ≫ eSec (G3 G) →
    ∀ (L : RigLB G) (t : LB.Gen (LB.LinComb L.L (fun I => genericFiberCubeInclusion V K G ≫ thφ G (x3 G) I) thε)),
    LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ t selfLieBasisVector) (LB.oneGen L.L) →
    t.IsGen →
    ∃! c : LB.Gen (Theta G L.L), c.IsGen ∧ LB.pullGen L.L _ _ c (genericFiberCubeInclusion V K G) = t
def corr_of_genericSt : Prop :=
  ∀ (V : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (K : Type u) [Field K] [Algebra V K] [IsFractionRing V K]
    (G : Over (Spec (CommRingCat.of V)))
    (T : Over (Spec (CommRingCat.of V))) [Flat T.hom] [IsReduced T.left]
    (L : LB G.left) {Kα Kβ : Type u} [Fintype Kα] [Fintype Kβ]
    (φ : Kα → (T.left ⟶ G.left)) (ε : Kα → ℤ) (φ' : Kβ → (T.left ⟶ G.left)) (ε' : Kβ → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')),
    LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t (pullback.fst T.hom (etaK V K)))
      (LB.pullGen L _ _ t' (pullback.fst T.hom (etaK V K))) →
    LB.Gen.Corr L _ _ _ _ t t'
def lemmaBSt : Prop :=
  ∀ (V : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] [GeometricallyConnected G.hom]
    (N : LB G.left), N.IsLB → ∀ (s : LB.Sec N) (π : V), Irreducible π →
    (∀ i (e : ℕ), s.f i ∈ Ideal.span {(G.left.presheaf.map (homOfLE (le_top :
        N.U i ≤ ⊤)).op).hom ((G.hom.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom π))} ^ e) →
    ∀ i, s.f i = 0
end
end ReciprocityTheory.ChartRestriction.G.Semi


