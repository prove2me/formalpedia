-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_QSurjective
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_QSurjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:25:19.151133+00:00
-- url     : https://prove2.me/theorems/6f2a5199-9ff2-40a2-83d8-a23df6a03b68
-- title:
--   QSurjective
-- statement:
--   Definitions and structural lemmas for QSurjective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/AbelianSchemeQuotients/QSurjective.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_SplitExtDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
namespace ReciprocityTheory.ChartRestriction.G.Semi
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TopologicalSpace
open scoped CategoryTheory.Obj
attribute [local instance] SplitExt.free SplitExt.finite
namespace SplitExt
variable {S : Scheme.{u}} (E : SplitExt S)
noncomputable abbrev basis : Module.Basis (Module.Free.ChooseBasisIndex ℤ E.X) ℤ E.X :=
  Module.Free.chooseBasis ℤ E.X
abbrev ChartIdx : Type u := ∀ k : Module.Free.ChooseBasisIndex ℤ E.X, (E.O (E.basis k)).L.ι
def chart (j : E.ChartIdx) : E.B.left.Opens := ⨅ k, (E.O (E.basis k)).L.U (j k)
lemma chart_le (j : E.ChartIdx) (k : Module.Free.ChooseBasisIndex ℤ E.X) :
    E.chart j ≤ (E.O (E.basis k)).L.U (j k) :=
  iInf_le (fun k => (E.O (E.basis k)).L.U (j k)) k
end SplitExt
noncomputable def charUnit (S : Scheme.{u}) (X : Type u) [AddCommGroup X] (χ : X) :
    Γ((splitTorus S X).left, ⊤)ˣ :=
  res (fun x _ => show (pullback.fst (splitTorusAff ZU X).hom (toZ S)).base x ∈ (⊤ : Opens _)
      from trivial)
    (pullU (pullback.fst (splitTorusAff ZU X).hom (toZ S)) ⊤
      (Units.map (Scheme.ΓSpecIso (torusRing ZU X)).inv.hom.toMonoidHom
        (Units.map (AddMonoidAlgebra.of ZU X) (toUnits (Multiplicative.ofAdd χ)))))
structure SplitExt.GtDatum {S : Scheme.{u}} (E : SplitExt S) (G : Over S) [GrpObj G] where
  q : G ⟶ E.B
  i : splitTorus S E.X ⟶ G
  q_hom : IsMonHom q
  i_hom : IsMonHom i
  q_flat : Flat q.left
  q_surjective : Surjective q.left
  q_affine : IsAffineHom q.left
  isKernel : IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ E.B)

  u : ∀ (j : E.ChartIdx) (_k : Module.Free.ChooseBasisIndex ℤ E.X),
    Γ(G.left, q.left ⁻¹ᵁ E.chart j)ˣ
  coord : ∀ (j : E.ChartIdx) (V : E.B.left.Opens) (_hV : IsAffineOpen V) (h : V ≤ E.chart j),
    Function.Bijective
      (AddMonoidAlgebra.liftNCRingHom (q.left.app V).hom
        ((Units.coeHom _).comp (AddMonoidHom.toMultiplicativeLeft
          (E.basis.constr ℤ (fun k => Additive.ofMul
            (res (Scheme.Hom.preimage_mono q.left h) (u j k)))).toAddMonoidHom))
        (fun _ _ => Commute.all _ _))
  trans : ∀ (j j' : E.ChartIdx) (k : Module.Free.ChooseBasisIndex ℤ E.X),
    res (Scheme.Hom.preimage_mono q.left (inf_le_right : E.chart j ⊓ E.chart j' ≤ E.chart j'))
        (u j' k) =
      pullU q.left _
          (res (le_inf (inf_le_left.trans (E.chart_le j k)) (inf_le_right.trans (E.chart_le j' k)))
            ((E.O (E.basis k)).L.g (j k) (j' k))) *
        res (Scheme.Hom.preimage_mono q.left (inf_le_left : E.chart j ⊓ E.chart j' ≤ E.chart j))
          (u j k)
  act_le : ∀ j : E.ChartIdx,
    (snd (splitTorus S E.X) G).left ⁻¹ᵁ (q.left ⁻¹ᵁ E.chart j) ≤
      (lift (fst (splitTorus S E.X) G ≫ i) (snd (splitTorus S E.X) G) ≫ μ[G]).left ⁻¹ᵁ
        (q.left ⁻¹ᵁ E.chart j)
  equiv : ∀ (j : E.ChartIdx) (k : Module.Free.ChooseBasisIndex ℤ E.X),
    res (act_le j)
        (pullU (lift (fst (splitTorus S E.X) G ≫ i) (snd (splitTorus S E.X) G) ≫ μ[G]).left _
          (u j k)) =
      res (fun x _ => show (fst (splitTorus S E.X) G).left.base x ∈ (⊤ : Opens _) from trivial)
          (pullU (fst (splitTorus S E.X) G).left ⊤ (charUnit S E.X (E.basis k))) *
        pullU (snd (splitTorus S E.X) G).left _ (u j k)

  unit_norm : ∀ (j : E.ChartIdx) (k : Module.Free.ChooseBasisIndex ℤ E.X),
    res (inf_le_left : eSec G ⁻¹ᵁ (q.left ⁻¹ᵁ E.chart j) ⊓
          ((E.O (E.basis k)).L.pull (eSec E.B)).U (fun _ => j k) ≤
          eSec G ⁻¹ᵁ (q.left ⁻¹ᵁ E.chart j))
        (pullU (eSec G) _ (u j k)) *
      res (inf_le_right : eSec G ⁻¹ᵁ (q.left ⁻¹ᵁ E.chart j) ⊓
          ((E.O (E.basis k)).L.pull (eSec E.B)).U (fun _ => j k) ≤
          ((E.O (E.basis k)).L.pull (eSec E.B)).U (fun _ => j k))
        ((E.O (E.basis k)).rig.s (fun _ => j k)) = 1
def SplitExt.IsGt {S : Scheme.{u}} (E : SplitExt S) (G : Over S) [GrpObj G] : Prop :=
  Nonempty (E.GtDatum G)
noncomputable def SplitExt.GtDatum.weight {S : Scheme.{u}} {E : SplitExt S} {G : Over S} [GrpObj G]
    (D : E.GtDatum G) (j : E.ChartIdx) (V : E.B.left.Opens) (hV : IsAffineOpen V)
    (h : V ≤ E.chart j) (χ : E.X) (s : Γ(G.left, D.q.left ⁻¹ᵁ V)) : Γ(E.B.left, V) :=
  ((Equiv.ofBijective _ (D.coord j V hV h)).symm s).coeff χ
end
end ReciprocityTheory.ChartRestriction.G.Semi


