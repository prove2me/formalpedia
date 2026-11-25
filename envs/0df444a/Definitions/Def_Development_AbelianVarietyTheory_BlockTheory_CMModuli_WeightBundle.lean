-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_WeightBundle
-- name    : Development_AbelianVarietyTheory_BlockTheory_CMModuli_WeightBundle
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T15:42:49.132801+00:00
-- url     : https://prove2.me/theorems/5b1eeade-3fb9-445a-ad75-981f6cf8524d
-- title:
--   Weight Bundle
-- statement:
--   Definitions and structural lemmas for Weight Bundle, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/WeightBundle.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Theorems.Thm_GlobalTheory_UU_val_sym_triv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.CubicalBundleRestrictions
section Notions
variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {X : Type} [AddCommGroup X]
def isoV {Y Y' Z : Scheme.{0}} {L : LB Y} {L' : LB Y'} {F : Y' ⟶ Y} (w : LB.Iso L' (L.pull F)) (z : Z)
    (J : (Z ⟶ Y) → L.ι) (J' : (Z ⟶ Y') → L'.ι) (r : Z ⟶ Y') : (Z.presheaf.stalk z)ˣ :=
  gw w r z (J (r ≫ F)) (J' r)
def BiRestricts {L : RigLB G} {L' : RigLB G'} {c : CubicalStr G L} {c' : CubicalStr G' L'} (f : S' ⟶ S)
    {F : G'.left ⟶ G.left} (w : LB.Iso L'.L (L.L.pull F)) {i : splitTorus S X ⟶ G} {i' : splitTorus S' X ⟶ G'}
    (s : BiTriv c i) (s' : BiTriv c' i') : Prop :=
  ∀ (Z : Over S') (t : Z ⟶ splitTorus S' X) (x : Z ⟶ G') (r : Z.left ⟶ (splitTorus S X ⊗ G).left),
    r ≫ (fst (splitTorus S X) G).left = t.left ≫ SplitTorus.bcMap f X → r ≫ (snd (splitTorus S X) G).left = x.left ≫ F →
    ∀ (z : Z.left) (J) (J'), Good L.L z J → Good L'.L z J' →
      val s.s r z J * isoV w z J J' (t ≫ i').left * isoV w z J J' x.left =
        isoV w z J J' ((t ≫ i') * x).left * isoV w z J J' (1 : Z ⟶ G').left * val s'.s (lift t x).left z J'
def CubRestricts {L : RigLB G} {L' : RigLB G'} {c : CubicalStr G L} {c' : CubicalStr G' L'} (f : S' ⟶ S)
    {F : G'.left ⟶ G.left} (w : LB.Iso L'.L (L.L.pull F)) {i : splitTorus S X ⟶ G} {i' : splitTorus S' X ⟶ G'}
    (σ : CubTriv c i) (σ' : CubTriv c' i') : Prop :=
  ∀ (Z : Over S') (t : Z ⟶ splitTorus S' X) (z : Z.left) (J) (J'), Good L.L z J → Good L'.L z J' →
    val σ.s (t.left ≫ SplitTorus.bcMap f X) z J * isoV w z J J' (1 : Z ⟶ G').left =
      isoV w z J J' (t ≫ i').left * val σ'.s t.left z J'
def IsEquivariant (Q : TQ G X) {L : RigLB G} {c : CubicalStr G L} (s : BiTriv c Q.i) (σ : CubTriv c Q.i)
    (M : LB Q.B.left) (w : LB.Iso L.L (M.pull Q.q.left)) : Prop :=
  ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (x : Z ⟶ G) (z : Z.left) (J) (J'), Good M z J → Good L.L z J' →
    isoV w z J J' ((t ≫ Q.i) * x).left * val s.s (lift t x).left z J' * val σ.s t.left z J' = isoV w z J J' x.left
def SquareComm {Y Y' B B' : Scheme.{0}} {L : LB Y} {L' : LB Y'} {M : LB B} {M' : LB B'} {F : Y' ⟶ Y} {q : Y ⟶ B}
    {q' : Y' ⟶ B'} {FB : B' ⟶ B} (w : LB.Iso L' (L.pull F)) (a : LB.Iso L (M.pull q)) (a' : LB.Iso L' (M'.pull q'))
    (v : LB.Iso M' (M.pull FB)) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (JL) (JL') (JM) (JM'), Good L z JL → Good L' z JL' → Good M z JM →
    Good M' z JM' →
    isoV a z JM JL (r ≫ F) * isoV w z JL JL' r = isoV v z JM JM' (r ≫ q') * isoV a' z JM' JL' r
def TriangleComm {Y B : Scheme.{0}} {L : LB Y} {M M' : LB B} {q : Y ⟶ B} (a : LB.Iso L (M.pull q))
    (a' : LB.Iso L (M'.pull q)) (v : LB.Iso M' (M.pull (𝟙 B))) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (JL) (JM) (JM'), Good L z JL → Good M z JM → Good M' z JM' →
    isoV a z JM JL r = isoV v z JM JM' (r ≫ q) * isoV a' z JM' JL r
def diagφ (w : G ⟶ G) : Fin 4 → (G.left ⟶ G.left) := ![(𝟙 G * w).left, 𝟙 G.left, w.left, (1 : G ⟶ G).left]
def diagε : Fin 4 → ℤ := ![1, -2, -1, 2]
structure IsDiagIso (P : CP G) (w : G ⟶ G) (u : LB.Gen (LB.LinComb P.L.L (diagφ w) diagε)) : Prop where
  gen : u.IsGen
  cub : ∀ (Z : Over S) (x y v : Z ⟶ G) (z : Z.left) (J), Good P.L.L z J →
    val u (x * y * v).left z J * val u x.left z J * val u y.left z J * val u v.left z J *
        cubV P.c z J x y v ^ 2 * cubV P.c z J (x ≫ w) (y ≫ w) (v ≫ w) =
      cubV P.c z J (x * (x ≫ w)) (y * (y ≫ w)) (v * (v ≫ w)) *
        val u (x * y).left z J * val u (x * v).left z J * val u (y * v).left z J
  even : ∀ (Z : Over S) (x : Z ⟶ G) (z : Z.left) (J), Good P.L.L z J →
    val u (x⁻¹).left z J * val P.sym x.left z J ^ 2 * val P.sym (x ≫ w).left z J =
      val P.sym (x * (x ≫ w)).left z J * val u x.left z J
def adjφ (a a' : G ⟶ G) : Fin 6 → ((G ⊗ G).left ⟶ G.left) :=
  ![((fst G G ≫ a) * snd G G).left, (fst G G ≫ a).left, (snd G G).left,
    (fst G G * (snd G G ≫ a')).left, (fst G G).left, (snd G G ≫ a').left]
def adjε : Fin 6 → ℤ := ![1, -1, -1, -1, 1, 1]
structure IsAdjIso {L : RigLB G} (c : CubicalStr G L) (a a' : G ⟶ G)
    (ρ : LB.Gen (LB.LinComb L.L (adjφ a a') adjε)) : Prop where
  gen : ρ.IsGen
  law1 : ∀ (Z : Over S) (x x' y : Z ⟶ G) (z : Z.left) (J), Good L.L z J →
    val ρ (lift (x * x') y).left z J * cubV c z J x x' (y ≫ a') =
      cubV c z J (x ≫ a) (x' ≫ a) y * val ρ (lift x y).left z J * val ρ (lift x' y).left z J
  law2 : ∀ (Z : Over S) (x y y' : Z ⟶ G) (z : Z.left) (J), Good L.L z J →
    val ρ (lift x (y * y')).left z J * cubV c z J x (y ≫ a') (y' ≫ a') =
      cubV c z J (x ≫ a) y y' * val ρ (lift x y).left z J * val ρ (lift x y').left z J
def IsBimul (G : Over S) [GrpObj G] (β : Γ((G ⊗ G).left, ⊤)ˣ) : Prop :=
  ∀ (Z : Over S) (x x' y : Z ⟶ G),
    (lift (x * x') y).left.appTop.hom β.val = (lift x y).left.appTop.hom β.val * (lift x' y).left.appTop.hom β.val ∧
    (lift y (x * x')).left.appTop.hom β.val = (lift y x).left.appTop.hom β.val * (lift y x').left.appTop.hom β.val
def IsWtBundle {G : Over S} [GrpObj G] (Q : TQ G X) (χ : X) (N : LB Q.B.left) (t : LB.Gen (N.pull Q.q.left)) : Prop :=
  N.IsLB ∧ Q.GenWt N t (-χ)
end Notions
def BiTrivExistsOver (S : Scheme.{0}) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over S) [GrpObj G] [IsCommMonObj G]
    (Q : TQ G X) (L : RigLB G) (c : CubicalStr G L), Nonempty (BiTriv c Q.i)
def BiTrivUniqueOver (S : Scheme.{0}) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over S) [GrpObj G] [IsCommMonObj G]
    (Q : TQ G X) (L : RigLB G) (c : CubicalStr G L) (s s' : BiTriv c Q.i), s = s'
def BiTrivLiftAlong {A : Type} [CommRing A] (J : Ideal A) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G]
    (G' : Over (Spec (CommRingCat.of (A ⧸ J)))) [GrpObj G'] [IsCommMonObj G']
    (F : G'.left ⟶ G.left) (hF : IsPullback F G'.hom G.hom (red J))
    (i : splitTorus _ X ⟶ G) (i' : splitTorus _ X ⟶ G'), IsMonHom i → IsMonHom i' → TorusCompat (red J) F i' i →
    ∀ (P : CP G) (P' : CP G') (w : LB.Iso P'.L.L (P.L.L.pull F)), IsCPMap P' P (red J) F hF.w w →
    ∀ s' : BiTriv P'.c i', ∃! s : BiTriv P.c i, BiRestricts (red J) w s s'
def BimulTrivialOver (S : Scheme.{0}) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over S) [GrpObj G] [IsCommMonObj G]
    (_ : TQ G X) (β : Γ((G ⊗ G).left, ⊤)ˣ), IsBimul G β → β = 1
def EvenTrivLiftAlong {A : Type} [CommRing A] (J : Ideal A) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G]
    (G' : Over (Spec (CommRingCat.of (A ⧸ J)))) [GrpObj G'] [IsCommMonObj G']
    (F : G'.left ⟶ G.left) (hF : IsPullback F G'.hom G.hom (red J))
    (i : splitTorus _ X ⟶ G) (i' : splitTorus _ X ⟶ G'), IsMonHom i → IsMonHom i' → TorusCompat (red J) F i' i →
    ∀ (P : CP G) (P' : CP G') (w : LB.Iso P'.L.L (P.L.L.pull F)), IsCPMap P' P (red J) F hF.w w →
    ∀ σ' : CubTriv P'.c i', σ'.Even →
      ∃ σ : CubTriv P.c i, σ.Even ∧ CubRestricts (red J) w σ σ' ∧
        ∀ τ : CubTriv P.c i, CubRestricts (red J) w τ σ' → τ = σ
def EvenTrivUniqueOver (S : Scheme.{0}) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over S) [GrpObj G] [IsCommMonObj G]
    (i : splitTorus S X ⟶ G), IsMonHom i → ∀ (P : CP G) (σ σ' : CubTriv P.c i), σ.Even → σ'.Even → σ = σ'
def EvenDefectOver (S : Scheme.{0}) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over S) [GrpObj G] [IsCommMonObj G]
    (i : splitTorus S X ⟶ G), IsMonHom i → ∀ (P : CP G) (σ : CubTriv P.c i),
    ∃! χ : X, (∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (z : Z.left) (J), Good P.L.L z J →
        val σ.s (t⁻¹).left z J =
          gm (𝟙 Z.left) z ⊤ (chV t χ) * val P.sym (t ≫ i).left z J * val σ.s t.left z J) ∧
      ((∃ τ : CubTriv P.c i, τ.Even) ↔ ∃ ψ : X, χ = ψ + ψ)
def EndPreservesTorusOver (S : Scheme.{0}) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over S) [GrpObj G] [IsCommMonObj G]
    (Q : TQ G X) (w : G ⟶ G), IsMonHom w → ∃ wT : splitTorus S X ⟶ splitTorus S X, wT ≫ Q.i = Q.i ≫ w
def DiagTrivOver (S : Scheme.{0}) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over S) [GrpObj G] [IsCommMonObj G]
    (Q : TQ G X) (P : CP G) (w : G ⟶ G), IsMonHom w → ∀ u, IsDiagIso P w u → ∀ s : BiTriv P.c Q.i,
    ∃ σ : CubTriv P.c Q.i, σ.Even ∧
      ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (z : Z.left) (J), Good P.L.L z J →
        val σ.s t.left z J * val u (t ≫ Q.i).left z J = val s.s (lift t (t ≫ Q.i ≫ w)).left z J
def DescExistsOver (S : Scheme.{0}) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over S) [GrpObj G] [IsCommMonObj G]
    (Q : TQ G X) (P : CP G) (s : BiTriv P.c Q.i) (σ : CubTriv P.c Q.i), σ.Even →
    ∃ D : Q.Desc P, IsEquivariant Q s σ D.M.L.L D.w
def DescUniqueOver (S : Scheme.{0}) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over S) [GrpObj G] [IsCommMonObj G]
    (Q : TQ G X) (P : CP G) (D D' : Q.Desc P),
    ∃ v : LB.Iso D'.M.L.L (D.M.L.L.pull (𝟙 _)), IsCPMap D'.M D.M (𝟙 S) (𝟙 _) (by simp) v ∧ TriangleComm D.w D'.w v ∧
      ∀ v' : LB.Iso D'.M.L.L (D.M.L.L.pull (𝟙 _)), v'.IsGen → TriangleComm D.w D'.w v' → v' = v
def EquivDescUniqueOver (S : Scheme.{0}) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over S) [GrpObj G] [IsCommMonObj G]
    (Q : TQ G X) (L : RigLB G) (c : CubicalStr G L) (s : BiTriv c Q.i) (σ : CubTriv c Q.i) (M M' : LB Q.B.left)
    (a : LB.Iso L.L (M.pull Q.q.left)) (a' : LB.Iso L.L (M'.pull Q.q.left)), M.IsLB → M'.IsLB → a.IsGen → a'.IsGen →
    IsEquivariant Q s σ M a → IsEquivariant Q s σ M' a' →
    ∃! v : LB.Iso M' (M.pull (𝟙 _)), v.IsGen ∧ TriangleComm a a' v
def DescRestrictsAlong {A : Type} [CommRing A] (J : Ideal A) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G]
    (G' : Over (Spec (CommRingCat.of (A ⧸ J)))) [GrpObj G'] [IsCommMonObj G']
    (F : G'.left ⟶ G.left) (hF : IsPullback F G'.hom G.hom (red J)) (Q : TQ G X) (Q' : TQ G' X),
    TorusCompat (red J) F Q'.i Q.i →
    ∀ (FB : Q'.B.left ⟶ Q.B.left) (hB : FB ≫ Q.B.hom = Q'.B.hom ≫ red J), F ≫ Q.q.left = Q'.q.left ≫ FB →
    ∀ (P : CP G) (P' : CP G') (w : LB.Iso P'.L.L (P.L.L.pull F)), IsCPMap P' P (red J) F hF.w w →
    ∀ (D : Q.Desc P) (D' : Q'.Desc P'),
      ∃! v : LB.Iso D'.M.L.L (D.M.L.L.pull FB), IsCPMap D'.M D.M (red J) FB hB v ∧ SquareComm w D.w D'.w v
def DescAdjOver (S : Scheme.{0}) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over S) [GrpObj G] [IsCommMonObj G]
    (Q : TQ G X) (P : CP G) (D : Q.Desc P) (a a' : G ⟶ G) (b b' : Q.B ⟶ Q.B),
    IsMonHom a → IsMonHom a' → IsMonHom b → IsMonHom b' → a ≫ Q.q = Q.q ≫ b → a' ≫ Q.q = Q.q ≫ b' →
    ∀ ρ ρB, IsAdjIso P.c a a' ρ → IsAdjIso D.M.c b b' ρB →
    ∀ (Z : Over S) (x y : Z ⟶ G) (z : Z.left) (J) (J'), Good D.M.L.L z J → Good P.L.L z J' →
      val ρB (lift (x ≫ Q.q) (y ≫ Q.q)).left z J * isoV D.w z J J' (x ≫ a).left * isoV D.w z J J' y.left *
          isoV D.w z J J' (x * (y ≫ a')).left =
        isoV D.w z J J' ((x ≫ a) * y).left * isoV D.w z J J' x.left * isoV D.w z J J' (y ≫ a').left *
          val ρ (lift x y).left z J'
def DescDiagOver (S : Scheme.{0}) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over S) [GrpObj G] [IsCommMonObj G]
    (Q : TQ G X) (P : CP G) (D : Q.Desc P) (w : G ⟶ G) (wB : Q.B ⟶ Q.B), IsMonHom w → IsMonHom wB →
    w ≫ Q.q = Q.q ≫ wB → ∀ u uB, IsDiagIso P w u → IsDiagIso D.M wB uB →
    ∀ (Z : Over S) (x : Z ⟶ G) (z : Z.left) (J) (J'), Good D.M.L.L z J → Good P.L.L z J' →
      val uB (x ≫ Q.q).left z J * isoV D.w z J J' x.left ^ 2 * isoV D.w z J J' (x ≫ w).left =
        isoV D.w z J J' (x * (x ≫ w)).left * isoV D.w z J J' (1 : Z ⟶ G).left ^ 2 * val u x.left z J'
def WtBundleOver (S : Scheme.{0}) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over S) [GrpObj G] [IsCommMonObj G]
    (Q : TQ G X) (χ : X),
    (∃ N t, IsWtBundle Q χ N t) ∧
    (∀ N t, IsWtBundle Q χ N t → ∀ (j : N.ι) (V : Q.B.left.Opens)
      (h : Q.q.left ⁻¹ᵁ V ≤ (N.pull Q.q.left).U (fun _ => j)) (u : Γ(G.left, Q.q.left ⁻¹ᵁ V)),
      IsWt Q.i _ u χ ↔ ∃! f : Γ(Q.B.left, V), (Q.q.left.app V).hom f = u * (res h (t.s fun _ => j)).val) ∧
    ∀ N t N' t', IsWtBundle Q χ N t → IsWtBundle Q χ N' t' →
      ∃! v : LB.Iso N' (N.pull (𝟙 _)), v.IsGen ∧
        ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J) (J'), Good N z J → Good N' z J' →
          val (φ := fun _ : PUnit => Q.q.left) (ε := fun _ => 1) t r z J =
            isoV v z J J' (r ≫ Q.q.left) * val (φ := fun _ : PUnit => Q.q.left) (ε := fun _ => 1) t' r z J'
structure Claims : Prop where
  biTriv_exists_field : ∀ (k : Type) [Field k], BiTrivExistsOver (Spec (CommRingCat.of k))
  biTriv_exists_thick : ∀ (A : Type) [CommRing A] [IsLocalRing A], IsNilpotent (IsLocalRing.maximalIdeal A) →
    BiTrivExistsOver (Spec (CommRingCat.of A))
  biTriv_unique : ∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J → IsReduced (A ⧸ J) →
    BiTrivUniqueOver (Spec (CommRingCat.of A))
  biTriv_lift : ∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J → BiTrivLiftAlong J
  bimul_trivial : ∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J → IsReduced (A ⧸ J) →
    BimulTrivialOver (Spec (CommRingCat.of A))
  evenTriv_lift : ∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J → EvenTrivLiftAlong J
  evenTriv_unique : ∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J → IsReduced (A ⧸ J) →
    EvenTrivUniqueOver (Spec (CommRingCat.of A))
  even_defect : ∀ (A : Type) [CommRing A] [IsLocalRing A], IsNilpotent (IsLocalRing.maximalIdeal A) →
    EvenDefectOver (Spec (CommRingCat.of A))
  end_preserves : ∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J → IsReduced (A ⧸ J) →
    EndPreservesTorusOver (Spec (CommRingCat.of A))
  diag_triv : ∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J → IsReduced (A ⧸ J) →
    DiagTrivOver (Spec (CommRingCat.of A))
  desc_exists : ∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J → IsReduced (A ⧸ J) →
    DescExistsOver (Spec (CommRingCat.of A))
  desc_unique : ∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J → IsReduced (A ⧸ J) →
    DescUniqueOver (Spec (CommRingCat.of A))
  equivDesc_unique : ∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J → IsReduced (A ⧸ J) →
    EquivDescUniqueOver (Spec (CommRingCat.of A))
  desc_restricts : ∀ (A : Type) [CommRing A] (J J' : Ideal A), IsNilpotent J' → IsReduced (A ⧸ J') → J ≤ J' →
    DescRestrictsAlong J
  desc_adj : ∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J → IsReduced (A ⧸ J) →
    DescAdjOver (Spec (CommRingCat.of A))
  desc_diag : ∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J → IsReduced (A ⧸ J) →
    DescDiagOver (Spec (CommRingCat.of A))
  wtBundle : ∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J → IsReduced (A ⧸ J) →
    WtBundleOver (Spec (CommRingCat.of A))
section Basic₂
variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]
example (w : G ⟶ G) : IsDiagIso (CP.triv G) w (unitGen _ _) := by
  have e : ∀ {Z : Scheme.{0}} (r : Z ⟶ G.left) z J,
      val (L := (CP.triv G).L.L) (unitGen (diagφ w) diagε) r z J = 1 := fun r z J => val_unitGen _ _ _ _ _
  have c : ∀ {Z : Over S} (z : Z.left) J (x y u : Z ⟶ G), cubV (CP.triv G).c z J x y u = 1 :=
    fun z J x y u => cubV_trivCub G z J x y u
  exact ⟨unitGen_isGen _ _, fun Z x y v z J _ => by simp only [e, c, one_pow, _root_.mul_one],
    fun Z x z J _ => by simp only [e, val_sym_triv, one_pow, _root_.mul_one]⟩
example (a a' : G ⟶ G) : IsAdjIso (trivCub G) a a' (unitGen _ _) := by
  have e : ∀ {Z : Scheme.{0}} (r : Z ⟶ (G ⊗ G).left) z J,
      val (L := (trivRig G).L) (unitGen (adjφ a a') adjε) r z J = 1 := fun r z J => val_unitGen _ _ _ _ _
  exact ⟨unitGen_isGen _ _, fun Z x y v z J _ => by simp only [e, cubV_trivCub, _root_.mul_one],
    fun Z x y v z J _ => by simp only [e, cubV_trivCub, _root_.mul_one]⟩
example {X : Type} [AddCommGroup X] (χ : X) :
    IsWtBundle (TQ.torus S X) χ (Inh.trivLB _) (scaleGen (charUnit S X (-χ)) (unitGen _ _)) :=
  ⟨Inh.trivLB_isLB _, (TQ.torus S X).genWt_triv _ (isWt_charUnit (-χ))⟩
end Basic₂
end GlobalTheory.IndefiniteRowSideFullHecke.CubicalBundleRestrictions
end


