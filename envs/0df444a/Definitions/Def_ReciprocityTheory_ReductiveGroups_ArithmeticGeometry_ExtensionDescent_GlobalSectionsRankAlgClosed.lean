-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:53:22.412687+00:00
-- url     : https://prove2.me/theorems/78a1c336-cd6f-4655-8012-e40ce527fb71
-- title:
--   Global Sections Rank Alg Closed
-- statement:
--   Definitions and structural lemmas for Global Sections Rank Alg Closed, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/GlobalSectionsRankAlgClosed.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.Out
open Semi
def GlobalSectionsRankAlgClosed : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (P : PolAV (Spec (CommRingCat.of k))) (n : ℕ), 1 ≤ n →
    Module.finrank Γ((baseOver (Spec (CommRingCat.of k))).left, ⊤)
      (SecM P.A P.L n (baseOver (Spec (CommRingCat.of k)))) = n ^ P.g
abbrev baseAt {S : Scheme.{0}} {V : S.Opens} {R : Type} [CommRing R]
    (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver S) V).left) : Over S :=
  Over.mk (t ≫ (overRes (T := baseOver S) V).hom)
def homAt {S : Scheme.{0}} {V : S.Opens} {R : Type} [CommRing R]
    (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver S) V).left) :
    baseAt t ⟶ overRes (T := baseOver S) V := Over.homMk t rfl
def SecBaseChangeSt : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n →
    ∀ p : S, ∃ V : S.Opens, p ∈ V ∧ ∃ b : Fin (n ^ P.g) → LB.Sec (LPow P.A P.L n (overRes (T := baseOver S) V)),
      ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver S) V).left)
        (b' : Fin (n ^ P.g) → LB.Sec (LPow P.A P.L n (baseAt t))),
        (∀ i, IsPullSec P.A P.L n (homAt t ▷ P.A) (whiskerRight_snd (homAt t) P.A) (b i) (b' i)) →
        LinearIndependent Γ((baseAt t).left, ⊤)
            (fun i => (SecM.ofSec P.A (b' i) : SecM P.A P.L n (baseAt t))) ∧
          Submodule.span Γ((baseAt t).left, ⊤)
            (Set.range fun i => (SecM.ofSec P.A (b' i) : SecM P.A P.L n (baseAt t))) = ⊤
def VeryAmpleAt {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (N : ℕ) : Prop :=
  ∀ U : S.Opens, IsAffineOpen U →
    ∃ M : ℕ, ∃ s : Fin (M + 1) → LB.Sec (powOver A L U N),
      (⨆ i, nonzeroLocus (s i) = ⊤) ∧
      ∀ i, IsAffineOpen (nonzeroLocus (s i)) ∧
        ∃ r : Fin (M + 1) → Γ((A.hom ⁻¹ᵁ U).toScheme, nonzeroLocus (s i)),
          (∀ j k, ((A.hom ⁻¹ᵁ U).toScheme.presheaf.map (homOfLE (inf_le_right :
              nonzeroLocus (s i) ⊓ (powOver A L U N).U k ≤ (powOver A L U N).U k)).op).hom
                ((s j).f k) =
            ((A.hom ⁻¹ᵁ U).toScheme.presheaf.map (homOfLE (inf_le_left :
              nonzeroLocus (s i) ⊓ (powOver A L U N).U k ≤ nonzeroLocus (s i))).op).hom (r j) *
            ((A.hom ⁻¹ᵁ U).toScheme.presheaf.map (homOfLE (inf_le_right :
              nonzeroLocus (s i) ⊓ (powOver A L U N).U k ≤ (powOver A L U N).U k)).op).hom
                ((s i).f k)) ∧
          Function.Surjective (MvPolynomial.eval₂Hom
            ((A.hom ∣_ U).appLE ⊤ (nonzeroLocus (s i)) le_top).hom r)
def GeneratedAt {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (N : ℕ) : Prop :=
  ∀ U : S.Opens, IsAffineOpen U →
    ∃ M : ℕ, ∃ s : Fin (M + 1) → LB.Sec (powOver A L U N), ⨆ i, nonzeroLocus (s i) = ⊤
def AmpleSt : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 4 ≤ n →
    GeneratedAt P.A P.L n ∧ VeryAmpleAt P.A P.L n
def KerPowSt : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (N : ℕ), 1 ≤ N →
    ∀ (T : Over S) (x : T ⟶ P.A),
    (∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
      ∃ c : LB.Gen ((thetaLB P.A P.L N x).pull ((fst T P.A).left ⁻¹ᵁ V).ι), c.IsGen) ↔
    x ^ N = 1
def MulPullSt : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ),
    ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, (mulA P.A n).left] ![(n : ℤ) ^ 2, -1]),
      α.IsGen
def MulNSt : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n →
    IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧
    (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ S), (n : k) ≠ 0 →
      Nat.card {x : Over.mk t ⟶ P.A // x ^ n = 1} = n ^ (2 * P.g)
def CubeSt : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (L : RigLB P.A), L.L = P.L →
    Nonempty (CubicalStr P.A L) ∧
    ∀ c c' : CubicalStr P.A L, LB.Gen.Corr L.L _ _ _ _ c.t c'.t
def SquareSt : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (T : Over S) (x y : T ⟶ P.A) (p : T.left),
    ∃ V : T.left.Opens, p ∈ V ∧
      ∃ c : LB.Gen ((LB.LinComb P.L (K := Fin 4)
          ![(translPt P.A (x * y)).left, (snd T P.A).left, (translPt P.A x).left,
            (translPt P.A y).left] ![1, 1, -1, -1]).pull ((fst T P.A).left ⁻¹ᵁ V).ι), c.IsGen
def RigiditySt : Prop :=
  ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B], IsAbelianScheme A → IsAbelianScheme B →
    ∀ f : A ⟶ B, η[A] ≫ f = η[B] → IsMonHom f
def WeilSt : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ) (T : Over S),
    (∀ x y : T ⟶ P.A, x ^ k = 1 → y ^ k = 1 → ∃! c : Γ(T.left, ⊤)ˣ, WeilIs P.A P.L k x y c) ∧
    (∀ (x x' y : T ⟶ P.A) (c c' : Γ(T.left, ⊤)ˣ),
      WeilIs P.A P.L k x y c → WeilIs P.A P.L k x' y c' → WeilIs P.A P.L k (x * x') y (c * c')) ∧
    (∀ x : T ⟶ P.A, x ^ k = 1 → WeilIs P.A P.L k x x 1) ∧
    (∀ (l : ℕ) (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), IsUnit ((k * l : ℕ) : Γ(T.left, ⊤)) →
      x ^ (k * l) = 1 → y ^ k = 1 →
      (WeilIs P.A P.L (k * l) x y c ↔ WeilIs P.A P.L k (x ^ l) y c))
def WeilNondegSt : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (k : ℕ), (k : K) ≠ 0 →
    ∀ x : baseOver _ ⟶ P.A, x ^ k = 1 →
      (∀ y : baseOver _ ⟶ P.A, y ^ k = 1 → WeilIs P.A P.L k x y 1) → x = 1
def SymLiftSt : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ), Odd k → IsUnit (k : Γ(S, ⊤)) →
    ∀ (T : Over S) (x : T ⟶ P.A), x ^ k = 1 →
      (∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
        ∃ θ : ThetaGrp P.A P.L k (overRes V), SymLift P.A P.L k k (overResι V ≫ x) θ) ∧
      ∀ θ θ' : ThetaGrp P.A P.L k T, SymLift P.A P.L k k x θ → SymLift P.A P.L k k x θ' →
        LB.Gen.Corr P.L _ _ _ _ θ.φ θ'.φ
def IrredSt : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (k : ℕ),
    (k = 1 ∨ 4 ≤ k) → (k : K) ≠ 0 →
    ∀ W : Submodule Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)
        (SecM P.A P.L k (baseOver (Spec (CommRingCat.of K)))),
      (∀ (θ : ThetaGrp P.A P.L k (baseOver _)) (s s' : LB.Sec (LPow P.A P.L k (baseOver _))),
        IsActOf P.A P.L k θ s s' → SecM.ofSec P.A s ∈ W → SecM.ofSec P.A s' ∈ W) →
      W = ⊥ ∨ W = ⊤
def GoodPtSt : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n : ℕ), 2 ≤ n →
    (n : K) ≠ 0 → ∀ (th : LB.Sec (LPow P.A P.L 1 (baseOver _))), SecM.ofSec P.A th ≠ 0 →
    ∀ a : baseOver _ ⟶ P.A, ∃ x : baseOver _ ⟶ P.A, x ^ n = 1 ∧
      ∃ (τ : LB.Gen (LB.LinComb P.L (Y := (baseOver _).left) (K := Fin 1)
          (fun _ => (a * x).left) (fun _ => 1))) (v : Γ((baseOver _).left, ⊤)),
        τ.IsGen ∧ IsValueAt P.A P.L 1 th (a * x) τ v ∧ v ≠ 0
def SerreSt : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (M : ℕ), 3 ≤ M → ∀ σ : P.A ≅ P.A, IsMonHom σ.hom →
    (∀ p : S, ∃ V : S.Opens, p ∈ V ∧
      ∃ c : LB.Gen ((LB.LinComb P.L (K := Fin 2) ![σ.hom.left, 𝟙 P.A.left] ![1, -1]).pull
        (P.A.hom ⁻¹ᵁ V).ι), c.IsGen) →
    (∀ (T : Over S) (x : T ⟶ P.A), x ^ M = 1 → x ≫ σ.hom = x) → σ.hom = 𝟙 P.A
def GlobalFnsSt : Prop :=
  ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A →
    Function.Bijective A.hom.appTop.hom
def toBase {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} {g : A'.left ⟶ A.left}
    (hw : g ≫ A.hom = A'.hom ≫ f) {T : Over S'} (x : T ⟶ A') : Over.mk (T.hom ≫ f) ⟶ A :=
  Over.homMk (x.left ≫ g) (by
    show (x.left ≫ g) ≫ A.hom = T.hom ≫ f
    rw [Category.assoc, hw, ← Category.assoc, Over.w x])
def PolBaseChangeSt : Prop :=
  ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (P : PolAV S), ∃ (P' : PolAV S') (g : P'.A.left ⟶ P.A.left)
    (hg : IsPullback g P'.A.hom P.A.hom f), P'.g = P.g ∧
    (∀ (T : Over S') (x y : T ⟶ P'.A), toBase hg.w (x * y) = toBase hg.w x * toBase hg.w y) ∧
    ∃ t : LB.Iso (P.L.pull g) P'.L, t.IsGen
def QuotientSt : Prop :=
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : PolAV (Spec (CommRingCat.of R)))
    (H : Over (Spec (CommRingCat.of R))) [GrpObj H] (i : H ⟶ P.A),
    IsMonHom i → Mono i → IsFinite H.hom → Flat H.hom →
    ∃ (A' : Over (Spec (CommRingCat.of R))) (_ : GrpObj A'), IsAbelianScheme A' ∧
      ∃ q : P.A ⟶ A', IsMonHom q ∧ IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧
        IsPullback i (toUnit H) q η[A']
def UnramExtSt : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (k' : Type) [Field k']
    [Algebra (IsLocalRing.ResidueField V) k'] [FiniteDimensional (IsLocalRing.ResidueField V) k']
    [Algebra.IsSeparable (IsLocalRing.ResidueField V) k'],
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal W) W) (_ : Algebra V W),
      Module.Finite V W ∧ Function.Injective (algebraMap V W) ∧ IsLocalHom (algebraMap V W) ∧
      Algebra.FormallyUnramified V W ∧
      ∃ e : IsLocalRing.ResidueField W ≃+* k', ∀ v : V,
        e (IsLocalRing.residue W (algebraMap V W v)) =
          algebraMap (IsLocalRing.ResidueField V) k' (IsLocalRing.residue V v)
structure Laws : Prop where
  globalSectionsRank : GlobalSectionsRankAlgClosed
  secBaseChange : SecBaseChangeSt
  ample : AmpleSt
  kerPow : KerPowSt
  mulPull : MulPullSt
  mulN : MulNSt
  cube : CubeSt
  square : SquareSt
  rigidity : RigiditySt
  weil : WeilSt
  weilNondeg : WeilNondegSt
  symLift : SymLiftSt
  irred : IrredSt
  goodPt : GoodPtSt
  serre : SerreSt
  extend : Semi.extend_existsSt.{0}
  cubicalExtends : Semi.cubical_extendsSt.{0}
  lemmaB : Semi.lemmaBSt.{0}
  evVal : ∀ S : Scheme.{0}, EvValSt (S := S)
  vvRank : ∀ S : Scheme.{0}, VVRankSt (S := S)
  globalFns : GlobalFnsSt
  polBaseChange : PolBaseChangeSt
  quotient : QuotientSt
  unramExt : UnramExtSt
end ReciprocityTheory.ChartRestriction.G.Out


