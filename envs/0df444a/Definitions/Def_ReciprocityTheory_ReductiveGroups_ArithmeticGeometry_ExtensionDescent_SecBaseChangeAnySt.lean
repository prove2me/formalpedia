-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:57:47.680399+00:00
-- url     : https://prove2.me/theorems/3cea856f-d70b-4f5e-8228-9f2fd3719a13
-- title:
--   Sec Base Change Any St
-- statement:
--   Definitions and structural lemmas for Sec Base Change Any St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/SecBaseChangeAnySt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.Out
open Semi
def SecBaseChangeAnySt : Prop :=
  ∀ (S : Scheme.{0}) (P : PolAV S) (n : ℕ), 1 ≤ n →
    ∀ p : S, ∃ V : S.Opens, p ∈ V ∧ ∃ b : Fin (n ^ P.g) → LB.Sec (LPow P.A P.L n (overRes (T := baseOver S) V)),
      ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver S) V).left)
        (b' : Fin (n ^ P.g) → LB.Sec (LPow P.A P.L n (baseAt t))),
        (∀ i, IsPullSec P.A P.L n (homAt t ▷ P.A) (whiskerRight_snd (homAt t) P.A) (b i) (b' i)) →
        LinearIndependent Γ((baseAt t).left, ⊤)
            (fun i => (SecM.ofSec P.A (b' i) : SecM P.A P.L n (baseAt t))) ∧
          Submodule.span Γ((baseAt t).left, ⊤)
            (Set.range fun i => (SecM.ofSec P.A (b' i) : SecM P.A P.L n (baseAt t))) = ⊤
def twistLB {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (q : ℕ) {T : Over S}
    (c : T ⟶ A) : LB (T ⊗ A).left :=
  LB.LinComb L (K := Fin 2) ![(snd T A).left, (translPt A c).left] ![(q : ℤ) - 1, 1]
def IsSecBasis {S : Scheme.{0}} {A : Over S} {T : Over S} (N : LB (T ⊗ A).left) {m : ℕ}
    (b : Fin m → LB.Sec N) : Prop :=
  ∀ s : LB.Sec N, ∃! r : Fin m → Γ(T.left, ⊤), ∀ j,
    s.f j = ∑ i, ((T ⊗ A).left.presheaf.map (homOfLE le_top).op).hom
      ((fst T A).left.appTop.hom (r i)) * (b i).f j
theorem wchart_comp_le {X Y Y' : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (h : Y' ⟶ Y) (j : K → L.ι) : LB.wchart L (fun k => h ≫ φ k) j ≤ h ⁻¹ᵁ LB.wchart L φ j := by
  intro y hy
  have hy' := Set.mem_iInter.1 hy
  show h.base y ∈ (⋂ k, (φ k).base ⁻¹' (L.U (j k) : Set X))
  exact Set.mem_iInter.2 fun k => by simpa [Scheme.Hom.comp_base] using hy' k
def IsPullSecLC {X Y Y' : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (h : Y' ⟶ Y) (s : LB.Sec (LB.LinComb L φ ε)) (s' : LB.Sec (LB.LinComb L (fun k => h ≫ φ k) ε)) :
    Prop :=
  ∀ j, s'.f j = (Y'.presheaf.map (homOfLE (wchart_comp_le L φ h j)).op).hom ((h.app _).hom (s.f j))
def SecTwistSt : Prop :=
  ∀ (S : Scheme.{0}) (P : PolAV S) (q : ℕ), 1 ≤ q →
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (t : Spec (CommRingCat.of R) ⟶ S)
      (c : Over.mk t ⟶ P.A),
      (∃ b : Fin (q ^ P.g) → LB.Sec (twistLB P.A P.L q c), IsSecBasis _ b) ∧
      ∀ sbar : LB.Sec (LB.LinComb P.L (K := Fin 2)
          (fun k => ((Over.homMk (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) rfl :
            Over.mk (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ t) ⟶ Over.mk t) ▷ P.A).left ≫
              ![(snd (Over.mk t) P.A).left, (translPt P.A c).left] k) ![(q : ℤ) - 1, 1]),
        ∃ s : LB.Sec (twistLB P.A P.L q c), IsPullSecLC P.L _ _ _ s sbar
def CharPairSt : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (N : ℕ), (N : K) ≠ 0 →
    ∀ χ : {x : baseOver (Spec (CommRingCat.of K)) ⟶ P.A // x ^ N = 1} →
        Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)ˣ,
      (∀ x y, χ ⟨x.1 * y.1, by rw [mul_pow, x.2, y.2, _root_.one_mul]⟩ = χ x * χ y) →
      ∃! b : baseOver (Spec (CommRingCat.of K)) ⟶ P.A, b ^ N = 1 ∧
        ∀ x, WeilIs P.A P.L N x.1 b (χ x)
def SmoothDenseSt : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)),
    IsReduced X → LocallyOfFiniteType f →
    Dense {x : X | ∃ U : X.Opens, x ∈ U ∧ Smooth (U.ι ≫ f)}
structure Laws2 : Prop where
  secBaseChangeAny : SecBaseChangeAnySt
  secTwist : SecTwistSt
  charPair : CharPairSt
  smoothDense : SmoothDenseSt
end ReciprocityTheory.ChartRestriction.G.Out


