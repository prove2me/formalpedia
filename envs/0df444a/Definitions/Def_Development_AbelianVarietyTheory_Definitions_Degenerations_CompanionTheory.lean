-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_CompanionTheory
-- name    : Development_AbelianVarietyTheory_Definitions_Degenerations_CompanionTheory
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:50:10.003221+00:00
-- url     : https://prove2.me/theorems/08412c95-8851-494b-bf3f-7e98f7528236
-- title:
--   Companion Theory
-- statement:
--   Definitions and structural lemmas for Companion Theory, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/CompanionTheory.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
namespace GlobalTheory.ZJ
abbrev Nrm {X : Scheme.{0}} (L : LB X) : Type :=
  ∀ (p : ℕ) [Fact p.Prime], (Sp (PadicAlgCl p) ⟶ X) → L.ι → ℝ
def IntAt {X Y : Scheme.{0}} (a : X ⟶ Y) (W : Set Y) {p : ℕ} [Fact p.Prime] (x : Sp (PadicAlgCl p) ⟶ X) : Prop :=
  ∃ b : Sp (OO p) ⟶ Y, gPt p ≫ b = x ≫ a ∧ b (cPt p) ∈ W
structure IsNrm {X : Scheme.{0}} (L : LB X) (ν : Nrm L) : Prop where
  pos : ∀ (p : ℕ) [Fact p.Prime] x j, 0 < ν p x j
  trans : ∀ (p : ℕ) [Fact p.Prime] (x : Sp (PadicAlgCl p) ⟶ X) i j, Set.range x ⊆ L.U i → Set.range x ⊆ L.U j →
    ‖valF x _ (L.g i j).val‖ * ν p x i = ν p x j
  int : ∀ (p : ℕ) [Fact p.Prime] (b : Sp (OO p) ⟶ X) j, b (cPt p) ∈ L.U j → ν p (gPt p ≫ b) j = 1
def NormOne {X Y : Scheme.{0}} {L : LB X} (ν : Nrm L) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) {p : ℕ} [Fact p.Prime] (x : Sp (PadicAlgCl p) ⟶ Y) : Prop :=
  ∀ J : K → L.ι, Set.range x ⊆ LB.wchart L φ J → ‖valF x _ (t.s J).val‖ * ∏ k, ν p (x ≫ φ k) (J k) ^ ε k = 1
namespace Core
variable (C : Core)
structure Theta where
  L : RigLB C.A
  cub : CubicalStr C.A L
  θ : LB.Sec L.L
  m : ℕ
  m_unit : IsUnit (m : Γ(C.Z, ⊤))
  O₁ : LB C.G.toScheme
  isLB : O₁.IsLB
  s : LB.Sec O₁
  w : LB.Iso (L.L.pull (mulN C.A m).left) (O₁.pull C.a)
  w_gen : w.IsGen
  w_sec : ∀ (x : C.A.left) (i : O₁.ι) (j : L.L.ι), C.a x ∈ O₁.U i → (mulN C.A m).left x ∈ L.L.U j →
    gs C.a x _ (s.f i) = gs (𝟙 _) x _ (w.s (fun _ => i, fun _ => j)).val * gs (mulN C.A m).left x _ (θ.f j)
  s_ne : ∀ z : C.Z, IsClosed ({z} : Set C.Z) → ∃ x ∈ Out.nonzeroLocus s, C.GG.hom x = z
variable {C}
structure Theta.Ext (T : C.Theta) {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ C.Z} (τ : C.Test y) where
  L : RigLB τ.H
  w : LB.Iso (T.L.L.pull τ.φ) (L.L.pull (pullback.fst τ.H.hom (Out.jK τ.V)))
  w_gen : w.IsGen
  θ : LB.Sec L.L
  θ_eq : ∀ (x : ↑(pullback τ.H.hom (Out.jK τ.V))) (i : L.L.ι) (j : T.L.L.ι),
    pullback.fst τ.H.hom (Out.jK τ.V) x ∈ L.L.U i → τ.φ x ∈ T.L.L.U j →
    gs (pullback.fst τ.H.hom (Out.jK τ.V)) x _ (θ.f i) =
      gs (𝟙 _) x _ (w.s (fun _ => i, fun _ => j)).val * gs τ.φ x _ (T.θ.f j)
  θ_ne : ∃ x ∈ Out.nonzeroLocus θ, τ.H.hom x = IsLocalRing.closedPoint τ.V
def Theta.Om (T : C.Theta) (L : C.Law) : Set C.G.toScheme :=
  letI := L.grp; (mulN C.GG T.m).left '' {x : C.G.toScheme | x ∈ Out.nonzeroLocus T.s}
def Theta.BTest (T : C.Theta) (L : C.Law) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z) (τ : C.Test y) (E : T.Ext τ) (x : τ.H.left),
    τ.H.hom x = IsLocalRing.closedPoint τ.V → (τ.f x ∈ T.Om L ↔ x ∈ Out.nonzeroLocus E.θ)
def TorsSec (C : Core) (n : ℕ) : Prop :=
  ∀ z : C.Z, IsClosed ({z} : Set C.Z) → ∃ N : C.Z.Opens, z ∈ N ∧
    ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z) (τ : C.Test y) (x : Sp (kb p) ⟶ N.toScheme)
      (c : Over.mk (rPt p ≫ spMap τ.j) ⟶ τ.H), y (cPt p) = z → x ≫ N.ι = rPt p ≫ y → c ^ n = 1 →
      ∃ h : N.toScheme ⟶ C.G.toScheme, h ≫ C.GG.hom = N.ι ∧ x ≫ h = c.left ≫ τ.f
def Theta.Few (T : C.Theta) (n : ℕ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z) (τ : C.Test y) (E : T.Ext τ) (c : Over.mk (rPt p ≫ spMap τ.j) ⟶ τ.H),
    6 * Nat.card {h : Over.mk (rPt p ≫ spMap τ.j) ⟶ τ.H // h ^ n = 1 ∧ ¬ ⊤ ≤ (c * h).left ⁻¹ᵁ Out.nonzeroLocus E.θ} <
      Nat.card {h : Over.mk (rPt p ≫ spMap τ.j) ⟶ τ.H // h ^ n = 1}
structure Theta.Norms (T : C.Theta) (Om : Set C.G.toScheme) (ν : Nrm T.L.L) : Prop where
  isNrm : IsNrm T.L.L ν
  rig : ∀ (p : ℕ) [Fact p.Prime] (x : Sp (PadicAlgCl p) ⟶ C.U.toScheme), IntAt C.U.ι Set.univ x → NormOne ν T.L.rig x
  cube : ∀ (p : ℕ) [Fact p.Prime] (x : Sp (PadicAlgCl p) ⟶ (G3 C.A).left),
    (∀ k, IntAt C.a Set.univ (x ≫ (x3 C.A k).left)) → NormOne (φ := thφ C.A (x3 C.A)) (ε := thε) ν T.cub.t x
  theta : ∀ (p : ℕ) [Fact p.Prime] (y : Sp (PadicAlgCl p) ⟶ C.U.toScheme), ∃ δ : ℝ, 0 < δ ∧
    ∀ (x : Sp (PadicAlgCl p) ⟶ C.A.left) (j : T.L.L.ι), x ≫ C.A.hom = y → Set.range x ⊆ T.L.L.U j →
      IntAt C.a Set.univ x → ‖valF x _ (T.θ.f j)‖ * ν p x j ≤ δ ∧ (‖valF x _ (T.θ.f j)‖ * ν p x j = δ ↔ IntAt C.a Om x)
def Law.CompanionTheory (L : C.Law) (Om : Set C.G.toScheme) : Prop :=
  letI := L.grp
  ∀ w : C.G.toScheme, IsClosed ({w} : Set C.G.toScheme) → ∃ (N : C.Z.Opens) (b c : Over.mk N.ι ⟶ C.GG),
    ∃ (K : Type) (_ : Field K) (t : Sp K ⟶ N.toScheme) (x b' c' : Over.mk (t ≫ N.ι) ⟶ C.GG),
      Set.range x.left = {w} ∧ b'.left = t ≫ b.left ∧ c'.left = t ≫ c.left ∧
      ∀ v ∈ [b', c', b' * c', x * b', x * c', x * b' * c'], Set.range v.left ⊆ Om
end Core
end GlobalTheory.ZJ
end


