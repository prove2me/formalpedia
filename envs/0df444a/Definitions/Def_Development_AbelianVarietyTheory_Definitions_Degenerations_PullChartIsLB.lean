-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
-- name    : Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:49:00.538428+00:00
-- url     : https://prove2.me/theorems/23cec3a9-3958-4f40-b45a-6c2abef0ef23
-- title:
--   Pull Chart Is LB
-- statement:
--   Definitions and structural lemmas for Pull Chart Is LB, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/PullChartIsLB.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
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
namespace GlobalTheory.ZH
export ReciprocityTheory.ChartRestriction.G.Geo.Tor (valR)
def Crd {X : Scheme.{0}} (H : LB X) {J : Type} (s : J → H.Sec) {R : Type} [CommRing R] (x : Sp R ⟶ X)
    (v : J → R) : Prop :=
  ∃ (l : H.ι) (c : Rˣ), ⊤ ≤ x ⁻¹ᵁ H.U l ∧ ∀ j, v j = (c : R) * valR x (H.U l) ((s j).f l)
def IsRatio {X : Scheme.{0}} {H : LB X} (s t : H.Sec) (W : X.Opens) (r : Γ(X, W)) : Prop :=
  ∀ l, resG X (inf_le_right : W ⊓ H.U l ≤ H.U l) (s.f l) =
    resG X (inf_le_left : W ⊓ H.U l ≤ W) r * resG X (inf_le_right : W ⊓ H.U l ≤ H.U l) (t.f l)
def IsLin {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) {H : LB X} {J : Type} [Fintype J]
    (s : J → H.Sec) (a : J → k) (φ : H.Sec) : Prop :=
  ∀ l, φ.f l = ∑ j, constFn p (H.U l) (a j) * (s j).f l
def ImmBy {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (H : LB X) {J : Type} (s : J → H.Sec)
    (J₀ : Set J) : Prop :=
  (⨆ i ∈ J₀, Out.nonzeroLocus (s i) = ⊤) ∧ ∀ i ∈ J₀, IsAffineOpen (Out.nonzeroLocus (s i)) ∧
    ∃ r : J → Γ(X, Out.nonzeroLocus (s i)), (∀ j, IsRatio (s j) (s i) _ (r j)) ∧
      Subring.closure (Set.range (constFn p (Out.nonzeroLocus (s i))) ∪ Set.range r) = ⊤
def cone {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (H : LB X) {J : Type} (s : J → H.Sec) :
    Set (J → k) := {v | ∃ x : Sp k ⟶ X, x ≫ p = 𝟙 _ ∧ Crd H s x v}
def npw {X : Scheme.{0}} (H : LB X) (d : ℕ) : LB X := ⟨H.ι, H.U, fun i j => H.g i j ^ d⟩
def Short {X : Type} [AddCommGroup X] (q : QuadraticMap ℤ X ℝ) (N : ℕ) (α : X) : Prop :=
  ∀ m : X, q α ≤ q (α + N • m)
def hilb {k J : Type} [Field k] [Finite J] (C : Set (J → k)) (d : ℕ) : ℕ :=
  Module.finrank k ((MvPolynomial.homogeneousSubmodule J k d).map
    (LinearMap.pi fun v : C => (MvPolynomial.aeval (R := k) v.1).toLinearMap))
attribute [local instance] SplitExt.free SplitExt.finite
structure FibPre (k : Type) [Field k] where
  E : SplitExt (Sp k)
  G : Over (Sp k)
  [grp : GrpObj G]
  [comm : IsCommMonObj G]
  D : E.GtDatum G
  N₀ : LB E.B.left
  isLB : N₀.IsLB
  aff : ∀ l, IsAffineOpen (N₀.U l)
  ch : N₀.ι → E.ChartIdx
  le : ∀ l, N₀.U l ≤ E.chart (ch l)
attribute [instance] FibPre.grp FibPre.comm
namespace FibPre
variable {k : Type} [Field k] (Φ : FibPre k)
def H (d : ℕ) : LB Φ.G.left :=
  ⟨Φ.N₀.ι, fun l => Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l, fun l l' => pullU Φ.D.q.left (Φ.N₀.U l ⊓ Φ.N₀.U l') (Φ.N₀.g l l') ^ d⟩
def wt {d : ℕ} (φ : (Φ.H d).Sec) (α : Φ.E.X) (l : Φ.N₀.ι) : Γ(Φ.E.B.left, Φ.N₀.U l) :=
  Φ.D.weight (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l) α (φ.f l)
def supp {d : ℕ} (φ : (Φ.H d).Sec) : Set Φ.E.X := {α | ∃ l, Φ.wt φ α l ≠ 0}
def Pure {d : ℕ} (α : Φ.E.X) (φ : (Φ.H d).Sec) : Prop := Φ.supp φ ⊆ {α}
def IsPart {d : ℕ} (α : Φ.E.X) (φ ψ : (Φ.H d).Sec) : Prop := Φ.Pure α ψ ∧ ∀ l, Φ.wt ψ α l = Φ.wt φ α l
abbrev Pt : Type := Out.baseOver (Sp k) ⟶ Φ.G
structure Pol (N : ℕ) where
  PB : Out.PolAV (Sp k)
  β : Φ.E.B ≅ PB.A
  hom : IsMonHom β.hom
  c : Φ.E.X → (Out.baseOver (Sp k) ⟶ PB.A)
  w₀ : LBIso Φ.N₀ ((lbPow PB.L N).pull β.hom.left)
  wO : ∀ α, LBIso (Φ.E.O α).L (LB.LinComb PB.L (K := Fin 2)
    ![(β.hom * (Over.homMk Φ.E.B.hom (Category.comp_id _) ≫ c α)).left, β.hom.left] ![1, -1])
structure Good (N : ℕ) (q : QuadraticMap ℤ Φ.E.X ℝ) {J : Type} [Fintype J] (cls : J → Φ.E.X)
    (F : J → (Φ.H 1).Sec) : Prop where
  pos : Filter.Tendsto q Filter.cofinite Filter.atTop
  short : ∀ i, Short q N (cls i)
  supp : ∀ i, ∀ β ∈ Φ.supp (F i), Short q N β ∧ ∃ m, β = cls i + N • m
  onto : ∀ α, Short q N α → ∀ φ : (Φ.H 1).Sec, Φ.Pure α φ → ∃ a : J → k,
    (∀ i, a i ≠ 0 → ∃ m, α = cls i + N • m) ∧
    ∀ l, Φ.wt φ α l = ∑ i, constFn Φ.E.B.hom _ (a i) * Φ.wt (F i) α l
  inj : ∀ α, Short q N α → ∀ a : J → k, (∀ i, a i ≠ 0 → ∃ m, α = cls i + N • m) →
    (∀ l, ∑ i, constFn Φ.E.B.hom _ (a i) * Φ.wt (F i) α l = 0) → a = 0
end FibPre
structure Big (g N N' : ℕ) : Prop where
  four : 4 ≤ N
  lll : 1 + 2 * (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2) < N
  sep : 2 * ((N ^ g * g.factorial : ℕ) : ℝ) * ((g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1)) * N < N'
example {R : Type} [CommRing R] (a : R) : valR (𝟙 (Sp R)) ⊤ (constFn (𝟙 (Sp R)) ⊤ a) = a := by
  have e : ∀ (h : (⊤ : (Sp R).Opens) ≤ ⊤) (x : Γ(Sp R, ⊤)), ((Sp R).presheaf.map (homOfLE h).op).hom x = x :=
    fun h x => congrArg (fun φ => CommRingCat.Hom.hom φ x) ((Sp R).presheaf.map_id _)
  simp only [valR, constFn, Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
  refine (dif_pos (fun _ _ => trivial)).trans ?_
  erw [e, e]
  exact (Scheme.ΓSpecIso (CommRingCat.of R)).inv_hom_id_apply a
example {k J : Type} [Field k] [Finite J] (d : ℕ) : hilb (∅ : Set (J → k)) d = 0 :=
  Module.finrank_zero_of_subsingleton
example {X : Type} [AddCommGroup X] (N : ℕ) (α : X) : Short (0 : QuadraticMap ℤ X ℝ) N α := fun _ => le_rfl
example (g N' : ℕ) : ¬ Big g 3 N' := fun h => absurd h.four (by norm_num)
end GlobalTheory.ZH
end


