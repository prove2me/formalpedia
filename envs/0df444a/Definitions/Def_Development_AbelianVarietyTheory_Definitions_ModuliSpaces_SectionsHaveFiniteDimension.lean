-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_SectionsHaveFiniteDimension
-- name    : Development_AbelianVarietyTheory_Definitions_ModuliSpaces_SectionsHaveFiniteDimension
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:14:54.825947+00:00
-- url     : https://prove2.me/theorems/b940a984-85ad-460e-996a-11e330e9ea52
-- title:
--   Sections Have Finite Dimension
-- statement:
--   Definitions and structural lemmas for Sections Have Finite Dimension, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ModuliSpaces/SectionsHaveFiniteDimension.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
namespace GlobalTheory.ZV
variable {K : Type} [Field K] {X Y : Scheme.{0}}
def SectionsHaveFiniteDimension (p : X ⟶ Sp K) (M : LB X) (r : ℕ) : Prop :=
  ∃ s : Fin r → M.Sec, ∀ t : M.Sec, ∃! a : Fin r → K, ∀ j, t.f j = ∑ i, constFn p _ (a i) * (s i).f j
def Vol (p : X ⟶ Sp K) (M : LB X) (g : ℕ) (δ : ℝ) : Prop :=
  ∃ h : ℕ → ℕ, (∀ e, SectionsHaveFiniteDimension p (lbPow M e) (h e)) ∧
    Filter.Tendsto (fun e : ℕ => (h e : ℝ) / (e : ℝ) ^ g) Filter.atTop (nhds δ)
def VAmp (p : X ⟶ Sp K) (M : LB X) {σ : Type} (th : σ → M.Sec) : Prop :=
  (⨆ i, Out.nonzeroLocus (th i) = ⊤) ∧ ∀ i, IsAffineOpen (Out.nonzeroLocus (th i)) ∧
    ∃ r : σ → Γ(X, Out.nonzeroLocus (th i)),
      (∀ j k, resG X (inf_le_right : Out.nonzeroLocus (th i) ⊓ M.U k ≤ M.U k) ((th j).f k) =
        resG X (inf_le_left : Out.nonzeroLocus (th i) ⊓ M.U k ≤ Out.nonzeroLocus (th i)) (r j) *
          resG X (inf_le_right : Out.nonzeroLocus (th i) ⊓ M.U k ≤ M.U k) ((th i).f k)) ∧
      ∀ f : Γ(X, Out.nonzeroLocus (th i)), ∃ F : MvPolynomial σ K,
        f = MvPolynomial.eval₂ (RingHom.comp (p.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) r F
def MapDeg (ψ : X ⟶ Y) (D : ℕ) : Prop :=
  ∀ U : Y.Opens, IsAffineOpen U → (U : Set Y).Nonempty →
    letI := (ψ.app U).hom.toAlgebra
    Module.rank Γ(Y, U) Γ(X, ψ ⁻¹ᵁ U) = (D : Cardinal)
def TorsBasis (A : Over (Sp K)) [GrpObj A] (k : ℕ) {m : ℕ} (pt : Fin m → (Out.baseOver (Sp K) ⟶ A)) : Prop :=
  0 < k ∧ (∀ i, pt i ^ k = 1) ∧ ∀ y : Out.baseOver (Sp K) ⟶ A, y ^ k = 1 →
    ∃! c : Fin m → ZMod k, Out.linComb pt (fun i => (c i).val) = y
def ActsBy {A : Over (Sp K)} [GrpObj A] {k m : ℕ} (pt : Fin m → (Out.baseOver (Sp K) ⟶ A)) (f : A ⟶ A)
    (Mat : Matrix (Fin m) (Fin m) (ZMod k)) : Prop :=
  0 < k ∧ ∀ i, pt i ≫ f = Out.linComb pt (fun i' => (Mat i' i).val)
def FormIs (P : Out.PolAV (Sp K)) (M : LB P.A.left) (s : P.A ⟶ P.A) : Prop :=
  IsMonHom s ∧ LBIso (abelian₂ P.A M) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ s] P.L)
def SymB {A : Over (Sp K)} [GrpObj A] (M : LB A.left) : Prop := LBIso M (M.pull (GrpObj.inv : A ⟶ A).left)
theorem SectionsHaveFiniteDimension.le {p : X ⟶ Sp K} {M : LB X} {r r' : ℕ} (h : SectionsHaveFiniteDimension p M r) (h' : SectionsHaveFiniteDimension p M r') : r ≤ r' := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨s', hs'⟩ := h'
  have hc : ∀ (U : X.Opens) (a : K), constFn p U a = AbLaw.cst p U a := fun _ _ => rfl
  choose B hB hBu using fun i => hs' (s i)
  let t : (Fin r → K) → M.Sec := fun a => ⟨fun j => ∑ i, AbLaw.cst p _ (a i) * (s i).f j, fun j k => by
    rw [map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, (s i).compat j k]
    erw [AbLaw.rs_cst, AbLaw.rs_cst]
    ring⟩
  have hinj : Function.Injective (Matrix.vecMulLinear (Matrix.of B)) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have h0 : ∀ j, (t a).f j = 0 := fun j => by
      change ∑ i, AbLaw.cst p _ (a i) * (s i).f j = 0
      have hB' : ∀ i, (s i).f j = ∑ k, AbLaw.cst p _ (B i k) * (s' k).f j := fun i => hB i j
      simp_rw [hB', Finset.mul_sum, ← _root_.mul_assoc, ← map_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [← Finset.sum_mul, ← map_sum]
      have : ∑ i, a i * B i k = 0 := congrFun ha k
      rw [this, map_zero, zero_mul]
    refine (hs (t a)).unique (fun j => rfl) fun j => ?_
    rw [h0]
    simp [hc]
  simpa using LinearMap.finrank_le_finrank_of_injective hinj
theorem SectionsHaveFiniteDimension.unique {p : X ⟶ Sp K} {M : LB X} {r r' : ℕ} (h : SectionsHaveFiniteDimension p M r) (h' : SectionsHaveFiniteDimension p M r') : r = r' :=
  le_antisymm (h.le h') (h'.le h)
theorem Vol.unique {p : X ⟶ Sp K} {M : LB X} {g : ℕ} {δ δ' : ℝ} (h : Vol p M g δ) (h' : Vol p M g δ') : δ = δ' := by
  obtain ⟨a, ha, ta⟩ := h
  obtain ⟨b, hb, tb⟩ := h'
  obtain rfl : a = b := funext fun e => (ha e).unique (hb e)
  exact tendsto_nhds_unique ta tb
theorem SectionsHaveFiniteDimension.one_of_isIso (p : X ⟶ Sp K) [IsIso p] {M : LB X} [Unique M.ι] (hU : M.U default = ⊤)
    (hg : ∀ i j, M.g i j = 1) : SectionsHaveFiniteDimension p M 1 := by
  have hb := AbLaw.cst_bijective p hU
  refine ⟨fun _ => ⟨fun _ => 1, fun i j => by rw [hg, map_one, map_one, Units.val_one, _root_.mul_one]⟩, fun t => ?_⟩
  obtain ⟨a, ha⟩ := hb.2 (t.f default)
  refine ⟨fun _ => a, fun j => ?_, fun b hb' => ?_⟩
  · obtain rfl : j = default := Subsingleton.elim _ _
    rw [Fin.sum_univ_one, _root_.mul_one]
    exact ha.symm
  · funext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    have := hb' default
    rw [Fin.sum_univ_one, _root_.mul_one] at this
    exact hb.1 (this.symm.trans ha.symm)
theorem SectionsHaveFiniteDimension.trivial_point (K : Type) [Field K] : SectionsHaveFiniteDimension (𝟙 (Sp K)) (Out.Inh.trivLB (Sp K)) 1 :=
  haveI : Unique (Out.Inh.trivLB (Sp K)).ι := inferInstanceAs (Unique PUnit)
  SectionsHaveFiniteDimension.one_of_isIso _ rfl fun _ _ => rfl
theorem Vol.trivial_point (K : Type) [Field K] : Vol (𝟙 (Sp K)) (Out.Inh.trivLB (Sp K)) 0 1 := by
  refine ⟨fun _ => 1, fun e => ?_, by simp⟩
  haveI : Unique (lbPow (Out.Inh.trivLB (Sp K)) e).ι := inferInstanceAs (Unique (PUnit → PUnit))
  exact SectionsHaveFiniteDimension.one_of_isIso _ (top_unique fun _ _ => Set.mem_iInter.2 fun _ => trivial)
    fun i j => Out.Inh.linComb_triv_g _ _ i j
example : ¬ SectionsHaveFiniteDimension (𝟙 (Sp ℚ)) (Out.Inh.trivLB (Sp ℚ)) 2 := fun h =>
  absurd (h.unique (SectionsHaveFiniteDimension.trivial_point ℚ)) (by decide)
example : ¬ Vol (𝟙 (Sp ℚ)) (Out.Inh.trivLB (Sp ℚ)) 0 0 := fun h =>
  zero_ne_one (h.unique (Vol.trivial_point ℚ))
example (p : X ⟶ Sp K) [Nonempty X] (M : LB X) (th : Empty → M.Sec) : ¬ VAmp p M th := fun h => by
  have hx : Classical.arbitrary X ∈ ⨆ i, Out.nonzeroLocus (th i) := by rw [h.1]; trivial
  obtain ⟨i, -⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  exact i.elim
section Torsion
variable {A : Over (Sp K)} [GrpObj A] {k m : ℕ} {pt : Fin m → (Out.baseOver (Sp K) ⟶ A)}
theorem TorsBasis.pos (h : TorsBasis A k pt) : 0 < k := h.1
theorem ActsBy.pos {f : A ⟶ A} {Mat : Matrix (Fin m) (Fin m) (ZMod k)} (h : ActsBy pt f Mat) : 0 < k := h.1
example (f : A ⟶ A) (Mat : Matrix (Fin m) (Fin m) (ZMod 0)) : ¬ ActsBy pt f Mat := fun h => lt_irrefl _ h.pos
end Torsion
end GlobalTheory.ZV
end


