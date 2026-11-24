-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FlagSectionNeZero
-- name    : GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FlagSectionNeZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:27.273622+00:00
-- url     : https://prove2.me/theorems/9d07e0de-0d5c-4c04-86b3-affad0815fcb
-- title:
--   Flag Section Ne Zero
-- statement:
--   Definitions and structural lemmas for Flag Section Ne Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FlagSectionNeZero.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_DetLineSmooth
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isArithVar_bot_4411830e09a7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isQuotRows_noRows_069a8b58390d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine
open MvPolynomial Filter Topology Matrix ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
namespace ComponentData
variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
def CuspBundlePos (D : ComponentData Ψ K ι) : Prop :=
  ∀ B : ℕ, 4 * D.f + 2 ≤ B → ∀ eps t' : ℝ, 0 < eps → eps ≤ 1 → 0 < t' → t' ≤ 1 →
    (D.MU B eps t').IsSemipos D.P ∧ (D.MU B eps t').IsNefFibres D.P ∧ (D.MU B eps t').IsAmpleGen D.P
def HtInterior (D : ComponentData Ψ K ι) (II : IntersectionSystem) (Ch : ℝ) : Prop :=
  ∀ B : ℕ, 4 * D.f * D.N ^ 2 ≤ B → ∀ eps t' : ℝ, 0 < eps → eps ≤ 1 → 0 < t' → t' ≤ 1 →
    ∀ W, IsAlgPt D.P W → ¬ OnBd D.Bd W →
      -Ch * D.f * D.jp * D.abelian₂ B - eps * D.Kamp ≤ (D.MU B eps t').ht II W
def HtBoundary (D : ComponentData Ψ K ι) (II : IntersectionSystem) (Ch : ℝ) : Prop :=
  ∀ B : ℕ, 4 * D.f * D.N ^ 2 ≤ B → ∀ eps t' : ℝ, 0 < eps → eps ≤ 1 → 0 < t' → t' ≤ 1 →
    ∀ W, IsAlgPt D.P W → OnBd D.Bd W →
      -Ch * D.f * D.jp * D.abelian₂ B - eps * D.Kamp ≤ (D.MU B eps t').ht II W
def CuspMean (D : ComponentData Ψ K ι) (Cu : ℝ) : Prop :=
  1 ≤ D.jp → 3 * D.jp + 1 ≤ D.N → ∀ B : ℕ, 4 * D.f * D.N ^ 2 ≤ B → D.meanU ≤ Cu * D.f * D.jp * D.abelian₂ B
end ComponentData
open ComponentData
def ZhangLowerX.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (D : ComponentData Ψ K ι) (II : IntersectionSystem) (A : RLine ι) (e : ℝ),
    IsIntersectionSystem II → A.IsSemipos D.P → A.IsNefFibres D.P → A.IsAmpleGen D.P → A.IsConjInv →
    (∀ W, IsAlgPt D.P W → e ≤ A.ht II W) →
    ((D.n + 1 : ℕ) : ℝ) * e * A.geomDeg D.P D.n ≤ A.top II D.P (D.n + 1)
def DimX.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (D : ComponentData Ψ K ι),
    ringKrullDim (MRingOver ℚ ι ⧸ Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) D.P) =
      ((D.n + Fintype.card K : ℕ) : WithBot ℕ∞)
def StokesLimit.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (D : ComponentData Ψ K ι) (II : IntersectionSystem),
    D.Clauses → IsIntersectionSystem II → D.KBound II →
    ∀ B : ℕ, 4 * D.f + 2 ≤ B → ∀ a : ℝ,
      (∀ eps t' : ℝ, 0 < eps → eps ≤ 1 → 0 < t' → t' ≤ 1 →
        ((D.n + 1 : ℕ) : ℝ) * (a - eps * D.Kamp) * (D.MU B eps t').geomDeg D.P D.n ≤
          (D.MU B eps t').top II D.P (D.n + 1)) →
      ((D.n + 1 : ℕ) : ℝ) * (a - D.meanU / 2) * D.degMu ≤ D.arLim II B
def PushDown.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (D : ComponentData Ψ K ι) (II : IntersectionSystem),
    D.Clauses → IsIntersectionSystem II → ∀ B : ℕ,
      D.PPB II B = ((cf D.n : ℚ) : ℝ) * (D.fdeg' : ℝ) * D.arLim II B ∧
      (∃ vol : ℝ, 0 < vol ∧ ((cf D.n : ℚ) : ℝ) * (D.fdeg' : ℝ) * D.degMu = vol * (D.J' : ℝ)) ∧
      0 < D.degMu
def GrassmannianHeightZTwo.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (hj : j ≤ N) (II : IntersectionSystem) (e : ℝ),
    IsIntersectionSystem II → 2 ≤ N → 1 ≤ j → j < N →
    0 < Jint (Ψ := Ψ) j hj (Fintype.card Ψ * j * (N - j)) →
    (∀ Z : Matrix (Fin (N - j)) (Fin j) ℂ, (∀ a b, ‖Z a b‖ = 1) → (1 / 2) * Real.log ((1 + Z * Zᴴ).det.re) ≤ e) →
    hFl II (FA (Ψ := Ψ) j hj (Fintype.card Ψ * j * (N - j))) ≤
      ((Fintype.card Ψ * j * (N - j) + 1 : ℕ) : ℝ) * (Jint (Ψ := Ψ) j hj (Fintype.card Ψ * j * (N - j)) : ℝ) *
        (Fintype.card Ψ : ℝ) * e
def LowerBoundComponent.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (D : ComponentData Ψ K ι) (II : IntersectionSystem) (Ch Cu : ℝ) (B : ℕ),
    D.Clauses → IsIntersectionSystem II → D.KBound II →
    ZhangLowerX.Statement → DimX.Statement → D.CuspBundlePos → D.HtInterior II Ch → D.HtBoundary II Ch →
    StokesLimit.Statement → D.CuspMean Cu → PushDown.Statement → GrassmannianHeightZTwo.Statement →
    1 ≤ D.jp → 3 * D.jp + 1 ≤ D.N → 4 * D.f * D.N ^ 2 ≤ B → 4 * D.f + 2 ≤ B →
    ∀ vol : ℝ, ((cf D.n : ℚ) : ℝ) * (D.fdeg' : ℝ) * D.degMu = vol * (D.J' : ℝ) →
      -(Ch + Cu / 2) * D.f * D.jp * D.abelian₂ B ≤ D.PPB II B / (((D.n + 1 : ℕ) : ℝ) * vol * (D.J' : ℝ))
section Example
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (GlobalTheory isArithVar_bot noRows isQuotRows_noRows)
abbrev ιE : Unit → Type := GlobalTheory 2
theorem isMultiHomog_zero' (d : Unit → ℕ) : IsMultiHomog (0 : MRing ιE) d := by
  intro m hm
  simp at hm
theorem isMultiHomog_one' : IsMultiHomog (1 : MRing ιE) 0 := by
  intro m hm k
  rw [support_one, Finset.mem_singleton] at hm
  subst hm
  simp
theorem isMultiHomog_Xpow (i : Fin 2) (e : ℕ) : IsMultiHomog ((X ⟨(), i⟩ : MRing ιE) ^ e) (fun _ => e) := by
  intro m hm k
  rw [support_X_pow, Finset.mem_singleton] at hm
  subst hm
  cases k
  rw [Fin.sum_univ_two]
  fin_cases i <;> simp
theorem X_notMem_bot (i : Fin 2) : (X ⟨(), i⟩ : MRing ιE) ∉ (⊥ : Ideal (MRing ιE)) := by
  rw [Ideal.mem_bot]
  exact X_ne_zero _
theorem cls_ne_zero {f : MRing ιE} (hf : f ≠ 0) : cls ⊥ f ≠ 0 := by
  intro h
  apply hf
  have h' := IsFractionRing.injective (MRing ιE ⧸ (⊥ : Ideal (MRing ιE))) (FnField (⊥ : Ideal (MRing ιE)))
    (h.trans (map_zero _).symm)
  rwa [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot] at h'
def y0E : FnField (⊥ : Ideal (MRing ιE)) := cls ⊥ (X ⟨(), 0⟩)
theorem flagSection_ne_zero : y0E ≠ 0 := cls_ne_zero (X_ne_zero _)
theorem isHomogOf_y0E : IsHomogOf ⊥ y0E (fun _ => 1) :=
  ⟨X ⟨(), 0⟩, 1, fun _ => 1, 0, by simpa using isMultiHomog_Xpow 0 1, isMultiHomog_one',
    by rw [Ideal.mem_bot]; exact one_ne_zero, by intro k; simp, by simp [y0E, cls]⟩
theorem isHomogOf_y0E_sq : IsHomogOf (⊥ : Ideal (MRing ιE)) (y0E * y0E) (fun _ => 2) := by
  have h1 : IsMultiHomog ((X ⟨(), 0⟩ : MRing ιE) ^ 2) (fun _ => 2) := isMultiHomog_Xpow 0 2
  have h3 : (1 : MRing ιE) ∉ (⊥ : Ideal (MRing ιE)) := by rw [Ideal.mem_bot]; exact one_ne_zero
  have h4 : ∀ k : Unit, (((fun _ => 2 : Unit → ℕ) k : ℕ) : ℤ) - (((0 : Unit → ℕ) k : ℕ) : ℤ) = 2 := fun _ => rfl
  have h5 : y0E * y0E * cls ⊥ (1 : MRing ιE) = cls ⊥ ((X ⟨(), 0⟩ : MRing ιE) ^ 2) := by
    simp only [y0E, cls, map_one, mul_one, pow_two, map_mul]
  exact ⟨_, _, _, _, h1, isMultiHomog_one', h3, h4, h5⟩
theorem isHomogOf_zeroE (d : Unit → ℕ) : IsHomogOf (⊥ : Ideal (MRing ιE)) 0 (fun k => (d k : ℤ)) :=
  ⟨0, 1, d, 0, isMultiHomog_zero' d, isMultiHomog_one', by rw [Ideal.mem_bot]; exact one_ne_zero,
    by intro k; simp, by simp [cls]⟩
def basisE : Module.Basis (Fin 2) (FnField (⊥ : Ideal (MRing ιE))) (Fin 2 → FnField (⊥ : Ideal (MRing ιE))) :=
  (Pi.basisFun _ (Fin 2)).unitsSMul fun _ => Units.mk0 y0E flagSection_ne_zero
theorem basisE_apply (a l : Fin 2) : basisE a l = if l = a then y0E else 0 := by
  simp [basisE, Module.Basis.unitsSMul_apply, Pi.single_apply]
def exData : ComponentData Unit Unit ιE where
  N := 2
  j := 1
  two_le_N := le_refl 2
  one_le_j := le_refl 1
  j_lt_N := by norm_num
  P := ⊥
  arith := by simpa using isArithVar_bot 1
  Bd := ∅
  bd_comp := by simp
  bdEq := fun _ => 0
  bdDeg := fun _ => 0
  bdEq_spec := by simp
  N1 := 2
  t := 0
  what₂ := fun _ => noRows 2
  rowDeg := fun _ => 0
  quot := fun _ => isQuotRows_noRows 2
  twist := fun _ _ => 1
  basis := fun _ => ⇑basisE
  ker_basis := fun _ => by
    refine ⟨basisE.linearIndependent, ?_⟩
    rw [basisE.span_eq]
    symm
    rw [LinearMap.ker_eq_top]
    exact LinearMap.ext fun _ => Subsingleton.elim _ _
  basis_homog := fun _ a l => by
    rw [basisE_apply]
    split_ifs
    · exact isHomogOf_y0E
    · simpa using isHomogOf_zeroE (fun _ => 1)
  hodge := fun _ => Matrix.of fun _ l => if l = 0 then y0E else 0
  hodge_homog := fun _ a l => by
    simp only [Matrix.of_apply]
    split_ifs
    · exact isHomogOf_y0E
    · simpa using isHomogOf_zeroE (fun _ => 1)
  hodge_indep := fun _ => by
    have : Unique (Fin (2 - 1)) := inferInstanceAs (Unique (Fin 1))
    show LinearIndependent (FnField ⊥) (fun (_ : Fin (2 - 1)) (l : Fin 2) => if l = 0 then y0E else 0)
    rw [linearIndependent_unique_iff]
    intro h
    have := congrFun h 0
    simp [flagSection_ne_zero] at this
  hodge_sub := fun _ a => Submodule.subset_span ⟨0, by
    funext l
    rw [basisE_apply]
    simp⟩
  metric := fun _ z => ((‖z ⟨(), 0⟩‖ ^ 2 + ‖z ⟨(), 1⟩‖ ^ 2 : ℝ)⁻¹ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
  detLine := fun _ => fsLine (fun _ => 2)
  detCoord := fun _ => y0E * y0E
  detCoord_homog := fun _ => isHomogOf_y0E_sq
  kMu := ()
  k0 := 1
  one_le_k0 := le_refl 1
  muCoord := fun i => cls ⊥ (X ⟨(), i⟩) / y0E
  muCoord_homog := fun i =>
    ⟨X ⟨(), i⟩, X ⟨(), 0⟩, fun _ => 1, fun _ => 1, by simpa using isMultiHomog_Xpow i 1,
      by simpa using isMultiHomog_Xpow 0 1, X_notMem_bot 0, by intro k; simp,
      by show cls ⊥ (X ⟨(), i⟩) / y0E * y0E = _; rw [div_mul_cancel₀ _ flagSection_ne_zero]⟩
  muCoord_ratio := fun i i' => by
    show cls ⊥ (X ⟨(), i⟩) * (cls ⊥ (X ⟨(), i'⟩) / y0E) = cls ⊥ (X ⟨(), i'⟩) * (cls ⊥ (X ⟨(), i⟩) / y0E)
    ring
  muCoord_ne := ⟨0, by rw [show cls ⊥ (X ⟨(), (0 : Fin 2)⟩) = y0E from rfl, div_self flagSection_ne_zero]; exact one_ne_zero⟩
  muLine := fsLine (Pi.single () 1)
  muLine_a := rfl
  muRef := fsLine (Pi.single () 1)
  muRef_a := rfl
  ample := fsLine (fun _ => 1)
  Kamp := 0
  S := ∅
  S_prime := by simp
  latNum := fun _ _ _ => 1
  latDen := fun _ _ _ => 1
  latFl := fun _ _ _ => oneLine
  cuspNorm := fun _ _ => 1
  rd := 1
  Lchi := 0
  one_le_rd := le_refl 1
  regMu := fun _ _ => 0
  regMu_inv := fun _ _ _ _ => rfl
  regCusp := fun _ _ => 0
  regCusp_inv := fun _ _ _ _ => rfl
  regFl := fun _ _ _ _ => 0
  regFl_inv := fun _ _ _ _ _ _ => rfl
end Example
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine


