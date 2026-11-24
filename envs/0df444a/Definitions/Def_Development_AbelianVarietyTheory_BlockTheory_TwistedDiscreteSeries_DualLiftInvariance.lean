-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLiftInvariance
-- name    : Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLiftInvariance
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:26.440449+00:00
-- url     : https://prove2.me/theorems/4129af0e-76ed-46e7-863d-7b5df8b9e77a
-- title:
--   Dual Lift Invariance
-- statement:
--   Definitions and structural lemmas for Dual Lift Invariance, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/DualLiftInvariance.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData
open GlobalTheory.SplitWeil GlobalTheory.LatPair
section Objects
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' n'' : Type} [Fintype n] [Fintype n'] [Fintype n'']
def InDual (L : Submodule 𝒪[k] (n → k)) (η : n → k) : Prop := ∀ y ∈ L, η ⬝ᵥ y ∈ 𝒪[k]
def Lifts (L : Submodule 𝒪[k] (n → k)) (F : n → k) (f : Module.Dual 𝓀[k] (Red L)) : Prop :=
  ∀ y : L, ∃ s : 𝒪[k], (s : k) = F ⬝ᵥ (y : n → k) ∧ residue 𝒪[k] s = f (Red.mk L y)
open Classical in

def cosetInd (q : Unif k) (L : Submodule 𝒪[k] (n → k)) (f : Module.Dual 𝓀[k] (Red L)) (η : n → k) : ℂ :=
  if ∃ F : n → k, Lifts L F f ∧ InDual L (η - q.inv • F) then 1 else 0
open Classical in

def datum (q : Unif k) (P : Pair k n') (LY : Submodule 𝒪[k] (n → k)) (x₀ : Matrix n n' k) (y : n → k) : ℂ :=
  if (∀ z ∈ P.ker, x₀ *ᵥ z ∈ LY) ∧ q.inv • y + x₀ *ᵥ P.vec ∈ LY then 1 else 0
def withCol (x₀ : Matrix n n' k) (y : n → k) : Matrix n (n' ⊕ Fin 1) k := fromCols x₀ (replicateCol (Fin 1) y)
def withRow (x' : Matrix n'' n k) (η : n → k) : Matrix (n'' ⊕ Fin 1) n k := fromRows x' (replicateRow (Fin 1) η)
def qvec (q : Unif k) (P : Pair k n') : Red P.ker :=
  Red.mk P.ker ⟨q.1 • P.vec, Pair.smul_mem_ker q.mem_max P.hasVal_vec.mem⟩
def resUnit (ε : 𝒪[k]ˣ) : 𝓀[k]ˣ := Units.map (residue 𝒪[k]).toMonoidHom ε
open Classical in

def term (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (ε : 𝓀[k]ˣ) (P : Pair k n') (LY : Submodule 𝒪[k] (n → k))
    (fW : Module.Dual 𝓀[k] (Red LY)) (x₀ : Matrix n n' k) : ℂ :=
  if h : ∀ z ∈ P.ker, x₀ *ᵥ z ∈ LY then
    χ (-((ε : 𝓀[k]) * fW (Red.mk LY
      ⟨x₀ *ᵥ (q.1 • P.vec), h _ (Pair.smul_mem_ker q.mem_max P.hasVal_vec.mem)⟩)))
  else 0
open Classical in

def compInd (L : Submodule 𝒪[k] (n' → k)) (LY : Submodule 𝒪[k] (n → k)) (f' : Module.Dual 𝓀[k] (Red L))
    (fW : Module.Dual 𝓀[k] (Red LY)) (x₀ : Matrix n n' k) : ℂ :=
  if ∃ h : ∀ z ∈ L, x₀ *ᵥ z ∈ LY, ∀ z : L, fW (Red.mk LY ⟨x₀ *ᵥ z, h z z.2⟩) = f' (Red.mk L z) then 1 else 0
def mainDatum (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (ε : 𝓀[k]ˣ) (P : Pair k n') (Q : Pair k n)
    (x₀ : Matrix n n' k) : ℂ :=
  ∑ᶠ f' : {f : Module.Dual 𝓀[k] (Red P.ker) // f ≠ 0},
    χ (-((ε : 𝓀[k]) * f'.1 (qvec q P))) * phiOne (ofDual P.ker f') Q x₀
def lastKer (L : Submodule 𝒪[k] (n'' → k)) : Submodule 𝒪[k] (n'' ⊕ Fin 1 → k) :=
  L.map (inX k n'' 1) ⊔ Submodule.span 𝒪[k] {avec k n'' 1 1}
open MeasureTheory ValuativeRel Matrix IsLocalRing in
open scoped Pointwise in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' n'' : Type} [Fintype n] [Fintype n'] [Fintype n''] in
omit [Fintype n''] in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer {L : Submodule 𝒪[k] (n'' → k)} {y : n'' ⊕ Fin 1 → k} :
    y ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.lastKer L ↔ y ∘ Sum.inl ∈ L ∧ y (Sum.inr 0) ∈ 𝒪[k] := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.lastKer
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, z, hz, rfl⟩
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hz
    refine ⟨?_, ?_⟩
    · have hcomp : ((_root_.GlobalTheory.LatPair.inX k n'' 1) x +
          s • _root_.GlobalTheory.LatPair.avec k n'' 1 1) ∘ Sum.inl = x := by
        funext i
        simp [_root_.GlobalTheory.LatPair.inX, _root_.GlobalTheory.LatPair.avec]
      rw [hcomp]
      exact hx
    · simpa [_root_.GlobalTheory.LatPair.inX, _root_.GlobalTheory.LatPair.avec, Subring.smul_def] using s.2
  · rintro ⟨h1, h2⟩
    refine ⟨_, ⟨_, h1, rfl⟩, (⟨y (Sum.inr 0), h2⟩ : 𝒪[k]) • _root_.GlobalTheory.LatPair.avec k n'' 1 1,
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
    funext i
    rcases i with i | i
    · simp [_root_.GlobalTheory.LatPair.inX, _root_.GlobalTheory.LatPair.avec]
    · fin_cases i
      simp [_root_.GlobalTheory.LatPair.inX, _root_.GlobalTheory.LatPair.avec, Subring.smul_def]
open MeasureTheory ValuativeRel Matrix IsLocalRing in
open scoped Pointwise in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' n'' : Type} [Fintype n] [Fintype n'] [Fintype n''] in
omit [Fintype n''] in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.lastKer_eq (q : _root_.GlobalTheory.LatPair.Unif k)
    (L : Submodule 𝒪[k] (n'' → k)) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.lastKer L = _root_.GlobalTheory.LatPair.gluedLat q 1 2 L 0 := by
  ext y
  rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer, _root_.GlobalTheory.LatPair.mem_gluedLat]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨0, by simpa using h1, fun i => ?_⟩
    fin_cases i
    exact ⟨fun _ => h2, fun h => by norm_num at h, fun h => by norm_num at h⟩
  · rintro ⟨s, h1, h2⟩
    exact ⟨by simpa using h1, (h2 0).1 (by norm_num)⟩
open MeasureTheory ValuativeRel Matrix IsLocalRing in
open scoped Pointwise in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' n'' : Type} [Fintype n] [Fintype n'] [Fintype n''] in
omit [Fintype n''] in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.isGlue_last (q : _root_.GlobalTheory.LatPair.Unif k) (L : Submodule 𝒪[k] (n'' → k)) [L.IsLattice k] :
    _root_.GlobalTheory.LatPair.IsGlue (_root_.GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.lastKer L) (q.inv • _root_.GlobalTheory.LatPair.avec k n'' 1 1) := by
  rw [_root_.GlobalTheory.LatPair.isGlue_iff q]
  refine ⟨_root_.GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.lastKer_eq q L ▸ _root_.GlobalTheory.LatPair.gluedLat_isLattice q 1 2 L 0, ?_, ?_⟩
  · rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer]
    rintro ⟨-, h⟩
    have hinv : (((q : 𝒪[k]) : k))⁻¹ ∈ 𝒪[k] := by
      simpa [_root_.GlobalTheory.LatPair.avec, _root_.GlobalTheory.LatPair.Unif.inv] using h
    apply q.mem_max
    exact IsUnit.of_mul_eq_one (b := ⟨_, hinv⟩)
      (Subtype.ext (by simp [mul_inv_cancel₀ q.ne_zero]))
  · rw [_root_.GlobalTheory.LatPair.Unif.smul_inv_smul, _root_.GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer]
    refine ⟨?_, ?_⟩
    · have hzero : _root_.GlobalTheory.LatPair.avec k n'' 1 1 ∘ Sum.inl = 0 := by
        funext i
        simp [_root_.GlobalTheory.LatPair.avec]
      rw [hzero]
      exact L.zero_mem
    · simpa [_root_.GlobalTheory.LatPair.avec] using one_mem 𝒪[k]
def lastPair (q : Unif k) (L : Submodule 𝒪[k] (n'' → k)) [L.IsLattice k] : Pair k (n'' ⊕ Fin 1) :=
  glue (isGlue_last q L)
variable [MeasurableSpace k]
def datumHat (ψ : AddChar k Circle) (ε : 𝒪[k]ˣ) (μ : Measure (n → k)) (q : Unif k) (P : Pair k n')
    (LY : Submodule 𝒪[k] (n → k)) (x₀ : Matrix n n' k) (η : n → k) : ℂ :=
  ∫ y, datum q P LY x₀ y * (ψ (((ε : 𝒪[k]) : k) * (η ⬝ᵥ y)) : ℂ) ∂μ
def volQ (μ : Measure (n → k)) (q : Unif k) (L : Submodule 𝒪[k] (n → k)) : ℝ :=
  μ.real {y | q.inv • y ∈ L}
variable [DecidableEq n'] {M A : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup A] [Module ℂ A]
def IsLiftInv (π : Representation ℂ (GL n' k) M) (θ : M →ₗ[ℂ] (Matrix n n' k → ℂ) →ₗ[ℂ] A)
    (L : Submodule 𝒪[k] (n' → k)) : Prop :=
  ∀ g ∈ latStab L, ∀ v : M, ∀ Ψ ∈ SB (Matrix n n' k), θ (π g v) (fun x => Ψ (x * g.val)) = θ v Ψ
end Objects
section Statements
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] (n n' n'' : Type) [Fintype n] [Fintype n'] [Fintype n''] [DecidableEq n']
def TransformFormula : Prop :=
  ∀ (q : Unif k) (ψ : AddChar k Circle) (hψ : HasConductor ψ 1) (ε : 𝒪[k]ˣ) (μ : Measure (n → k))
    [μ.IsAddHaarMeasure] (P : Pair k n') (LY : Submodule 𝒪[k] (n → k)) [LY.IsLattice k],
    (∀ x₀ y, datum q P LY x₀ y = latInd (gluedS q 1 P.ker P.vec) LY (withCol x₀ y)) ∧
    0 < volQ μ q LY ∧
    ∀ (x₀ : Matrix n n' k) (η : n → k),
      Integrable (fun y => datum q P LY x₀ y * (ψ (((ε : 𝒪[k]) : k) * (η ⬝ᵥ y)) : ℂ)) μ ∧
      datumHat ψ ε μ q P LY x₀ η = (volQ μ q LY : ℂ) * ∑ᶠ fW : Module.Dual 𝓀[k] (Red LY),
        term q (resChar ψ hψ q) (resUnit ε) P LY fW x₀ * cosetInd q LY fW η
def Decomposition : Prop :=
  ∀ (q : Unif k) (ψ : AddChar k Circle) (hψ : HasConductor ψ 1) (ε : 𝒪[k]ˣ)
    (P : Pair k n') (LY : Submodule 𝒪[k] (n → k)) [LY.IsLattice k],
    (∀ (fW : Module.Dual 𝓀[k] (Red LY)) (x₀ : Matrix n n' k),
      latInd P.ker LY x₀ = ∑ᶠ f' : Module.Dual 𝓀[k] (Red P.ker), compInd P.ker LY f' fW x₀ ∧
      term q (resChar ψ hψ q) (resUnit ε) P LY fW x₀ = ∑ᶠ f' : Module.Dual 𝓀[k] (Red P.ker),
        resChar ψ hψ q (-((resUnit ε : 𝓀[k]) * f' (qvec q P))) * compInd P.ker LY f' fW x₀) ∧
    term q (resChar ψ hψ q) (resUnit ε) P LY 0 = latInd P.ker LY ∧
    (∀ fW : {f : Module.Dual 𝓀[k] (Red LY) // f ≠ 0},
      compInd P.ker LY 0 fW.1 = latInd P.ker (ofDual LY fW).ker ∧
      (∀ f' : {f : Module.Dual 𝓀[k] (Red P.ker) // f ≠ 0},
        compInd P.ker LY f'.1 fW.1 = phiOne (ofDual P.ker f') (ofDual LY fW)) ∧
      term q (resChar ψ hψ q) (resUnit ε) P LY fW.1 =
        latInd P.ker (ofDual LY fW).ker + mainDatum q (resChar ψ hψ q) (resUnit ε) P (ofDual LY fW)) ∧
    ∀ L : Submodule 𝒪[k] (n → k), (L = LY ∨ ∃ fW, L = (ofDual LY fW).ker) →
      (∀ g ∈ latStab P.ker, ∀ x₀ : Matrix n n' k, latInd P.ker L (x₀ * g.val) = latInd P.ker L x₀) ∧
      ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (φ : Form k n' M), φ ∈ Mram k n' M →
        (∀ x₀ : Matrix n n' k, ∑ P₁ ∈ withKer P.ker, latInd P₁.ker L x₀ • φ P₁ = 0) ∧
        ∀ (π : Representation ℂ (GL n' k) M) (A : Type) [AddCommGroup A] [Module ℂ A]
          (θ : M →ₗ[ℂ] (Matrix n n' k → ℂ) →ₗ[ℂ] A), φ ∈ EqForm π → IsLiftInv π θ P.ker →
          θ (φ P) (latInd P.ker L) = 0
def ClassSumFormula : Prop :=
  ∀ (q : Unif k) (ψ : AddChar k Circle) (hψ : HasConductor ψ 1) (ε : 𝒪[k]ˣ)
    (L : Submodule 𝒪[k] (n' → k)) [L.IsLattice k] (Q : Pair k n)
    (M : Type) [AddCommGroup M] [Module ℂ M] (φ : Form k n' M), φ ∈ Mram k n' M →
    (∀ x₀ : Matrix n n' k,
      ∑ P ∈ withKer L, mainDatum q (resChar ψ hψ q) (resUnit ε) P Q x₀ • φ P =
        ∑ P' ∈ withLat L, phiOne P' Q x₀ • dia (resUnit ε) (FFStar q (resChar ψ hψ q) φ) P') ∧
    ∀ (π : Representation ℂ (GL n' k) M) (A : Type) [AddCommGroup A] [Module ℂ A]
      (θ : M →ₗ[ℂ] (Matrix n n' k → ℂ) →ₗ[ℂ] A), φ ∈ EqForm π → IsLiftInv π θ L →
      ∀ P P' : Pair k n', P.ker = L → P'.lat = L →
        θ (φ P) (mainDatum q (resChar ψ hψ q) (resUnit ε) P Q) =
          θ (dia (resUnit ε) (FFStar q (resChar ψ hψ q) φ) P') (phiOne P' Q)
open Classical in

def LastStep : Prop :=
  ∀ (q : Unif k) (LY : Submodule 𝒪[k] (n → k)) [LY.IsLattice k] (L'' : Submodule 𝒪[k] (n'' → k)) [L''.IsLattice k],
    (∀ (fW : {f : Module.Dual 𝓀[k] (Red LY) // f ≠ 0}) (x' : Matrix n'' n k) (η : n → k),
      phiOne (ofDual LY fW) (lastPair q L'') (withRow x' η) =
        latInd LY L'' x' * (if Lifts LY (q.1 • η) fW.1 then 1 else 0) ∧
      phiOne (ofDual LY fW) (lastPair q L'') (withRow x' η) = latInd LY L'' x' * cosetInd q LY fW.1 η) ∧
    ∀ (ψ : AddChar k Circle) (hψ : HasConductor ψ 1) (ε : 𝒪[k]ˣ) (L : Submodule 𝒪[k] (n' → k)) [L.IsLattice k]
      (M : Type) [AddCommGroup M] [Module ℂ M] (φ : Form k n' M), φ ∈ Mram k n' M →
      ∀ (x' : Matrix n'' n k) (η : n → k),
        (∀ x₀ : Matrix n n' k,
          ∑ P ∈ withKer L, (∑ᶠ fW : {f : Module.Dual 𝓀[k] (Red LY) // f ≠ 0},
              mainDatum q (resChar ψ hψ q) (resUnit ε) P (ofDual LY fW) x₀ *
                (latInd LY L'' x' * cosetInd q LY fW.1 η)) • φ P =
            ∑ Q ∈ withLat LY, ∑ P' ∈ withLat L,
              (phiOne Q (lastPair q L'') (withRow x' η) * phiOne P' Q x₀) •
                dia (resUnit ε) (FFStar q (resChar ψ hψ q) φ) P') ∧
        ∀ (μ : Measure (n → k)) [μ.IsAddHaarMeasure],
          (∀ x₀ : Matrix n n' k,
            ∑ P ∈ withKer L, (datumHat ψ ε μ q P LY x₀ η * latInd LY L'' x') • φ P =
              (volQ μ q LY : ℂ) • ∑ Q ∈ withLat LY, ∑ P' ∈ withLat L,
                (phiOne Q (lastPair q L'') (withRow x' η) * phiOne P' Q x₀) •
                  dia (resUnit ε) (FFStar q (resChar ψ hψ q) φ) P') ∧
          ∀ (π : Representation ℂ (GL n' k) M) (A : Type) [AddCommGroup A] [Module ℂ A]
            (θ : M →ₗ[ℂ] (Matrix n n' k → ℂ) →ₗ[ℂ] A), φ ∈ EqForm π → IsLiftInv π θ L →
            ∀ P P' : Pair k n', P.ker = L → P'.lat = L →
              latInd LY L'' x' • θ (φ P) (fun x₀ => datumHat ψ ε μ q P LY x₀ η) =
                (volQ μ q LY : ℂ) • ∑ Q ∈ withLat LY, phiOne Q (lastPair q L'') (withRow x' η) •
                  θ (dia (resUnit ε) (FFStar q (resChar ψ hψ q) φ) P') (phiOne P' Q)
end Statements
def LastTwoSteps : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n n' n'' : Type) [Fintype n] [Fintype n'] [Fintype n''] [DecidableEq n'],
    TransformFormula k n n' ∧ Decomposition k n n' ∧ ClassSumFormula k n n' ∧ LastStep k n n' n''
section Examples
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' n'' : Type} [Fintype n] [Fintype n'] [Fintype n'']
example (q : Unif k) (L : Submodule 𝒪[k] (n'' → k)) [L.IsLattice k] :
    (lastPair q L).ker = lastKer L ∧ (lastPair q L).HasVal (q.inv • avec k n'' 1 1) 1 :=
  ⟨glue_ker _, glue_hasVal _⟩
example (q : Unif k) (P : Pair k n') (LY : Submodule 𝒪[k] (n → k)) : datum q P LY 0 0 = 1 :=
  if_pos ⟨fun _ _ => by simp, by simp⟩
example (q : Unif k) (L : Submodule 𝒪[k] (n → k)) : cosetInd q L 0 0 = 1 :=
  if_pos ⟨0, fun _ => ⟨0, by simp, by simp⟩, fun _ _ => by simp⟩
example : (resUnit (-1 : 𝒪[k]ˣ) : 𝓀[k]) = -1 := by simp [resUnit]
end Examples
end GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData


