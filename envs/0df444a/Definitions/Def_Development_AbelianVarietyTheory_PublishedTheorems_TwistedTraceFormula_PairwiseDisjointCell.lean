-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
-- name    : Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:43.669381+00:00
-- url     : https://prove2.me/theorems/19d0211e-7aa7-4086-bd82-4d14a92eafd7
-- title:
--   Pairwise Disjoint Cell
-- statement:
--   Definitions and structural lemmas for Pairwise Disjoint Cell, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/PairwiseDisjointCell.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_refl
import Theorems.Thm_GlobalTheory_SmGL_hasSatake_detRep
import Theorems.Thm_GlobalTheory_SmGL_nabs_eq_one
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_eq_one_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf


set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling Formalism.UG
open scoped NNReal Pointwise
namespace GlobalTheory.GLDoubling
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n]
abbrev siegel : Subgroup (GL (n ⊕ n) k) := stabGL (diagSub k (Equiv.refl (n ⊕ n)))
abbrev io : GL n k × GL n k →* GL (n ⊕ n) k := blkGL (Equiv.refl (n ⊕ n))
def absRatio : siegel k n →* ℝ≥0 :=
  (distribHaarChar k).comp ((GeneralLinearGroup.det.comp (leviGL (Equiv.refl (n ⊕ n)))) ^ 2 /
    GeneralLinearGroup.det.comp (siegel k n).subtype)
def sphSection (s : ℂ) (h : GL (n ⊕ n) k) : ℂ :=
  npow (iwAbs (absRatio k n) (KO k (n ⊕ n)) h) (s + (Fintype.card n : ℂ) / 2)
variable {k n}
theorem nabs_det_of_mem_KO {m : Type} [Fintype m] [DecidableEq m] {g : GL m k} (hg : g ∈ KO k m) :
    nabs k (GeneralLinearGroup.det g) = 1 := by
  obtain ⟨g, rfl⟩ := hg
  apply nabs_eq_one
  have h1 : ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap 𝒪[k] k) g) : kˣ) : k) =
      algebraMap 𝒪[k] k (GeneralLinearGroup.det g : 𝒪[k]ˣ) :=
    ((algebraMap 𝒪[k] k).map_det _).symm
  rw [h1]
  exact (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit _)
def shear (B C : Matrix n n k) (h : B * C = 0) (h' : C * B = 0) : GL (n ⊕ n) k :=
  ⟨fromBlocks 1 B C 1, fromBlocks 1 (-B) (-C) 1, by simp [fromBlocks_multiply, h, h'],
    by simp [fromBlocks_multiply, h, h']⟩
variable (k n) in

def torusElt (ϖ : kˣ) (e : n → ℤ) : GL n k := diagT k n fun i => ϖ ^ e i
variable (k n) in

def cell (ϖ : kˣ) (e : n → ℤ) : Set (GL n k) :=
  DoubleCoset.doubleCoset (torusElt k n ϖ e) (KO k n) (KO k n)
def lFactor (q : ℕ) (α : n → ℂˣ) (s : ℂ) : ℂ := ∏ i, (1 - (α i : ℂ) * (q : ℂ) ^ (-s))⁻¹
def invNormFactor (q N : ℕ) (s : ℂ) : ℂ := ∏ i ∈ Finset.Icc 1 N, (1 - (q : ℂ) ^ (-(2 * s + i)))
end GlobalTheory.GLDoubling
namespace GlobalTheory.Published
open GlobalTheory.GLDoubling
def UnramifiedDoublingGL : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (n : ℕ) [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)]
    (μ : Measure (GL (Fin n) k)) [μ.IsHaarMeasure], μ (KO k (Fin n)) = 1 →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (α : Fin n → ℂˣ),
      HasSatake π α → ∀ ω : GL (Fin n) k → ℂ, IsZonal π (KO k (Fin n)) ω →
      ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
        Integrable (fun g => sphSection k (Fin n) s (io k (Fin n) (g, 1)) * ω g) μ ∧
        ∫ g, sphSection k (Fin n) s (io k (Fin n) (g, 1)) * ω g ∂μ =
          lFactor (resCard k) α (s + 1 / 2) * lFactor (resCard k) α⁻¹ (s + 1 / 2) *
            invNormFactor (resCard k) n s
example {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    {χ : kˣ →* ℂˣ} (h : IsUnram χ) {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) :
    ∃ α, HasSatake (detRep (Fin n) χ) α ∧
      IsZonal (detRep (Fin n) χ) (KO k (Fin n)) fun g => (χ (GeneralLinearGroup.det g) : ℂ) := by
  have key : ∀ g ∈ KO k (Fin n), χ (GeneralLinearGroup.det g) = 1 := fun g hg =>
    h _ ((nabs_eq_one_iff _).1 (nabs_det_of_mem_KO hg))
  refine ⟨_, hasSatake_detRep h hϖ, 1, fun g => ?_, LinearMap.id, fun g => ?_, rfl, fun g => by simp [detRep]⟩
  · simp [detRep, key _ g.2]
  · ext
    simp [detRep, Module.Dual.transpose_apply, key _ g.2]
end GlobalTheory.Published


