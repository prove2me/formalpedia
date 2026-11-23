-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneRightInjective
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneRightInjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:36:42.354673+00:00
-- url     : https://prove2.me/theorems/ca237301-7987-4dff-9d15-639c8cbc4cb6
-- title:
--   Block One Right Injective
-- statement:
--   Definitions and structural lemmas for Block One Right Injective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneRightInjective.lean

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
namespace GlobalTheory.CompanionTheory.SW.StabFirst
section Blocks
variable {K : Type} [CommRing K] {M : ℕ}
@[simp] lemma blockOne_zero_zero (t : K) (A : Matrix (Fin M) (Fin M) K) :
    blockOne t A 0 0 = t := rfl
@[simp] lemma blockOne_zero_succ (t : K) (A : Matrix (Fin M) (Fin M) K) (j : Fin M) :
    blockOne t A 0 j.succ = 0 := rfl
@[simp] lemma blockOne_succ_zero (t : K) (A : Matrix (Fin M) (Fin M) K) (i : Fin M) :
    blockOne t A i.succ 0 = 0 := rfl
@[simp] lemma blockOne_succ_succ (t : K) (A : Matrix (Fin M) (Fin M) K) (i j : Fin M) :
    blockOne t A i.succ j.succ = A i j := rfl
lemma blockOne_mul (a b : K) (A B : Matrix (Fin M) (Fin M) K) :
    blockOne a A * blockOne b B = blockOne (a * b) (A * B) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]
lemma blockOne_one : blockOne (1 : K) (1 : Matrix (Fin M) (Fin M) K) = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]
lemma map_blockOne {L : Type} [CommRing L] (φ : K →+* L) (a : K) (A : Matrix (Fin M) (Fin M) K) :
    (blockOne a A).map φ = blockOne (φ a) (A.map φ) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp
lemma cT_blockOne (σ : K →+* K) (a : K) (A : Matrix (Fin M) (Fin M) K) :
    cT σ (blockOne a A) = blockOne (σ a) (cT σ A) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp [cT]
def blockHom : Matrix (Fin M) (Fin M) K →* Matrix (Fin (M + 1)) (Fin (M + 1)) K where
  toFun A := blockOne 1 A
  map_one' := blockOne_one
  map_mul' A B := by rw [blockOne_mul, one_mul]
def blockGL : GL (Fin M) K →* GL (Fin (M + 1)) K := Units.map blockHom
lemma blockGL_mem_UJ (σ : K →+* K) (J : Matrix (Fin M) (Fin M) K) (s : K) {g : GL (Fin M) K}
    (hg : g ∈ UJ σ J) : blockGL g ∈ UJ σ (blockOne s J) := by
  have hg' : cT σ (g : Matrix (Fin M) (Fin M) K) * J * (g : Matrix (Fin M) (Fin M) K) = J := hg
  change cT σ (blockOne 1 (g : Matrix (Fin M) (Fin M) K)) * blockOne s J *
    blockOne 1 (g : Matrix (Fin M) (Fin M) K) = blockOne s J
  rw [cT_blockOne, blockOne_mul, blockOne_mul, hg', map_one, one_mul, mul_one]
end Blocks
section Grp
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (s : E)
lemma JR_blockOne : JR (F := F) R (blockOne s J) = blockOne (inclR (F := F) R s) (JR (F := F) R J) :=
  map_blockOne (inclR (F := F) R) s J
lemma blockGL_mem_HR {g : GL (Fin M) (R ⊗[F] E)} (hg : g ∈ HR R σ J) :
    blockGL g ∈ HR R σ (blockOne s J) := by
  unfold HR
  rw [JR_blockOne]
  exact blockGL_mem_UJ _ _ _ hg
def mkHA (g : GL (Fin M) (R ⊗[F] E)) (hg : g ∈ HR R σ J) : HA R σ J :=
  (⟨g, hg⟩ : HR R σ J)
lemma mat_mem (u : HA R σ J) : HA.mat R σ J u ∈ HR R σ J :=
  Subtype.property (p := fun g => g ∈ HR R σ J) u
lemma mat_injective : Function.Injective (HA.mat R σ J) :=
  fun _ _ h => Subtype.ext (p := fun g => g ∈ HR R σ J) h
def iotaHom : HA R σ J →* HA R σ (blockOne s J) where
  toFun u := mkHA R σ _ (blockGL (HA.mat R σ J u)) (blockGL_mem_HR R σ J s (mat_mem R σ J u))
  map_one' := mat_injective R σ _ (map_one (blockGL (K := R ⊗[F] E) (M := M)))
  map_mul' a b := mat_injective R σ _
    (map_mul (blockGL (K := R ⊗[F] E) (M := M)) (HA.mat R σ J a) (HA.mat R σ J b))
section Top
variable [TopologicalSpace R]
def pairMap {N : ℕ} (J' : Matrix (Fin N) (Fin N) E) (h : HA R σ J') :
    Matrix (Fin N) (Fin N) (R ⊗[F] E) × (Matrix (Fin N) (Fin N) (R ⊗[F] E))ᵐᵒᵖ :=
  Units.embedProduct _ (HA.mat R σ J' h)
end Top
end Grp
end GlobalTheory.CompanionTheory.SW.StabFirst


