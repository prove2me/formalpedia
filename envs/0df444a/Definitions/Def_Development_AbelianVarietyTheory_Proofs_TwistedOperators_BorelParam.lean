-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BorelParam
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_BorelParam
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:52:38.091355+00:00
-- url     : https://prove2.me/theorems/2b3e61a5-54a6-460c-b220-1075616fd504
-- title:
--   Borel Param
-- statement:
--   Definitions and structural lemmas for Borel Param, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BorelParam.lean

import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_VolumeFlatSection
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling
namespace GlobalTheory.ZonalCellDecomposition
def blkEquiv (l t : ℕ) : Fin (l * t) ≃ GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.Blocks l t :=
  finProdFinEquiv.symm.trans (Equiv.sigmaEquivProd (Fin l) (Fin t)).symm
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def mtor {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (e : D → ℤ) :
    GL (A ⊕ D) k :=
  torusElt k (A ⊕ D) ϖ (Sum.elim 0 e)
def dcell {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (e : D → ℤ) :
    Set (GL (A ⊕ D) k) :=
  DoubleCoset.doubleCoset (mtor ϖ e) (GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.parahoric k A D : Set (GL (A ⊕ D) k))
    (GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.parahoric k A D)
def IsBiType {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ξ : kˣ →* ℂˣ)
    (φ : GL (A ⊕ D) k → ℂ) : Prop :=
  ∀ j ∈ GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.parahoric k A D, ∀ d : kˣ, (d : k) = (j : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det →
    ∀ g, φ (j * g) = (ξ d : ℂ) * φ g ∧ φ (g * j) = (ξ d : ℂ) * φ g
def sumAbs {D : Type} [Fintype D] (e : D → ℤ) : ℤ := ∑ i, |e i|
def zonalInt {N : ℕ} [MeasurableSpace (GL (Fin N) k)] (μK : Measure (GL (Fin N) k)) (ψ : GL (Fin N) k → ℂ)
    (g : GL (Fin N) k) : ℂ :=
  ∫ κ in (KO k (Fin N) : Set (GL (Fin N) k)), ψ (κ * g) ∂μK
def borelParam {N : ℕ} (q : ℕ) (α : Fin N → ℂˣ) (x : Fin N) : ℂ :=
  (α x : ℂ) * (q : ℂ) ^ (((x : ℕ) : ℂ) - ((N : ℂ) - 1) / 2)
end GlobalTheory.ZonalCellDecomposition


