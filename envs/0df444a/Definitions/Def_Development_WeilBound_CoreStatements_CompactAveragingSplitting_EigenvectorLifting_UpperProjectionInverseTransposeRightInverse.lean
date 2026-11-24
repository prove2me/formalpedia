-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
-- name    : Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T22:04:03.411429+00:00
-- url     : https://prove2.me/theorems/220be683-8ae8-472b-a5e7-601352723806
-- title:
--   Upper Projection Inverse Transpose Right Inverse
-- statement:
--   Definitions and structural lemmas for Upper Projection Inverse Transpose Right Inverse, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/UpperProjectionInverseTransposeRightInverse.lean

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero


set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
namespace PositivityTheory.ThK.SplitLoc.Unr
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SmGL
section Alg
open PowerSeries
abbrev polys : Subring (PowerSeries ℂ) := (Polynomial.coeToPowerSeries.ringHom : Polynomial ℂ →+* PowerSeries ℂ).range
def conv (P : Polynomial ℂ) (n : ℕ) (f : ℤ → ℂ) (m : ℤ) : ℂ := ∑ j ∈ Finset.range (n + 1), P.coeff j * f (m - j)
end Alg
section ZetaNonvanishing₂
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def dShell (n : ℕ) (m : ℤ) : Set (GL (Fin n) k) := {g | ord k (gdet g) = m}
def wt {n : ℕ} (d : ℕ) (ν : kˣ →* ℂˣ) (g : GL (Fin n) k) : ℂ := (ν (gdet g) : ℂ) * apow (gdet g) ((d : ℂ) / 2)
def cst (d : ℕ) (ϖ : kˣ) (ν : kˣ →* ℂˣ) : ℂ := (ν ϖ : ℂ) * (resCard k : ℂ) ^ (-(d : ℂ) / 2)
def scal (n : ℕ) (u : kˣ) : GL (Fin n) k := diagGL fun _ => u
variable [MeasurableSpace k] [BorelSpace k]
def Jm (n : ℕ) (φ : Matrix (Fin n) (Fin n) k → ℂ) (m : ℤ) : ℂ :=
  ∫ g in dShell n m, φ g.val ∂haarVol (KO k (Fin n))
section Hermite
open GlobalTheory.SatakeBound
theorem span_pow_le_min {R : Type} [CommRing R] (p : R) (m M : ℕ) :
    Ideal.span {p ^ m} ≤ Ideal.span {p ^ min m M} :=
  Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow p (min_le_left m M))
def hermRed {R : Type} [CommRing R] {n : ℕ} (p : R) (a : Fin n → ℕ) (M : ℕ) :
    HermIdx p a →+ HermIdx p fun i => min (a i) M where
  toFun c i j := Ideal.Quotient.factor (span_pow_le_min p (a i) M) (c i j)
  map_zero' := by funext i j; simp
  map_add' c c' := by funext i j; simp
def cosetInt {n : ℕ} (φ : Matrix (Fin n) (Fin n) k → ℂ) (x : Matrix (Fin n) (Fin n) k) : ℂ :=
  ∫ w in (KO k (Fin n) : Set (GL (Fin n) k)), φ (x * w.val) ∂haarVol (KO k (Fin n))
end Hermite
end ZetaNonvanishing₂
section Cont
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
end Cont
section SBfun
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end SBfun
section Main
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
section Frames
variable {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
end Frames
variable [MeasurableSpace k] [BorelSpace k]
end Main
section Main2
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def blkAGL {a a' : ℕ} (b : GL (Fin (a + a')) k) (dA : kˣ) (h : (dA : k) = (blkA b).det) : GL (Fin a) k :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (blkA b) (by rw [← h]; exact dA.ne_zero)
def blkDGL {a a' : ℕ} (b : GL (Fin (a + a')) k) (dD : kˣ) (h : (dD : k) = (blkD b).det) : GL (Fin a') k :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (blkD b) (by rw [← h]; exact dD.ne_zero)
variable [MeasurableSpace k] [BorelSpace k]
variable {a a' : ℕ} {ϖ : kˣ} {α β ν : kˣ →* ℂˣ}
end Main2
section Clauses
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {a a' : ℕ} {ϖ : kˣ} {α β ν : kˣ →* ℂˣ}
end Clauses
section Clauses2
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {a a' : ℕ} {ϖ : kˣ} {α β ν : kˣ →* ℂˣ}
end Clauses2
end PositivityTheory.ThK.SplitLoc.Unr
namespace PositivityTheory.ThK.SplitLoc
open Unr GlobalTheory.SplitFlip GlobalTheory.SplitWeil
end PositivityTheory.ThK.SplitLoc


