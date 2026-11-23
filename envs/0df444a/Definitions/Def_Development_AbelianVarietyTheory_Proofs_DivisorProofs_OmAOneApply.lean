-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmAOneApply
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmAOneApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:21:43.000779+00:00
-- url     : https://prove2.me/theorems/a4d1979b-30e4-4d06-942b-5254242b8a7a
-- title:
--   Om AOne Apply
-- statement:
--   Definitions and structural lemmas for Om AOne Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OmAOneApply.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRankSB
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil
namespace GlobalTheory.RankFibreKer
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def tw (ν : kˣ →* ℂˣ) (d : ℕ) {a : ℕ} (g : GL (Fin a) k) : ℂ :=
  (ν (gdet g) : ℂ) * apow (gdet g) ((d : ℂ) / 2)
def minor {a d : ℕ} (Y : Matrix (Fin a) (Fin d) k) (J : Fin a ↪ Fin d) : k := (Y.submatrix id J).det
def idx {a d : ℕ} : (Fin a ↪ Fin d) ≃ Fin (Fintype.card (Fin a ↪ Fin d)) := Fintype.equivFin _
variable (k) in

def slice (a d : ℕ) : Set (Matrix (Fin a) (Fin d) k) :=
  {Z | ∃ J : Fin a ↪ Fin d, Z.submatrix id J = 1 ∧ ∀ J' : Fin a ↪ Fin d,
    valuation k (minor Z J') ≤ 1 ∧ (idx J' < idx J → valuation k (minor Z J') < 1)}
def IsFirstMax {a d : ℕ} (Y : Matrix (Fin a) (Fin d) k) (J : Fin a ↪ Fin d) : Prop :=
  minor Y J ≠ 0 ∧ ∀ J' : Fin a ↪ Fin d, valuation k (minor Y J') ≤ valuation k (minor Y J) ∧
    (idx J' < idx J → valuation k (minor Y J') < valuation k (minor Y J))
open Classical in

def sec {a d : ℕ} (Y : Matrix (Fin a) (Fin d) k) : GL (Fin a) k :=
  if h : ∃ J, IsFirstMax Y J then GeneralLinearGroup.mkOfDetNeZero (Y.submatrix id h.choose) h.choose_spec.1 else 1
end GlobalTheory.RankFibreKer


