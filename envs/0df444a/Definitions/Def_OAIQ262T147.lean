-- Prove2me | Definitions.Def_OAIQ262T147
-- name    : OAIQ262T147
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T17:25:18.149442+00:00
-- url     : https://prove2.me/theorems/41ae4e1b-30bd-4f40-8a51-2b0b59430ce7
-- title:
--   Definitions bundle OAIQ262T147 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 41 declarations of OpenAI's Lean: 3 definitions and 38 theorems. The definitions and types are `OAI.AtomicTriangular.Construction.exceptionalRow`, `OAI.AtomicTriangular.Construction.exceptionalValue`, `OAI.AtomicTriangular.FiniteCertificate.ordinarySignRowBox`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Triangular_Signs_Exceptional`, `Triangular_Signs_ExceptionalSign0`, `Triangular_Signs_RemainderData4`, `Triangular_Signs_RemainderData5`, `Triangular_Signs_RemainderData6`, `Triangular_Signs_RemainderSums0`, `Triangular_Signs_RemainderSums1`, `Triangular_Signs_RemainderSums2`, `Triangular_Signs_RemainderSums3`, `Triangular_Signs_RemainderSums4`, `Triangular_Signs_RemainderSums5`, `Triangular_Signs_RemainderSums6`, `Triangular_Signs_SignBase`.
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T085`, `OAIQ262T097`, `OAIQ262T100`, `OAIQ262T113`, `OAIQ262T132` and `OAIQ262T133` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T159`, `OAIQ262T171`, `OAIQ262T174`, `OAIQ262T175`, `OAIQ262T177`, `OAIQ262T180`, `OAIQ262T181`, `OAIQ262T183`, `OAIQ262T184`, `OAIQ262T185`, `OAIQ262T186`, `OAIQ262T187`, `OAIQ262T188`, `OAIQ262T189`, `OAIQ262T190`, `OAIQ262T191` and `OAIQ262T192`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T085
import Definitions.Def_OAIQ262T097
import Definitions.Def_OAIQ262T100
import Definitions.Def_OAIQ262T113
import Definitions.Def_OAIQ262T132
import Definitions.Def_OAIQ262T133

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_Exceptional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction

def exceptionalRow (test : Fin 4) (l : Fin 23) (r : Fin 8) : ℝ :=
  exceptionalOffset test l.val r +
    ∑ ep : Fin 2, ∑ j : Fin 3, if j.val≤l.val ∧ l.val-j.val<21 then
      exceptionalWeight test ep j * frozenTaylorRow (if ep.val=0 then 0 else Z) (l.val-j.val) r else 0

def exceptionalValue (test : Fin 4) (e : Fin 8 → ℝ) (τ : ℝ) : ℝ :=
  let A := frozenTaylor 0 e τ
  let D := frozenTaylor Z e τ
  if test.val=0 then Q 1+τ*A
  else if test.val=1 then Q 1*(τ+Z)+(2*(τ^2+2*Z*τ)*A+τ^2*D)/3
  else if test.val=2 then Q 1*(τ+2*Z)+((τ^2+4*Z*τ+6*Z^2)*A+2*(τ^2+2*Z*τ)*D)/3
  else Q 1*(τ+3*Z)+(τ^2+4*Z*τ+6*Z^2)*D
lemma exceptionalRow_eval (test : Fin 4) (e : Fin 8 → ℝ) (he : e 1=1) (τ : ℝ) :
    (∑ l : Fin 23, (∑ r : Fin 8, exceptionalRow test l r*e r)*τ^l.val) =
      exceptionalValue test e τ := by
  have hoff : (∑ l : Fin 23, (∑ r : Fin 8, exceptionalOffset test l.val r*e r)*τ^l.val) =
      (if test.val=0 then Q 1 else Q 1*(τ+test.val*Z)) := by
    simp only [exceptionalOffset,ite_mul,zero_mul]
    fin_cases test <;> norm_num [Fin.sum_univ_succ,Fin.succ,he] <;> ring
  have hshift (ep : Fin 2) (j : Fin 3) :
      (∑ l : Fin 23, (∑ r : Fin 8,
        (if j.val≤l.val ∧ l.val-j.val<21 then
          exceptionalWeight test ep j*frozenTaylorRow (if ep.val=0 then 0 else Z) (l.val-j.val) r else 0)*e r)*τ^l.val) =
        exceptionalWeight test ep j*τ^j.val*frozenTaylor (if ep.val=0 then 0 else Z) e τ := by
    simp only [ite_mul,zero_mul,Finset.sum_ite_irrel,Finset.sum_const_zero]
    simp_rw [mul_assoc,←Finset.mul_sum]
    have hh := PolynomialShift.shift_sum (N:=20) (M:=22) (d:=j.val) (by omega)
      (fun l => ∑ r : Fin 8, frozenTaylorRow (if ep.val=0 then 0 else Z) l r*e r) τ
    have hcond (l : Fin 23) : (j.val≤l.val ∧ l.val-j.val<21) ↔ (j.val≤l.val ∧ l.val-j.val≤20) := by omega
    have hfac (c : Prop) [Decidable c] (x : ℝ) :
        (if c then exceptionalWeight test ep j*x else 0) =
          exceptionalWeight test ep j*(if c then x else 0) := by split_ifs <;> simp
    simp only [hcond,hfac, mul_assoc,←Finset.mul_sum]
    simp only [ite_mul,zero_mul] at hh
    rw [hh]
    rfl
  simp only [exceptionalRow,add_mul,Finset.sum_add_distrib,Finset.sum_mul]
  simp only [Finset.sum_mul] at hoff
  rw [hoff]
  have hex : (∑ l : Fin 23, (∑ r : Fin 8, ∑ ep : Fin 2, ∑ j : Fin 3,
      (if j.val≤l.val ∧ l.val-j.val<21 then
          exceptionalWeight test ep j*frozenTaylorRow (if ep.val=0 then 0 else Z) (l.val-j.val) r else 0)*e r)*τ^l.val) =
      ∑ ep : Fin 2, ∑ j : Fin 3,
        exceptionalWeight test ep j*τ^j.val*frozenTaylor (if ep.val=0 then 0 else Z) e τ := by
    simp_rw [Finset.sum_comm (s:=Finset.univ (α:=Fin 8)) (t:=Finset.univ (α:=Fin 2)),
      Finset.sum_comm (s:=Finset.univ (α:=Fin 8)) (t:=Finset.univ (α:=Fin 3)),Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ep _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simpa only [Finset.sum_mul] using hshift ep j
  simp only [Finset.sum_mul] at hex
  rw [hex]
  fin_cases test <;> norm_num [exceptionalValue,exceptionalWeight,Fin.sum_univ_succ,Fin.succ] <;> ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_ExceptionalSign0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma ex0r22_calc (r : Fin 8) : exceptionalRowBox 0 22 r = ex0r22 r := by
  revert r
  decide +kernel
lemma ex0b0_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 0 r = ex0b0 r := by
  revert r
  decide +kernel
lemma ex0b10_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 10 r = ex0b10 r := by
  revert r
  decide +kernel
lemma ex0b11_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 11 r = ex0b11 r := by
  revert r
  decide +kernel
lemma ex0b12_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 12 r = ex0b12 r := by
  revert r
  decide +kernel
lemma ex0b13_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 13 r = ex0b13 r := by
  revert r
  decide +kernel
lemma ex0b14_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 14 r = ex0b14 r := by
  revert r
  decide +kernel
lemma ex0b15_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 15 r = ex0b15 r := by
  revert r
  decide +kernel
lemma ex0b16_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 16 r = ex0b16 r := by
  revert r
  decide +kernel
lemma ex0b17_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 17 r = ex0b17 r := by
  revert r
  decide +kernel
lemma ex0b18_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 18 r = ex0b18 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderData4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData4_00_pre (j : Fin 31) : (remainderExpInput 0 0 4 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 4).mul (taylorNormTable 0 0 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData4_01_pre (j : Fin 31) : (remainderExpInput 0 1 4 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 4).mul (taylorNormTable 0 1 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData4_10_pre (j : Fin 31) : (remainderExpInput 1 0 4 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 4).mul (taylorNormTable 1 0 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData4_11_pre (j : Fin 31) : (remainderExpInput 1 1 4 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 4).mul (taylorNormTable 1 1 j)).divNat 24)).lo := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderData5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData5_00_pre (j : Fin 31) : (remainderExpInput 0 0 5 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 5).mul (taylorNormTable 0 0 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData5_01_pre (j : Fin 31) : (remainderExpInput 0 1 5 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 5).mul (taylorNormTable 0 1 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData5_10_pre (j : Fin 31) : (remainderExpInput 1 0 5 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 5).mul (taylorNormTable 1 0 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData5_11_pre (j : Fin 31) : (remainderExpInput 1 1 5 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 5).mul (taylorNormTable 1 1 j)).divNat 24)).lo := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderData6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData6_00_pre (j : Fin 31) : (remainderExpInput 0 0 6 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 6).mul (taylorNormTable 0 0 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData6_01_pre (j : Fin 31) : (remainderExpInput 0 1 6 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 6).mul (taylorNormTable 0 1 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData6_10_pre (j : Fin 31) : (remainderExpInput 1 0 6 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 6).mul (taylorNormTable 1 0 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData6_11_pre (j : Fin 31) : (remainderExpInput 1 1 6 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 6).mul (taylorNormTable 1 1 j)).divNat 24)).lo := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderSums0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderColumns0_0_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (remainderData0_10 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=remainderColumns0_0 c := by
  revert c
  decide +kernel
lemma remainderColumns0_1_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (remainderData0_11 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=remainderColumns0_1 c := by
  revert c
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderSums1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderColumns1_0_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (remainderData1_10 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=remainderColumns1_0 c := by
  revert c
  decide +kernel
lemma remainderColumns1_1_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (remainderData1_11 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=remainderColumns1_1 c := by
  revert c
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderSums2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderColumns2_0_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (remainderData2_10 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=remainderColumns2_0 c := by
  revert c
  decide +kernel
lemma remainderColumns2_1_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (remainderData2_11 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=remainderColumns2_1 c := by
  revert c
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderSums3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderColumns3_0_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (remainderData3_10 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=remainderColumns3_0 c := by
  revert c
  decide +kernel
lemma remainderColumns3_1_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (remainderData3_11 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=remainderColumns3_1 c := by
  revert c
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderSums4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderColumns4_0_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (remainderData4_10 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=remainderColumns4_0 c := by
  revert c
  decide +kernel
lemma remainderColumns4_1_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (remainderData4_11 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=remainderColumns4_1 c := by
  revert c
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderSums5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderColumns5_0_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (remainderData5_10 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=remainderColumns5_0 c := by
  revert c
  decide +kernel
lemma remainderColumns5_1_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (remainderData5_11 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=remainderColumns5_1 c := by
  revert c
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderSums6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderColumns6_0_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (remainderData6_10 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=remainderColumns6_0 c := by
  revert c
  decide +kernel
lemma remainderColumns6_1_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (remainderData6_11 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=remainderColumns6_1 c := by
  revert c
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_SignBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

def ordinarySignRowBox (side : Fin 2) (n : Fin 7) (a : Fin 21 → Fin 8 → RI)
    (l : Fin 21) (r : Fin 8) : RI :=
  if side.val=0 then ((if l.val=0 then ordinaryOffsetBox n r else RI.point 0).sub (a l r)) else a l r
end AtomicTriangular.FiniteCertificate
end

end OAI
end


