-- Prove2me | Definitions.Def_OAIQ033D013
-- name    : OAIQ033D013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T01:50:34.92466+00:00
-- url     : https://prove2.me/theorems/8a251347-c4ac-45f5-a247-006c244c1f5c
-- title:
--   Definitions bundle OAIQ033D013 of the split of OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DimensionTen.main_pair`, carved from OpenAI's openai/math development (OpenAI, *Entanglement without distillable secret key in local dimension ten (result family 272)*, OpenAI Math Release, September 27, 2026, result family 272, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 54 declarations of OpenAI's Lean: 35 definitions and 19 theorems. The definitions and types are `OAI.DimensionTen.Mod131.u1`, `OAI.DimensionTen.Mod131.u10`, `OAI.DimensionTen.Mod131.u11`, `OAI.DimensionTen.Mod131.u12`, `OAI.DimensionTen.Mod131.u13`, `OAI.DimensionTen.Mod131.u14`, `OAI.DimensionTen.Mod131.u15`, `OAI.DimensionTen.Mod131.u16`, `OAI.DimensionTen.Mod131.u17`, `OAI.DimensionTen.Mod131.u2`, `OAI.DimensionTen.Mod131.u5`, `OAI.DimensionTen.Mod131.u6`, `OAI.DimensionTen.Mod131.u7`, `OAI.DimensionTen.Mod131.u8`, `OAI.DimensionTen.Mod139.pow1_16_q`, `OAI.DimensionTen.Mod139.pow1_17_q`, `OAI.DimensionTen.Mod139.pow1_4_q`, `OAI.DimensionTen.Mod139.pow1_8_q`, `OAI.DimensionTen.Mod139.u10`, `OAI.DimensionTen.Mod139.u11`, `OAI.DimensionTen.Mod139.u12`, `OAI.DimensionTen.Mod139.u13`, `OAI.DimensionTen.Mod139.u14`, `OAI.DimensionTen.Mod139.u15`, `OAI.DimensionTen.Mod139.u16`, `OAI.DimensionTen.Mod139.u17`, `OAI.DimensionTen.Mod139.u18`, `OAI.DimensionTen.Mod139.u19`, `OAI.DimensionTen.Mod139.u4`, `OAI.DimensionTen.Mod139.u5`, `OAI.DimensionTen.Mod139.u6`, `OAI.DimensionTen.quadraticEval`, `OAI.DimensionTen.symmetricEquiv`, `OAI.DimensionTen.symmetricIndex`, `OAI.DimensionTen.veroneseCoeffs`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Quantum/DimensionTen, in whole or in part: `Quantum_DimensionTen_BorderData`, `Quantum_DimensionTen_Mod131Powers01`, `Quantum_DimensionTen_Mod131Powers03`, `Quantum_DimensionTen_Mod131Powers04`, `Quantum_DimensionTen_Mod131Powers05`, `Quantum_DimensionTen_Mod131Powers06`, `Quantum_DimensionTen_Mod131Powers07`, `Quantum_DimensionTen_Mod131Powers08`, `Quantum_DimensionTen_Mod131Powers09`, `Quantum_DimensionTen_Mod139Powers01`, `Quantum_DimensionTen_Mod139Powers02`, `Quantum_DimensionTen_Mod139Powers03`, `Quantum_DimensionTen_Mod139Powers05`, `Quantum_DimensionTen_Mod139Powers06`, `Quantum_DimensionTen_Mod139Powers07`, `Quantum_DimensionTen_Mod139Powers08`, `Quantum_DimensionTen_Mod139Powers09`, `Quantum_DimensionTen_Mod139Powers10`, `Quantum_DimensionTen_PencilModel`, `Quantum_DimensionTen_Veronese`.
--
--   **Imports.** It imports the published bundle `Def_DimensionTenPair`; the bundles `OAIQ033D000`, `OAIQ033D002`, `OAIQ033D003`, `OAIQ033D004`, `OAIQ033D005`, `OAIQ033D006`, `OAIQ033D007` and `OAIQ033D008` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ033D014`; the statements `OAI.DimensionTen.Mod131.iterate13`, `OAI.DimensionTen.Mod131.iterate7`, `OAI.DimensionTen.Mod139.iterate12`, `OAI.DimensionTen.Mod139.iterate18` and `OAI.DimensionTen.Mod139.iterate6`; the proofs of `OAI.DimensionTen.Mod131.iterate13`, `OAI.DimensionTen.Mod131.iterate7`, `OAI.DimensionTen.Mod139.iterate12`, `OAI.DimensionTen.Mod139.iterate18`, `OAI.DimensionTen.Mod139.iterate6` and `OAI.DimensionTen.exists_swap_of_mod131`.
-- source:
--   OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 272; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Quantum/DimensionTen at commit adc7f12

import Mathlib
import Definitions.Def_DimensionTenPair
import Definitions.Def_OAIQ033D000
import Definitions.Def_OAIQ033D002
import Definitions.Def_OAIQ033D003
import Definitions.Def_OAIQ033D004
import Definitions.Def_OAIQ033D005
import Definitions.Def_OAIQ033D006
import Definitions.Def_OAIQ033D007
import Definitions.Def_OAIQ033D008

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_BorderData
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix
namespace DimensionTen.Border
lemma commute_12_row2 : ∀ k : Fin 20, (B1 * B2) 2 k = (B2 * B1) 2 k := by decide +kernel
lemma commute_12_row3 : ∀ k : Fin 20, (B1 * B2) 3 k = (B2 * B1) 3 k := by decide +kernel
lemma commute_12_row4 : ∀ k : Fin 20, (B1 * B2) 4 k = (B2 * B1) 4 k := by decide +kernel
lemma commute_12_row5 : ∀ k : Fin 20, (B1 * B2) 5 k = (B2 * B1) 5 k := by decide +kernel
lemma commute_12_row6 : ∀ k : Fin 20, (B1 * B2) 6 k = (B2 * B1) 6 k := by decide +kernel
lemma commute_12_row7 : ∀ k : Fin 20, (B1 * B2) 7 k = (B2 * B1) 7 k := by decide +kernel
lemma commute_12_row8 : ∀ k : Fin 20, (B1 * B2) 8 k = (B2 * B1) 8 k := by decide +kernel
lemma commute_12_row9 : ∀ k : Fin 20, (B1 * B2) 9 k = (B2 * B1) 9 k := by decide +kernel
lemma commute_12_row10 : ∀ k : Fin 20, (B1 * B2) 10 k = (B2 * B1) 10 k := by decide +kernel
lemma commute_12_row11 : ∀ k : Fin 20, (B1 * B2) 11 k = (B2 * B1) 11 k := by decide +kernel
lemma commute_12_row12 : ∀ k : Fin 20, (B1 * B2) 12 k = (B2 * B1) 12 k := by decide +kernel
lemma commute_12_row13 : ∀ k : Fin 20, (B1 * B2) 13 k = (B2 * B1) 13 k := by decide +kernel
lemma commute_12_row14 : ∀ k : Fin 20, (B1 * B2) 14 k = (B2 * B1) 14 k := by decide +kernel
lemma commute_12_row15 : ∀ k : Fin 20, (B1 * B2) 15 k = (B2 * B1) 15 k := by decide +kernel
lemma commute_12_row16 : ∀ k : Fin 20, (B1 * B2) 16 k = (B2 * B1) 16 k := by decide +kernel
lemma commute_12_row17 : ∀ k : Fin 20, (B1 * B2) 17 k = (B2 * B1) 17 k := by decide +kernel
lemma commute_12_row18 : ∀ k : Fin 20, (B1 * B2) 18 k = (B2 * B1) 18 k := by decide +kernel
lemma commute_12_row19 : ∀ k : Fin 20, (B1 * B2) 19 k = (B2 * B1) 19 k := by decide +kernel

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod131Powers01
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131


abbrev u1 {R : Type*} [CommRing R] (z : R) : R := pow1_131 z


abbrev u2 {R : Type*} [CommRing R] (z : R) : R := pow2_131 z

end DimensionTen.Mod131

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod131Powers03
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131


abbrev u5 {R : Type*} [CommRing R] (z : R) : R := pow5_131 z


abbrev u6 {R : Type*} [CommRing R] (z : R) : R := pow6_131 z

end DimensionTen.Mod131

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod131Powers04
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131


abbrev u7 {R : Type*} [CommRing R] (z : R) : R := pow7_131 z


abbrev u8 {R : Type*} [CommRing R] (z : R) : R := pow8_131 z

end DimensionTen.Mod131

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod131Powers05
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131


abbrev u10 {R : Type*} [CommRing R] (z : R) : R := pow10_131 z

end DimensionTen.Mod131

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod131Powers06
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131


abbrev u11 {R : Type*} [CommRing R] (z : R) : R := pow11_131 z


abbrev u12 {R : Type*} [CommRing R] (z : R) : R := pow12_131 z

end DimensionTen.Mod131

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod131Powers07
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131


abbrev u13 {R : Type*} [CommRing R] (z : R) : R := pow13_131 z


abbrev u14 {R : Type*} [CommRing R] (z : R) : R := pow14_131 z

end DimensionTen.Mod131

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod131Powers08
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131


abbrev u15 {R : Type*} [CommRing R] (z : R) : R := pow15_131 z


abbrev u16 {R : Type*} [CommRing R] (z : R) : R := pow16_131 z

end DimensionTen.Mod131

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod131Powers09
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131


abbrev u17 {R : Type*} [CommRing R] (z : R) : R := pow17_131 z

end DimensionTen.Mod131

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod139Powers01
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139

abbrev pow1_4_q {R : Type*} [CommRing R] (z : R) : R := pow1_2_q z

abbrev pow1_8_q {R : Type*} [CommRing R] (z : R) : R := pow1_2_q z

abbrev pow1_16_q {R : Type*} [CommRing R] (z : R) : R := pow1_2_q z

abbrev pow1_17_q {R : Type*} [CommRing R] (z : R) : R := pow1_2_q z

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod139Powers02
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139


abbrev u4 {R : Type*} [CommRing R] (z : R) : R := pow4_139 z

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod139Powers03
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139


abbrev u5 {R : Type*} [CommRing R] (z : R) : R := pow5_139 z


abbrev u6 {R : Type*} [CommRing R] (z : R) : R := pow6_139 z

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod139Powers05
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139


abbrev u10 {R : Type*} [CommRing R] (z : R) : R := pow10_139 z

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod139Powers06
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139


abbrev u11 {R : Type*} [CommRing R] (z : R) : R := pow11_139 z


abbrev u12 {R : Type*} [CommRing R] (z : R) : R := pow12_139 z

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod139Powers07
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139


abbrev u13 {R : Type*} [CommRing R] (z : R) : R := pow13_139 z


abbrev u14 {R : Type*} [CommRing R] (z : R) : R := pow14_139 z

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod139Powers08
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139


abbrev u15 {R : Type*} [CommRing R] (z : R) : R := pow15_139 z


abbrev u16 {R : Type*} [CommRing R] (z : R) : R := pow16_139 z

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod139Powers09
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139


abbrev u17 {R : Type*} [CommRing R] (z : R) : R := pow17_139 z


abbrev u18 {R : Type*} [CommRing R] (z : R) : R := pow18_139 z

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod139Powers10
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139


abbrev u19 {R : Type*} [CommRing R] (z : R) : R := u0 z

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_PencilModel
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix ComplexOrder
open Matrix Complex

namespace DimensionTen

def quadraticEval (q : QuadraticIndex → ℂ) (x : Fin 4 → ℂ) : ℂ :=
  ∑ ij : QuadraticIndex, q ij * x ij.val.1 * x ij.val.2




end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Veronese
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

def symmetricIndex (i : Fin 10) : QuadraticIndex :=
  ⟨symmetricPairs i, by fin_cases i <;> decide⟩

lemma symmetricIndex_bijective : Function.Bijective symmetricIndex := by decide

def symmetricEquiv : Fin 10 ≃ QuadraticIndex :=
  Equiv.ofBijective symmetricIndex symmetricIndex_bijective

def veroneseCoeffs (u : Fin 10 → ℂ) (ij : QuadraticIndex) : ℂ :=
  star (u (symmetricEquiv.symm ij)) *
    (if ij.val.1 = ij.val.2 then 1 else (Real.sqrt 2 : ℂ))

end DimensionTen

end
end

end OAI
end


