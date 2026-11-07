-- Prove2me | Definitions.Def_MatMulDS_wordRun
-- name    : MatMulDS_wordRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:00:47.22843+00:00
-- url     : https://prove2.me/theorems/7599e067-b3dd-4e75-b0fa-82f0da69b6e3
-- title:
--   Word programs on the algebraic RAM
-- statement:
--   A **word program** is a program of the published algebraic RAM using only word instructions: no field cell and no coin. This is how the mission counts the time of the combinatorial steps of the source (labelings, search over strings).
--
--   `wordRun` gives the final word memory of such a program on given input words if it halts within $t$ steps, and `encStr` is a fixed encoding of a string over a finite alphabet as a natural number, in base the alphabet's size.
--
--   **Formalization Note** Field cells play no part in a word program, so the placeholder field $\mathbb Q$ in `wordRun` has no effect.
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), Lemma A.3, p.70 (PDF p.72); Lemma A.4, p.71 (PDF p.73); Lemma A.6, p.76 (PDF p.78)

import Mathlib
import Definitions.Def_MatroidSensOracle_AlgRAM

set_option autoImplicit false

open MatroidSensOracle

namespace MatMulDS

/-- A word instruction of the published algebraic RAM: no field cell and no coin is touched. -/
def IsWordInstr : AInstr → Prop
  | .one _ | .add _ _ _ | .sub _ _ _ | .mul _ _ _ | .udiv _ _ _ | .umod _ _ _ | .load _ _ | .store _ _
  | .bltz _ _ | .halt => True
  | _ => False

/-- A program of the published algebraic RAM that uses word instructions only: a word RAM program. -/
def IsWordProgram (P : List AInstr) : Prop := ∀ i ∈ P, IsWordInstr i

/-- The final word memory, if the word program `P` on the input words `inp` halts within `t` steps. Field cells and
coins play no part in a word program, so the field `ℚ` here is only a placeholder. -/
noncomputable def wordRun (P : List AInstr) (w : ℕ) (inp : List ℤ) (t : ℕ) : Option (ℤ → BitVec w) :=
  (aexec (F := ℚ) P (fun _ => 0) t 0 0 (aloadWords w inp) (aloadFields [])).map Prod.fst

/-- A fixed encoding of a string over a finite alphabet as a natural number, in base `|X|`. -/
noncomputable def encStr {X : Type} [Fintype X] {n : ℕ} (σ : Fin n → X) : ℕ :=
  ∑ ℓ : Fin n, ((Fintype.equivFin X (σ ℓ) : ℕ)) * Fintype.card X ^ (ℓ : ℕ)

end MatMulDS


