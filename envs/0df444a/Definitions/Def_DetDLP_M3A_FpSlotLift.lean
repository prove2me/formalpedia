-- Prove2me | Definitions.Def_DetDLP_M3A_FpSlotLift
-- name    : DetDLP_M3A_FpSlotLift
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T13:39:14.458416+00:00
-- url     : https://prove2.me/theorems/7dacc71c-fde5-4b24-b325-7c2c43e488a2
-- title:
--   Fp slot row lift
-- statement:
--   Forward residue map, bit readouts, and unique row-strip witness lift for Fp slots
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_M3A_FpSlotSound

set_option autoImplicit false
namespace DetDLP.M3A.FpSlotLift

export FpSlotSound (forget physical_iff rowPart residue_read hash_read hash_pad multiplier_input hash_bits hash_value)

open FpSlotRows FpSlotTile S8J S8G.FpPhysicalAtom

variable {d k m p T : ℕ} (hd : 1 ≤ d) (mul : w3_modMulInterface) (hp : 2 ≤ p) (hf : p < 2^d)
variable (seed : FpSeed p m) (i : Fin m)

abbrev Accepted (T k : ℕ) := {x : Fin (slotLayout d k hd).nb → Bool //
    Accept _ (slotTest hd p T (seed i).1.val (seed i).2.val) x}

/-- The positive-input and threshold strips certify membership of the decoded residue. -/
def toResidue (x : Accepted hd seed i T k) : w3_fpBlockResidues seed i T := by
  let w := rowPart hd x.1
  have H := (physical_iff hd _).mp ((forget hd x).2)
  have hpb : p < 2^(d+1) := hf.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have W : wordsOK p (min T p) w := FpSlotRows.sound hpb ((min_le_right T p).trans_lt hpb) H.1.2
  have tie (j : Fin (d+1)) := H.2.1 (Fin.natAdd (3*d) (finProdFinEquiv ((0 : Fin 5),j)))
  simp only [ties,Fin.addCases_right,Equiv.symm_apply_apply] at tie
  have et : number w 1 2 = number w 2 0 :=
    congrArg (fun v => (S8L.FpPair.Stage.readWord v).val) (funext tie)
  have e1 := W.1 (1 : Fin 7); have e2 := W.1 (2 : Fin 7); have e3 := W.1 (3 : Fin 7)
  change number w 1 0 + number w 1 1 + 1 = number w 1 2 at e1
  change number w 2 0 + number w 2 1 + 1 = number w 2 2 at e2
  change number w 3 0 + number w 3 1 + 1 = number w 3 2 at e3
  have ep := W.2.2.2.2.2.2.1
  have et' := W.2.2.2.2.2.2.2.2.1
  have ha : (seed i).1.val+1 < p := by have := (seed i).1.isLt; omega
  have he := hash_value hd mul hp hf ha (seed i).2.isLt x.2
  refine ⟨⟨number w 1 2,by omega⟩,?_,?_⟩
  · change number w 1 2 ≠ 0; omega
  change ((seed i).1.val.succ * number w 1 2 + (seed i).2.val) % p < T
  change number w 3 0 = _ at he
  rw [←he]; omega

end DetDLP.M3A.FpSlotLift

noncomputable abbrev DetDLP_M3A_FpSlotLift := @DetDLP.M3A.FpSlotLift.toResidue


