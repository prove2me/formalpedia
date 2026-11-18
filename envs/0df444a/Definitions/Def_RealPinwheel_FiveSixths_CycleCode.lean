-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_CycleCode
-- name    : RealPinwheel_FiveSixths_CycleCode
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T03:03:51.000403+00:00
-- url     : https://prove2.me/theorems/12d82869-901f-4cc9-8bce-dc55aafbac73
-- title:
--   Compact periodic words and rational density boxes
-- statement:
--   A cycle code stores a finite word over letters A, B, and so on, together with integer numerators and denominators for its rational density endpoints and flags for open faces. Decoding at dimension $n>0$ produces a finite array of task positions. Its density box is described by
--
--   $$d_i<p_i/q_i\quad\text{or}\quad d_i\le p_i/q_i,$$
--
--   according to the face flag. The exact integer cycle checker is applied after decoding. This compact representation permits the paper's certificate words and their annotations to be stored without assuming their validity or domain coverage.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf, Section 3, proof of equation (2), printed p. 8 (PDF p. 9), and Section 4, printed pp. 9–11 (PDF pp. 10–12). Certificate data: https://github.com/grzegorz-gutowski/pinwheel_scheduling/tree/main/packing_plans/proof_5_6

import Definitions.Def_RealPinwheel_FiveSixths_CycleCheck

namespace RealPinwheel.FiveSixths

/-- A finite periodic word and rational endpoint data, stored compactly. -/
structure CycleCode where
  word : String
  num : Array ℕ
  den : Array ℕ
  strict : Array Bool
  deriving Repr, DecidableEq

/-- Letters A,B,... encode distinct task positions. Only the integer checker
is used to justify any scheduling property of this data. -/
def codeWord (n : ℕ) (hn : 0 < n) (c : CycleCode) : Array (Fin n) :=
  c.word.toList.toArray.map fun x => ⟨(x.toNat - 65) % n, Nat.mod_lt _ hn⟩

def codeNum {n : ℕ} (c : CycleCode) (i : Fin n) : ℕ := c.num[i.val]?.getD 0

def codeDen {n : ℕ} (c : CycleCode) (i : Fin n) : ℕ := c.den[i.val]?.getD 0

def codeStrict {n : ℕ} (c : CycleCode) (i : Fin n) : Bool := c.strict[i.val]?.getD false

def codeCheck (n : ℕ) (hn : 0 < n) (c : CycleCode) : Bool :=
  cycleCheck (codeWord n hn c) (codeNum c) (codeDen c) (codeStrict c)

/-- Membership in the rational density box described by the endpoint data. -/
def codeBox {n : ℕ} (c : CycleCode) (d : Fin n → ℝ) : Prop :=
  ∀ i, if codeStrict c i then d i < (codeNum c i : ℝ) / codeDen c i
    else d i ≤ (codeNum c i : ℝ) / codeDen c i

end RealPinwheel.FiveSixths


