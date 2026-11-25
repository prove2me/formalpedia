-- Prove2me | Definitions.Def_DetDLP_S8L_FpPairChain
-- name    : DetDLP_S8L_FpPairChain
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T05:46:29.050214+00:00
-- url     : https://prove2.me/theorems/863e1e89-037a-460d-9e44-643bba1c36b2
-- title:
--   Shortened product chain for a finite-field tuple pair
-- statement:
--   Given two ordered tuples of $m$ prime-field units, use the first factor as the accumulator and multiply the remaining factors. The checked transcript has exactly $2m-1$ multiplication stages. Erasing these stages and the two families of hash certificates gives a bijection with the prefix-constrained pairs whose product equals the public target.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4 & Section 3.1–3.2, Lemma 2.4 & Theorem 3.1 (pp. 9–13)

import Definitions.Def_DetDLP_S8C_FpQueryCount

set_option autoImplicit false
namespace DetDLP.S8L.FpPair
open S8C M89S1

/-- Initialize the accumulator with the first factor. The empty list uses the unit. -/
def chain {p : ℕ} [NeZero p] (xs : List (Fin p)) (r : ProductRun p) (z : Fin p) : Prop :=
  match xs with
  | [] => w3_checkStages (Nat.succ_pos (bitLen p)) (w3_fpResidue 1) [] r z
  | x :: ys => w3_checkStages (Nat.succ_pos (bitLen p)) x ys r z

private theorem stages_length {p d : ℕ} {hd : 1 ≤ d} {x z : Fin p} {xs : List (Fin p)}
    {r : List (w3_mulStage d hd p)} (h : w3_checkStages hd x xs r z) : r.length = xs.length := by
  induction xs generalizing x r with
  | nil => cases r with
    | nil => rfl
    | cons => exact False.elim h
  | cons a as ih => cases r with
    | nil => exact False.elim h
    | cons t ts => exact congrArg Nat.succ (ih h.2)

theorem chain_length {p : ℕ} [NeZero p] {xs : List (Fin p)} {r : ProductRun p} {z : Fin p}
    (h : chain xs r z) : r.length = xs.length - 1 := by
  cases xs <;> exact stages_length h

private theorem chain_value {p : ℕ} [Fact p.Prime] (mul : w3_modMulInterface)
    (xs : List (Fin p)) (z : Fin p) :
    (∀ r, chain xs r z → z.val = (xs.map Fin.val).prod % p) ∧
    (z.val = (xs.map Fin.val).prod % p → ∃! r, chain xs r z) := by
  have hp := (Fact.out : p.Prime).two_le
  have h₁ : (w3_fpResidue (p := p) 1).val = 1 := by simp [w3_fpResidue, ZMod.val_one]
  cases xs with
  | nil =>
    constructor
    · intro r hr
      simpa [h₁] using w3_checkStages_output (Nat.succ_pos _) hp (primeFitsAtom p) mul _ [] r z hr
    · intro h
      exact w3_checkStages_existsUnique (Nat.succ_pos _) hp (primeFitsAtom p) mul _ [] z (by simpa [h₁] using h)
  | cons a as =>
    exact ⟨fun r hr => w3_checkStages_output (Nat.succ_pos _) hp (primeFitsAtom p) mul a as r z hr,
      fun h => w3_checkStages_existsUnique (Nat.succ_pos _) hp (primeFitsAtom p) mul a as z h⟩

private theorem factors_value {p m : ℕ} [Fact p.Prime] (ab : UnitPair p m) :
    ((pairFactors ab).map Fin.val).prod % p = (w3_fpResidue (∏ i, ab.1 i * ab.2 i)).val := by
  rw [← ZMod.val_natCast]
  simp [pairFactors, w3_fpResidue, List.map_ofFn, Function.comp_def, List.prod_ofFn,
    Finset.prod_mul_distrib, Units.coe_prod]

/-- A Tag 5 transcript with two atom families and the shortened product chain. -/
def shortOK {p m : ℕ} [Fact p.Prime] (S : FpSeed p m) (T : ℕ) (X : (ZMod p)ˣ) (η : List Bool)
    (ab : UnitPair p m) (r : PairRun p m) : Prop :=
  (∀ i, atomOK S i T (w3_fpResidue (ab.1 i)) (r.1 i)) ∧
  (∀ i, atomOK S i T (w3_fpResidue (ab.2 i)) (r.2.1 i)) ∧
  (tupleWord elemWord ab).take η.length = η ∧ chain (pairFactors ab) r.2.2 (w3_fpResidue X)

theorem stage_count {p m : ℕ} [Fact p.Prime] {S : FpSeed p m} {T : ℕ} {X : (ZMod p)ˣ} {η : List Bool}
    {ab : UnitPair p m} {r : PairRun p m} (h : shortOK S T X η ab r) : r.2.2.length = 2*m-1 := by
  simpa [pairFactors, two_mul] using chain_length h.2.2.2

noncomputable def shortEquiv {p m : ℕ} [Fact p.Prime] (mul : w3_modMulInterface)
    (S : FpSeed p m) (T : ℕ) (X : (ZMod p)ˣ) (η : List Bool) :
    {v : UnitPair p m × PairRun p m // shortOK S T X η v.1 v.2} ≃ ↥(pairSet S T X η) := by
  classical
  apply certEquiv
  · rintro ab r ⟨ha,hb,hη,hc⟩
    have out := ((chain_value mul _ _).1 _ hc).trans (factors_value ab)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ ab,fun i => ⟨atom_sound mul S i T _ _ (ha i),
      atom_sound mul S i T _ _ (hb i)⟩,hη,Units.ext (ZMod.val_injective p out.symm)⟩
  · intro ab hab
    obtain ⟨_,hm,hη,hX⟩ := Finset.mem_filter.mp hab
    choose a ha ua using fun i => (atom_mem_iff mul S i T (ab.1 i)).mpr (hm i).1
    choose b hb ub using fun i => (atom_mem_iff mul S i T (ab.2 i)).mpr (hm i).2
    obtain ⟨r,hr,ur⟩ := (chain_value mul (pairFactors ab) (w3_fpResidue X)).2 (by rw [factors_value,hX])
    refine ⟨(a,b,r),⟨ha,hb,hη,hr⟩,?_⟩
    rintro ⟨a',b',r'⟩ ⟨ha',hb',_,hr'⟩
    exact Prod.ext (funext fun i => ua i _ (ha' i)) (Prod.ext (funext fun i => ub i _ (hb' i)) (ur _ hr'))

end DetDLP.S8L.FpPair


