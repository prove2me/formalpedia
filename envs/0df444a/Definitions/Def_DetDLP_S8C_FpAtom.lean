-- Prove2me | Definitions.Def_DetDLP_S8C_FpAtom
-- name    : DetDLP_S8C_FpAtom
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T04:07:12.775325+00:00
-- url     : https://prove2.me/theorems/95de07f2-eed3-4bf9-82d7-9a4723354237
-- title:
--   Finite-field membership and product certificates
-- statement:
--   The affine-hash atom accepts precisely canonical nonzero residues whose hash lies below the threshold. The product chain accepts exactly pairs of tuples with the prescribed product. Every accepted input has a unique auxiliary certificate. A single widened internal word handles all primes, including two.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4 & Section 3.1–3.2, Lemma 2.4 & Theorem 3.1 (pp. 9–13)

import Definitions.Def_DetDLP_W3_FpHashPins
import Definitions.Def_DetDLP_M89_S1_Queries

set_option autoImplicit false
namespace DetDLP.S8C
open M89S1

/-- Widen once so the strict-modulus multiplier also handles the binary prime. -/
abbrev atomWidth (p : ℕ) := bitLen p + 1

theorem primeFitsAtom (p : ℕ) : p < 2 ^ atomWidth p := by
  have h : p ≤ 2 ^ bitLen p := Nat.le_pow_clog (by decide) p
  exact lt_of_le_of_lt h (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))

abbrev AtomRun (p : ℕ) := Fin p × w3_fpHashCert (atomWidth p) p (Nat.succ_pos _)

/-- The external value is already a canonical residue; its nonzero test enforces the unit domain. -/
def atomOK {p m : ℕ} (S : FpSeed p m) (i : Fin m) (T : ℕ) (x : Fin p) (r : AtomRun p) : Prop :=
  x.val ≠ 0 ∧ r.1.val < T ∧
  w3_fpHashCheck (Nat.succ_pos (bitLen p)) ((S i).1.val+1) (S i).2.val x.val r.1.val r.2

theorem atom_iff {p m : ℕ} [Fact p.Prime] (mul : w3_modMulInterface) (S : FpSeed p m)
    (i : Fin m) (T : ℕ) (x : Fin p) :
    (∃! r, atomOK S i T x r) ↔ x.val ≠ 0 ∧ w3_fpHashWord S i x.val < T := by
  let hd : 1 ≤ atomWidth p := Nat.succ_pos _
  let a : Fin p := ⟨(S i).1.val+1, by have := (S i).1.isLt; omega⟩
  let b := (S i).2
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have sound (r : AtomRun p) (hr : atomOK S i T x r) : r.1.val = w3_fpHashWord S i x.val :=
    w3_fpHash_sound hd hp (primeFitsAtom p) mul a b x r.1 r.2 hr.2.2
  constructor
  · rintro ⟨r,hr,_⟩; exact ⟨hr.1, (sound r hr) ▸ hr.2.1⟩
  · rintro ⟨hx,ht⟩
    let z : Fin p := ⟨w3_fpHashWord S i x.val, Nat.mod_lt _ (by omega)⟩
    obtain ⟨c,hc,uc⟩ := w3_fpHash_unique hd hp (primeFitsAtom p) mul a b x z rfl
    refine ⟨(z,c),⟨hx,ht,hc⟩,?_⟩
    rintro ⟨v,e⟩ he
    have hv : v = z := Fin.ext (sound (v,e) he)
    subst v; rw [uc e he.2.2]

theorem residue_mem_iff {p m : ℕ} [Fact p.Prime] (S : FpSeed p m) (i : Fin m) (T : ℕ)
    (u : (ZMod p)ˣ) : u ∈ fpFactorBlock T S i ↔
    (w3_fpResidue u).val ≠ 0 ∧ w3_fpHashWord S i (w3_fpResidue u).val < T := by
  have hn : (w3_fpResidue u).val ≠ 0 := fun h => u.ne_zero (ZMod.val_injective p (h.trans ZMod.val_zero.symm))
  simp [fpFactorBlock,fpFactorMem,w3_fpHashWord,hn,w3_fpResidue] at *

theorem atom_mem_iff {p m : ℕ} [Fact p.Prime] (mul : w3_modMulInterface) (S : FpSeed p m)
    (i : Fin m) (T : ℕ) (u : (ZMod p)ˣ) :
    (∃! r, atomOK S i T (w3_fpResidue u) r) ↔ u ∈ fpFactorBlock T S i :=
  (atom_iff mul S i T _).trans (residue_mem_iff S i T u).symm

abbrev UnitPair (p m : ℕ) := (Fin m → (ZMod p)ˣ) × (Fin m → (ZMod p)ˣ)

def pairFactors {p m : ℕ} [NeZero p] (ab : UnitPair p m) :=
  (List.ofFn fun i => w3_fpResidue (ab.1 i)) ++ (List.ofFn fun i => w3_fpResidue (ab.2 i))

abbrev ProductRun (p : ℕ) := List (w3_mulStage (atomWidth p) (Nat.succ_pos _) p)

def productOK {p m : ℕ} [NeZero p] (ab : UnitPair p m) (X : (ZMod p)ˣ) (r : ProductRun p) :=
  w3_checkStages (Nat.succ_pos (bitLen p)) (w3_fpResidue 1) (pairFactors ab) r (w3_fpResidue X)

theorem product_iff {p m : ℕ} [Fact p.Prime] (mul : w3_modMulInterface)
    (ab : UnitPair p m) (X : (ZMod p)ˣ) : (∃! r, productOK ab X r) ↔ (∏ i, ab.1 i * ab.2 i) = X := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have cast_prod : ((((pairFactors ab).map Fin.val).prod : ℕ) : ZMod p) = ((∏ i, ab.1 i * ab.2 i : (ZMod p)ˣ) : ZMod p) := by
    simp [pairFactors,w3_fpResidue,List.map_ofFn,Function.comp_def,List.prod_ofFn,Finset.prod_mul_distrib,Units.coe_prod]
  have hv : ((w3_fpResidue (p := p) 1).val * ((pairFactors ab).map Fin.val).prod) % p =
      (w3_fpResidue (∏ i, ab.1 i * ab.2 i)).val := by
    rw [← ZMod.val_natCast, Nat.cast_mul, cast_prod]; simp [w3_fpResidue]
  constructor
  · rintro ⟨r,hr,_⟩
    have h := w3_checkStages_output (Nat.succ_pos (bitLen p)) hp (primeFitsAtom p) mul _ _ _ _ hr
    exact Units.ext (ZMod.val_injective p (h.trans hv).symm)
  · intro h
    apply w3_checkStages_existsUnique (Nat.succ_pos (bitLen p)) hp (primeFitsAtom p) mul
    rw [hv,h]

end DetDLP.S8C


