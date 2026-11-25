-- Prove2me | Definitions.Def_DetDLP_M3B_ECArithBlock
-- name    : DetDLP_M3B_ECArithBlock
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T11:12:07.490804+00:00
-- url     : https://prove2.me/theorems/6878e512-5402-404b-9ccb-3b8761f13cb1
-- title:
--   Witness-independent EC slot arithmetic rows
-- statement:
--   Builds the seven range-checked products, parity-selected native seed, finite curve check and threshold adder from named rows, and proves their register-level equivalence to elemOK under hash routing.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8H0_PointGraph
import Definitions.Def_DetDLP_M3B_ECPrefix

set_option autoImplicit false
set_option maxHeartbeats 12000
namespace DetDLP.M3B.ECArithBlock
open S8H0 RegisterMap NamedBlocks ResidueWires SignalBank GateRoutes GateSemantics HashRows RangeRows
open S8H.ECPointArithmetic S8H.ECPointSlots

/- In a factor-base slot infinity is forbidden. Repurpose its flag register
   for the complement of the parity bit. This makes all four one-bit functions
   of parity available as named wires or public constants, without fan-in. -/
variable {p m : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))
variable (seed : ECSeed p m) (i : Fin m)
abbrev Sh (p : ℕ) := S (d p) (e p)

def negRef : Ref (Sh p) := .reg CurveRows.flag
def posRef : Ref (Sh p) := .reg (CurveRows.ybit ⟨0,hd p⟩)
def chooseRef (a b : Bool) : Ref (Sh p) :=
  match a,b with
  | false,false => .pin false
  | true,true => .pin true
  | false,true => posRef
  | true,false => negRef

def parityRow (p : ℕ) := rows (s:=Sh p) 1 2 (fun _ => ![posRef,negRef])
  (fun _ a => decide (a 1 = !a 0))

theorem parityRow_iff (u : U p) : (parityRow p).OK u ↔ negRef.eval u = !posRef.eval u := by
  simp [parityRow,rows_iff]

theorem choose_spec (u : U p) (hn : (parityRow p).OK u) (a b : Bool) :
    (chooseRef a b).eval u = if posRef.eval u then b else a := by
  have H := (parityRow_iff u).mp hn
  cases a <;> cases b <;> simp [chooseRef,H] <;> rfl

def selectWord (f g : ℕ) : Word (Sh p) := fun j => chooseRef (f.testBit j) (g.testBit j)

theorem select_spec (u : U p) (hn : (parityRow p).OK u) (f g : ℕ) :
    evalWord (selectWord f g) u (if posRef.eval u then g else f) := by
  intro j; rw [selectWord,choose_spec u hn]; split <;> rfl

def A (s : Bool) := (seed i s).1.val+1
def Bv (s : Bool) := (seed i s).2.val

def seedWires := { wires (hd p) p (coeff E) 6 with
  a := selectWord (A seed i false) (A seed i true)
  b := selectWord (Bv seed i false) (Bv seed i true) }

private theorem rawWord (u : U p) (f : Path (triple (d p)) (Sh p)) (z : Triple (d p))
    (H : ∀ j : Fin (d p), (f (.fst (.word j))).get (raw u) = z.1 j) :
    evalWord (rword f) u (value z.1).val := word_eval _ u z.1 H

theorem parity_value (u : U p) (h : canonical p (raw u)) :
    posRef.eval u = decide ((typed u h).1.2.2.val % 2 = 1) := by
  have H := (Addr.correct (CurveRows.ybit (e:=e p) (⟨0,hd p⟩ : Fin (d p))) (u ∘ Fin.castSucc)).symm
  change posRef.eval u = (raw u).1.2.2.1 ⟨0,hd p⟩ at H
  rw [H,coordY u h,← ResidueWires.value_bit (raw u).1.2.2.1 ⟨0,hd p⟩]; exact Nat.testBit_zero ..

theorem seed_iff (u : U p) (h : canonical p (raw u)) (hn : (parityRow p).OK u) :
    let v := typed u h
    (HashRows.block p (seedWires E seed i)).OK u ↔ w3_slotHashBits (hd p)
      (alpha seed i v.1.2.2).val (beta seed i v.1.2.2).val v.1.2.1.val
      (v.2.1 6).1.val (v.2.1 6).2 (v.2.2 6) := by
  let v := typed u h
  let o := decide (v.1.2.2.val % 2 = 1)
  have ha : (alpha seed i v.1.2.2).val = A seed i o := by
    apply ZMod.val_natCast_of_lt; have := (seed i o).1.isLt; change (seed i o).1.val+1 < p; omega
  have hb : (beta seed i v.1.2.2).val = Bv seed i o := ZMod.val_natCast_of_lt (seed i o).2.isLt
  have pick (f : Bool → ℕ) : evalWord (selectWord (f false) (f true)) u (f o) := by
    have hs := select_spec u hn (f false) (f true)
    have he : (if posRef.eval u then f true else f false) = f o := by
      change (if posRef.eval u then f true else f false) = f o
      rw [show posRef.eval u = o from parity_value u h]; cases o <;> rfl
    rwa [he] at hs
  apply block_spec (hd p) _ u _ _ _ _ _ _
  · rw [ha]; exact pick (A seed i)
  · rw [coordX u h]; exact rawWord u xa (raw u).1.2.1 (fun _ => rfl)
  · rw [hb]; exact pick (Bv seed i)
  · rw [outVal u h]; exact rawWord u (oa 6) ((raw u).2.1 6).1 (fun _ => rfl)
  · exact rawWord u (ra 6) ((raw u).2.1 6).2.1.1 (fun _ => rfl)
  · exact word_eval (fun a => runPath 6 (.snd (.fst (.snd (.fst a))))) u ((raw u).2.1 6).2.1.2.1 (fun _ => rfl)
  · exact word_eval (fun a => m1 6 (.fst a)) u ((raw u).2.1 6).2.1.2.2.1.1 (fun _ => rfl)
  · exact word_eval (fun a => m2 6 (.fst a)) u ((raw u).2.1 6).2.1.2.2.2.1 (fun _ => rfl)
  · exact word_eval (fun a => aux 6 (.snd (.fst a))) u ((raw u).2.2 6).2.1 (fun _ => rfl)
  · intro j; have H := ((Ref.masked (p.testBit j) (cm (d:=d p) (e:=e p) 6)).correct u).symm
    change (Ref.masked (p.testBit j) (cm 6)).eval u = (if ((raw u).2.1 6).2.2 then p else 0).testBit j
    rw [H]; change (p.testBit j && ((raw u).2.1 6).2.2) = _
    cases ((raw u).2.1 6).2.2 <;> simp
  all_goals funext j; exact (Addr.correct _ (u ∘ Fin.castSucc)).symm

/-- The first six products use the curve coefficients; only the seventh uses
    the parity-selected public seed. No test captures a point or a trace. -/
def products := many 6 fun g => if g = 6 then HashRows.block p (seedWires E seed i)
  else HashRows.block p (wires (hd p) p (coeff E) g)

set_option maxHeartbeats 300000 in
private theorem args_fixed (x y a b : ZMod p) (v : Fin 7 → ZMod p) (g : Fin 7) (hg : g ≠ 6) :
    args E x y 0 0 v g = args E x y a b v g := by
  have hg' : g = 0 ∨ g = 1 ∨ g = 2 ∨ g = 3 ∨ g = 4 ∨ g = 5 := by omega
  rcases hg' with (rfl|rfl|rfl|rfl|rfl|rfl) <;> simp [args]

theorem products_iff (u : U p) (h : canonical p (raw u)) (hn : (parityRow p).OK u) :
    let v := typed u h
    (products E seed i).OK u ↔ slots E v.1.2.1 v.1.2.2 (alpha seed i v.1.2.2) (beta seed i v.1.2.2) v.2 := by
  unfold products slots; rw [many_iff]; apply forall_congr'; intro g
  by_cases hg : g = 6
  · subst g; rw [if_pos rfl]; exact seed_iff E seed i u h hn
  · rw [if_neg hg]; apply (hash_iff E u h g).trans
    unfold SevenChecks.gateArgs; rw [args_fixed E _ _ _ _ _ _ hg]

/-- Fold curve equality into bit rows without testing the scratch parity flag
    as if it were an infinity tag. The decoded coordinate tag is always false. -/
def onCurve (p : ℕ) := eqs (s:=Sh p) (d p) (fun j => .reg (CurveRows.outbit 2 j))
  (fun j => .reg (CurveRows.outbit 5 j))

theorem onCurve_iff (u : U p) (h : canonical p (raw u)) :
    (onCurve p).OK u ↔ checkCurve (false,(typed u h).1.2) (typed u h).2 := by
  rw [onCurve,eqs_iff]
  have he (g : Fin 7) (j : Fin (d p)) : (Ref.reg (CurveRows.outbit g j)).eval u =
      ((typed u h).2.1 g).1.val.testBit j.val := by
    rw [outVal u h,ResidueWires.value_bit]; exact (Addr.correct _ (u ∘ Fin.castSucc)).symm
  simp only [he]; change (∀ j : Fin (d p), _ = _) ↔ ((typed u h).2.1 2).1 = ((typed u h).2.1 5).1
  constructor
  · intro H; apply ZMod.val_injective p; apply Nat.eq_of_testBit_eq; intro j
    by_cases hj : j < d p
    · exact H ⟨j,hj⟩
    · have hpw := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_gt hj)
      rw [Nat.testBit_eq_false_of_lt (((typed u h).2.1 2).1.val_lt.trans_le ((fits p).le.trans hpw)),
        Nat.testBit_eq_false_of_lt (((typed u h).2.1 5).1.val_lt.trans_le ((fits p).le.trans hpw))]
  · intro H j; rw [H]

def baseBlock := joinB (PointGraph.zeroLast (Sh p).size) <| joinB (RangeRows.block (d p) (e p) p) <|
  joinB (parityRow p) (joinB (products E seed i) (onCurve p))

theorem baseBlock_iff (u : U p) : (baseBlock E seed i).OK u ↔
    u (Fin.last _) = false ∧ ∃ h : canonical p (raw u), negRef.eval u = !posRef.eval u ∧
    let v := typed u h
    slots E v.1.2.1 v.1.2.2 (alpha seed i v.1.2.2) (beta seed i v.1.2.2) v.2 ∧
      checkCurve (false,v.1.2) v.2 := by
  simp only [baseBlock,joinB_iff,PointGraph.zeroLast_iff,RangeRows.block_iff]
  constructor
  · rintro ⟨hz,h,hn,hs,hc⟩
    exact ⟨hz,h,(parityRow_iff u).mp hn,(products_iff E seed i u h hn).mp hs,(onCurve_iff u h).mp hc⟩
  · rintro ⟨hz,h,hn,hs,hc⟩; have hn' := (parityRow_iff u).mpr hn
    exact ⟨hz,h,hn',(products_iff E seed i u h hn').mpr hs,(onCurve_iff u h).mpr hc⟩

/-- Embed a slot's existing names in a larger register space without changing
    its factor tests. The result includes the range proof for gate 6's output. -/
def rewire {a b : ℕ} (c : B a) (f : Fin a → Fin b) : B b := ⟨c.core,f ∘ c.name⟩

theorem rewire_iff {a b : ℕ} (c : B a) (f : Fin a → Fin b) (v : Bits b) :
    (rewire c f).OK v ↔ c.OK (v ∘ f) := Iff.rfl

variable {s : Shape} (T : ℕ)
structure SlotPath (p : ℕ) (s : Shape) where
  bank : Fin ((Sh p).size+1) → Fin (s.size+1)
  hash : Fin (d p) → Ref s
  diff : Fin (d p) → Ref s
  carry : Fin (d p+1) → Ref s

def threshold (z : SlotPath p s) := add (n:=d p+1) true (pad z.hash) (pad z.diff)
  (fun j => .pin (T.testBit j.val)) z.carry

def slotBlock (z : SlotPath p s) := joinB (rewire (baseBlock E seed i) z.bank) (threshold T z)

def diffCert (z : SlotPath p s) (v : Bits (s.size+1)) : w3_slotDiff (d p) :=
  (value (fun j => (z.diff j).eval v),fun j => (z.carry j).eval v)

def rawHash (u : U p) : Bits (d p) := ((raw u).2.1 6).1.1

theorem threshold_iff (z : SlotPath p s) (v : Bits (s.size+1))
    (route : ∀ j, (z.hash j).eval v = rawHash (v ∘ z.bank) j) :
    (threshold T z).OK v ↔ w3_slotLt (d p) (value (rawHash (v ∘ z.bank))).val T (diffCert z v) := by
  rw [threshold,add_iff]; unfold w3_slotLt diffCert
  have h₁ := pad_eval (n:=d p+1) z.hash v _ route
  have h₂ := pad_eval (n:=d p+1) z.diff v (fun j => (z.diff j).eval v) (fun _ => rfl)
  simp only [h₁,h₂]; exact S8C.AddLayout.columns_iff (by omega) ..

theorem slotBlock_iff (z : SlotPath p s) (v : Bits (s.size+1))
    (route : ∀ j, (z.hash j).eval v = rawHash (v ∘ z.bank) j) :
    let u := v ∘ z.bank
    (slotBlock E seed i T z).OK v ↔ u (Fin.last _) = false ∧ ∃ h : canonical p (raw u),
      negRef.eval u = !posRef.eval u ∧ elemOK E seed i T (bitLen p) []
        ((false,(typed u h).1.2),(typed u h).2,diffCert z v) := by
  dsimp only
  rw [slotBlock,joinB_iff,rewire_iff,baseBlock_iff,threshold_iff T z v route]
  constructor
  · rintro ⟨⟨hz,h,hn,hs,hc⟩,ht⟩
    refine ⟨hz,h,hn,hs,hc,rfl,?_,rfl⟩
    rw [outVal]; exact ht
  · rintro ⟨hz,h,hn,hs,hc,_,ht,_⟩
    refine ⟨⟨hz,h,hn,hs,hc⟩,?_⟩
    simpa only [rawHash,←outVal (v ∘ z.bank) h 6] using ht

end DetDLP.M3B.ECArithBlock


