-- Prove2me | Definitions.Def_DetDLP_M13B_EndpointPoly
-- name    : DetDLP_M13B_EndpointPoly
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T01:43:39.617156+00:00
-- url     : https://prove2.me/theorems/f3558f35-9214-4706-acef-41414200dc48
-- title:
--   DetDLP M13B EndpointPoly

import Definitions.Def_DetDLP_M13B_EndpointCore
import Definitions.Def_ToTuring_Lib_Unary
import Theorems.Thm_Groundwork_PolyT_pow_unary
import Theorems.Thm_Groundwork_Unary_of_length
import Theorems.Thm_Groundwork_Unary_of_le
import Theorems.Thm_Groundwork_PolyT_div
import Theorems.Thm_Groundwork_PolyT_mod
import Theorems.Thm_Groundwork_PolyT_mul

set_option autoImplicit false
set_option maxHeartbeats 600000
namespace DetDLP.M13BEndpoint
open Groundwork
attribute [local fun_prop] Groundwork.PolyT.comp Groundwork.PolyT.const Groundwork.PolyT.fst
  Groundwork.PolyT.snd Groundwork.PolyT.prodMk Groundwork.PolyT.length Groundwork.PolyT.map
  Groundwork.PolyT.filter Groundwork.PolyT.flatMap Groundwork.PolyT.testBit Groundwork.PolyT.div
  Groundwork.PolyT.mod Groundwork.PolyT.mul P2M_Groundwork_PolyT_id__1c5d0f44cc8f
  P2M_Groundwork_PolyT_cons__3a60f43a3b86 P2M_Groundwork_PolyT_ite__226169acf219
  P2M_Groundwork_PolyT_cond__4c673073da15 P2M_Groundwork_PolyT_size__c8c8eb1b342f

@[fun_prop] theorem unpack_poly {α : Type} [Enc α] {b src : α → ℕ} (hb : PolyT b) (hs : PolyT src) :
    PolyT (fun x => unpack (b x) (src x)) := by
  obtain ⟨t,ht,_,hlt⟩ := PolyT.len_bound hb
  have hf : PolyT (fun x => (src x).bits.foldl (fun s _ => advance (b x) s) (src x, [])) := by
    refine PolyT.foldl_add (g := fun x (s : State) (_ : Bool) => advance (b x) s) (by fun_prop)
      (by fun_prop) (by unfold advance; fun_prop) ⟨fun n => 2*t n + 6, (PB.const 2 |>.mul ht).add (PB.const 6), ?_⟩
    intro x c e he
    unfold advance; split
    · omega
    · have hq := Nat.size_le_size (Nat.div_le_self (c.1 / b x) (b x) |>.trans (Nat.div_le_self _ _))
      by_cases hz : b x = 0
      · rcases c with ⟨n,l⟩
        have hx := hlt x; simp [hz,len_pair,len_cons,len_nat] at *; omega
      · have hm := Nat.size_le_size (Nat.mod_lt c.1 (Nat.pos_of_ne_zero hz)).le
        have hm' := Nat.size_le_size (Nat.mod_lt (c.1 / b x) (Nat.pos_of_ne_zero hz)).le
        have hx := hlt x
        rcases c with ⟨n,l⟩
        simp only [len_pair,len_cons,len_nat] at *; omega
  exact PolyT.reverse (PolyT.snd hf)

/-- A clipped exponent is polynomially bounded even on malformed inputs. -/
def cell (q s n : ℕ) := (q+2)^(min n s.bits.length)-1
@[fun_prop] theorem cell_poly {α : Type} [Enc α] {q s n : α → ℕ} (hq : PolyT q) (hs : PolyT s) (hn : PolyT n) :
    PolyT (fun x => cell (q x) (s x) (n x)) := by
  unfold cell; apply PolyT.sub _ (PolyT.const 1)
  exact PolyT.pow_unary (by fun_prop) (Unary.of_le (Unary.of_length (PolyT.bits hs)) (by fun_prop) (fun x => min_le_right _ _))

abbrev Inputs := ℕ × ℕ × ℕ × ℕ × ℕ

def cells (x : Inputs) :=
  let s := x.2.2.2.1
  let es := (unpack x.2.2.1 x.2.1).map (orient s)
  es.flatMap fun e => es.flatMap fun f =>
    [cell x.1 s e.1, cell x.1 s f.1, cell x.1 s e.2, cell x.1 s f.2]

theorem cells_poly : PolyT cells := by unfold cells orient Prod.swap; dsimp only; fun_prop

private theorem size_horner (acc d b : ℕ) : (d + b*acc).size ≤ acc.size + d.size + b.size + 1 := by
  apply Nat.size_le.mpr
  have ha := Nat.lt_size_self acc
  have hd := Nat.lt_size_self d
  have hb := Nat.lt_size_self b
  let T := 2 ^ (acc.size + d.size + b.size)
  have hd' : d < T := hd.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hx : b*acc ≤ 2^(acc.size+b.size) := by rw [pow_add,mul_comm b acc]; exact Nat.mul_le_mul ha.le hb.le
  have hx' : b*acc ≤ T := hx.trans (Nat.pow_le_pow_right (by decide) (by omega))
  change d + b*acc < 2^(acc.size+d.size+b.size+1); rw [pow_succ]; change d + b*acc < T*2; omega

def pack (b : ℕ) (xs : List ℕ) := xs.reverse.foldl (fun n d => d+b*n) 1

@[fun_prop] theorem pack_poly {α : Type} [Enc α] {b : α → ℕ} {xs : α → List ℕ} (hb : PolyT b) (hx : PolyT xs) : PolyT (fun x => pack (b x) (xs x)) := by
  obtain ⟨s,hs,_,hls⟩ := PolyT.len_bound hx
  obtain ⟨t,ht,_,hlt⟩ := PolyT.len_bound hb
  refine PolyT.foldl_add (g := fun x (acc d : ℕ) => d+b x*acc) (PolyT.reverse hx) (PolyT.const 1) (by fun_prop)
    ⟨fun n => s n+t n+3,(hs.add ht).add (PB.const 3),?_⟩
  intro x c e he
  have he' := (len_le_of_mem (List.mem_reverse.mp he)).trans (hls x)
  have h := size_horner c e (b x)
  have h' := hlt x
  simp only [len_nat] at *; omega

theorem pack_eq (b : ℕ) (xs : List ℕ) : pack b xs = Nat.ofDigits b (xs++[1]) := by
  induction xs with
  | nil => simp [pack]
  | cons hd tl ih => simp [pack,List.reverse_cons,List.foldl_append,Nat.ofDigits_cons,← ih]

def word (x : Inputs) : List Bool := (pack x.2.2.2.2 (cells x)).bits

theorem word_poly : PolyT word := by unfold word; exact PolyT.bits (pack_poly (by fun_prop) cells_poly)

end DetDLP.M13BEndpoint


