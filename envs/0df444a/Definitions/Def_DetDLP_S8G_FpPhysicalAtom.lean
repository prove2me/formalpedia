-- Prove2me | Definitions.Def_DetDLP_S8G_FpPhysicalAtom
-- name    : DetDLP_S8G_FpPhysicalAtom
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T07:32:19.58115+00:00
-- url     : https://prove2.me/theorems/fa3a9552-0f89-4965-af85-e13e58f3e38b
-- title:
--   Single physical-wire Fp hash atom
-- statement:
--   A Lean 4 physical layout combining one linked Fp hash stage with an eight-strip adder layout. It exposes designated input wires and uses link equalities to connect selected buses. The current module provides a parameter-only factor test and an edge-count bound.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8L_FpPairPhysicalHash

set_option autoImplicit false
namespace DetDLP.S8G.FpPhysicalAtom
open S8C S8J S8L.FpPair S8L.FpPair.Stage S8L.FpPair.Stage.Links w4_M5PortTensor

/-- Eight adjacent strips: successor of the slope, positive input, three strict
comparisons (input, output, remainder), two hash sums and the reduction flag. -/
def base (d : ℕ) (hd : 1 ≤ d) := join (Links.layout hd) (AddLayout.layout (8*(d+1)))
variable {d : ℕ} (hd : 1 ≤ d)
def col (j : Fin 8) (i : Fin (d+1)) : Fin (8*(d+1)) := finProdFinEquiv (j,i)
def port (j : Fin 8) (l : Fin 4) (i : Fin (d+1)) : Fin (base d hd).nb :=
  Fin.natAdd _ (AddLayout.reg (col j i) l)
def st (i : Bit hd) : Fin (base d hd).nb := Fin.castAdd _ i

def ties (k : Fin (3*d+5*(d+1))) : Fin (base d hd).nb × Fin (base d hd).nb :=
  Fin.addCases (fun k : Fin (3*d) =>
    let ji : Fin 3 × Fin d := finProdFinEquiv.symm k
    let i := ji.2
    match ji.1.val with
    | 0 => (port hd 0 2 i.castSucc, st hd (mul1 hd (inPos false i)))
    | 1 => (port hd 1 2 i.castSucc, st hd (mul1 hd (inPos true i)))
    | _ => (port hd 5 0 i.castSucc, st hd (addr hd ⟨i.val,by omega⟩ 1)))
    (fun k : Fin (5*(d+1)) =>
      let ji : Fin 5 × Fin (d+1) := finProdFinEquiv.symm k
      let i := ji.2
      match ji.1.val with
      | 0 => (port hd 1 2 i, port hd 2 0 i)
      | 1 => (port hd 3 0 i, port hd 6 0 i)
      | 2 => (port hd 4 0 i, port hd 5 0 i)
      | 3 => (port hd 5 2 i, port hd 6 2 i)
      | _ => (port hd 7 1 i, port hd 6 1 i)) k

def layout (d : ℕ) (hd : 1 ≤ d) := links (base d hd) (fun k => (ties hd k).1) (fun k => (ties hd k).2)
def aWire (i : Fin d) : Fin (layout d hd).nb := port hd 0 0 i.castSucc
def bWire (i : Fin d) : Fin (layout d hd).nb := port hd 5 1 i.castSucc
def xWire (i : Fin d) : Fin (layout d hd).nb := port hd 1 2 i.castSucc

/-- Column zero starts a fresh carry chain in each strip; the top carry must
vanish. Strip seven instead copies its flag to the next column's carry port. -/
def rowTest (d p T : ℕ) : w3_factorTest (AddLayout.layout (8*(d+1))) := fun g f =>
  let ji : Fin 8 × Fin (d+1) := finProdFinEquiv.symm g
  let j := ji.1.val
  let i := ji.2.val
  let get (l : Fin 5) := f ⟨AddLayout.pos g l,AddLayout.col_pos ..⟩
  let a := get 0; let b := get 1; let z := get 2; let c := get 3
  if j=7 then decide (a=c ∧ z=false ∧ (i≠0 → a=get 4) ∧ b=(a && p.testBit i))
  else
    let cin := if i=0 then decide (j<5) else get 4
    decide (a.toNat+b.toNat+cin.toNat=z.toNat+2*c.toNat ∧ (i=d → c=false) ∧
      (j<2 → b=false ∧ (i=d → z=false)) ∧ (j=0 ∧ i=d → a=false) ∧
      (j=2 ∨ j=4 → z=p.testBit i) ∧ (j=3 → z=T.testBit i) ∧
      (j=5 ∧ i=d → a=false ∧ b=false))

noncomputable def stageTest (p : ℕ) : w3_factorTest (Links.layout hd) :=
  atPins (atPins (linkedTests hd) (fun i => mul2 hd (inPos true i)) (fun i => p.testBit i.val))
    (fun i : Fin d => addr hd ⟨d+i.val,by omega⟩ 1) (fun _ => false)
noncomputable def test (d : ℕ) (hd : 1 ≤ d) (p T : ℕ) : w3_factorTest (layout d hd) :=
  linksTest (fun k => (ties hd k).1) (fun k => (ties hd k).2) (joinTest (stageTest hd p) (rowTest d p T))

theorem accept_iff (p T : ℕ) (w : Vec (layout d hd).nb) : Accept _ (test d hd p T) w ↔
    (Accept _ (stageTest hd p) (w ∘ Fin.castAdd _) ∧ Accept _ (rowTest d p T) (w ∘ Fin.natAdd _)) ∧
    ∀ k, w (ties hd k).1 = w (ties hd k).2 := by
  unfold test; erw [links_iff,join_iff]; rfl

theorem edges : (layout d hd).ne < 12000*(d+3) := by
  have h := Links.edges hd
  change (Links.layout hd).ne + (8*(d+1))*5 + ((3*d+5*(d+1))+(3*d+5*(d+1))) < _
  omega

end DetDLP.S8G.FpPhysicalAtom

abbrev DetDLP_S8G_FpPhysicalAtom := DetDLP.S8G.FpPhysicalAtom.layout


