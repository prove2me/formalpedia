-- Prove2me | Definitions.Def_DetDLP_S8M_Routes
-- name    : DetDLP_S8M_Routes
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T12:52:14.283638+00:00
-- url     : https://prove2.me/theorems/5917eb6d-4780-4711-a5b7-9c52a990a42f
-- title:
--   Tag 6 EC pair-collision register routes
-- statement:
--   For $m\ge1$, the register bank contains $2m$ factor-point slots, $2m$ conversion records, and $2m-1$ short-Weierstrass addition records. The public seed selects the two hash coefficients for each factor block. Prefix rows read the flag and the two big-endian coordinate words of each point in pair order. `network_iff` characterizes acceptance by the atom rows, conversion rows, the fold pinned at $(\mathrm{true},0,0)$, and the prefix equation. `networkAt_iff` gives the same characterization for a public target triple.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8M_ECAtomSlot
import Definitions.Def_DetDLP_S8M_ECMapRows
import Definitions.Def_DetDLP_S8M_ECFoldRoutes
import Definitions.Def_DetDLP_S8M_ECPairWitness

set_option autoImplicit false

namespace DetDLP.S8M.Routes
open S8H0.RegisterMap

/-- Register bank for interleaved EC inputs, conversion records, and fold steps. -/
def bank (m d e : ℕ) : Shape :=
  .pair (.vec (2 * m) (DetDLP.S8M.ECAtomSlot.slotShape d e))
    (.pair (.vec (2 * m) (DetDLP.S8M.ECMapRows.mapShape d e))
      (.vec (2 * m - 1) (DetDLP.S8N.ECAddRoutes.addShape d e)))

open S8H0 NamedBlocks HashRows ResidueWires GateRoutes RangeRows
open S8G.SeedAndAtomBank (allRows allRows_iff)
variable {m d e : ℕ}
abbrev G (hd : 1 ≤ d) := (w4_M5GraphBounds.graph d hd).nE
abbrev L (i : Fin m) : Fin (2*m) := ⟨i,by omega⟩
abbrev R (i : Fin m) : Fin (2*m) := ⟨m+i,by omega⟩
def idx (j : Fin (2*m)) : Fin m := ⟨j%m,Nat.mod_lt _ (by have := j.isLt; omega)⟩
abbrev A (i : Fin (2*m)) : Path (ECAtomSlot.slotShape d e) (bank m d e) := fun j => .fst (.vec i j)
abbrev M (i : Fin (2*m)) : Path (ECMapRows.mapShape d e) (bank m d e) := fun j => .snd (.fst (.vec i j))
abbrev F : Path (ECFoldRoutes.foldShape (2*m-1) d e) (bank m d e) := fun j => .snd (.snd j)
abbrev TripleW (s : Shape) := Ref s × Word s × Word s
abbrev atomW (i : Fin (2*m)) : TripleW (bank m d e) :=
  (.reg (A i (.fst CurveRows.flag)),word (n:=d) (fun j => A i (.fst (xa (.fst j)))),
    word (n:=d) (fun j => A i (.fst (ya (.fst j)))))
abbrev mapW (i : Fin (2*m)) : TripleW (bank m d e) :=
  (.reg (M i (.fst (.fst .bit))),word (n:=d) (fun j => M i (.fst (.snd (.fst (.fst j))))),
    word (n:=d) (fun j => M i (.fst (.snd (.snd (.fst j))))))
abbrev SeedData (m : ℕ) := Fin m → Bool → ℕ × ℕ

def atomRows (hd : 1 ≤ d) (p T : ℕ) (c : Coeff) (S : SeedData m) (j : Fin (2*m)) : B ((bank m d (G hd)).size+1) :=
  let k := S (idx j)
  ECAtomSlot.slotBlock hd p T c (pub (k false).1) (pub (k false).2) (pub (k true).1) (pub (k true).2) (A j)
def mapRows (hd : 1 ≤ d) (p b2 a1 a3 : ℕ) (j : Fin (2*m)) : B ((bank m d (G hd)).size+1) :=
  let w := atomW j; ECMapRows.mapBlock hd p b2 a1 a3 w.1 w.2.1 w.2.2 (M j)
abbrev first (hm : 1 ≤ m) : Fin (2*m) := ⟨0,by omega⟩
abbrev next (j : Fin (2*m-1)) : Fin (2*m) := ⟨j+1,by have := j.isLt; omega⟩
abbrev Target := Bool × ℕ × ℕ
abbrev pins {s : Shape} (t : Target) : TripleW s := (.pin t.1,pub t.2.1,pub t.2.2)
def foldRows (hd : 1 ≤ d) (hm : 1 ≤ m) (p neg1 three c4 : ℕ) (t : Target) : B ((bank m d (G hd)).size+1) :=
  let a := mapW (first hm); let b := fun j => mapW (next j); let z := pins t
  ECFoldRoutes.foldBlock hd p neg1 three c4 a.1 a.2.1 a.2.2 (fun i => (b i).1) (fun i => (b i).2.1) (fun i => (b i).2.2) z.1 z.2.1 z.2.2 F

def digits (b : ℕ) (j : Fin (2*m)) : List (Ref (bank m d e)) :=
  let w := atomW j; w.1 :: (List.ofFn (fun i : Fin b => w.2.1 i.rev) ++ List.ofFn (fun i : Fin b => w.2.2 i.rev))
def refs (b : ℕ) : List (Ref (bank m d e)) :=
  (List.finRange m).flatMap fun i => digits b (L i) ++ digits b (R i)
def prefixRows (b : ℕ) (η : List Bool) : B ((bank m d e).size+1) :=
  let r := refs (m:=m) (d:=d) (e:=e) b
  rows η.length 1 (fun i _ => r[i.val]?.getD (.pin false)) (fun i v => decide (i.val < r.length ∧ v 0 = η[i]))

theorem prefix_iff (b : ℕ) (η : List Bool) (u : Bits ((bank m d e).size+1)) :
    (prefixRows b η).OK u ↔ ((refs b).map (fun r => r.eval u)).take η.length = η := by
  let r := refs (m:=m) (d:=d) (e:=e) b
  rw [eq_comm (a := List.take ..), ← List.prefix_iff_eq_take,List.prefix_iff_getElem]
  simp only [prefixRows,rows_iff,decide_eq_true_eq,List.length_map,List.getElem_map]; constructor
  · intro h; refine ⟨?_,fun i hi => ?_⟩
    · by_contra! hn; exact Nat.lt_irrefl _ (h ⟨_,hn⟩).1
    · simpa [List.getElem?_eq_getElem (h ⟨i,hi⟩).1] using (h ⟨i,hi⟩).2.symm
  · rintro ⟨hl,h⟩ i; have hi := i.isLt.trans_le hl
    exact ⟨hi,by simpa [List.getElem?_eq_getElem hi] using (h i i.isLt).symm⟩

variable (hd : 1 ≤ d) (hm : 1 ≤ m) (p T : ℕ) (c : Coeff) (S : SeedData m) (b2 neg1 three c4 : ℕ) (η : List Bool)
/-- Only public coefficients, seed words, target words, and prefix bits enter the routing. -/
def networkAt (t : Target) := joinB (allRows _ (atomRows hd p T c S)) <| joinB (allRows (2*m) (mapRows hd p b2 c.a1 c.a3)) <|
  joinB (foldRows hd hm p neg1 three c4 t) (prefixRows (bitLen p) η)
abbrev network := networkAt hd hm p T c S b2 neg1 three c4 η (true,0,0)
theorem networkAt_iff (t : Target) (u : Bits ((bank m d (G hd)).size+1)) :
    (networkAt hd hm p T c S b2 neg1 three c4 η t).OK u ↔
      (∀ i, (atomRows hd p T c S i).OK u) ∧ (∀ i, (mapRows (m:=m) hd p b2 c.a1 c.a3 i).OK u) ∧
      (foldRows hd hm p neg1 three c4 t).OK u ∧ ((refs (bitLen p)).map (fun r => r.eval u)).take η.length = η := by
  simp only [networkAt,joinB_iff,allRows_iff,prefix_iff]
theorem network_iff (u : Bits ((bank m d (G hd)).size+1)) :
    (network hd hm p T c S b2 neg1 three c4 η).OK u ↔
      (∀ i, (atomRows hd p T c S i).OK u) ∧ (∀ i, (mapRows (m:=m) hd p b2 c.a1 c.a3 i).OK u) ∧
      (foldRows hd hm p neg1 three c4 (true,0,0)).OK u ∧ ((refs (bitLen p)).map (fun r => r.eval u)).take η.length = η :=
  networkAt_iff hd hm p T c S b2 neg1 three c4 η _ u
end DetDLP.S8M.Routes


