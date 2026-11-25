-- Prove2me | Definitions.Def_DetDLP_S8N_MomentSignalHash
-- name    : DetDLP_S8N_MomentSignalHash
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T10:17:00.609011+00:00
-- url     : https://prove2.me/theorems/02ff8e05-a5b8-5b23-8b5d-110f823a9fd2
-- title:
--   Signal tables for rows, register words and modular hash circuits
-- statement:
--   Numeric tables identify each row port, repeated block and modular multiplication input. Their lookups track the physical register and run in polynomial time.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, elliptic-curve moment-query compiler.

import Definitions.Def_DetDLP_S8H4_TracksRowsSpec
import Definitions.Def_DetDLP_S8N_Routes_v3

section
set_option autoImplicit false
namespace DetDLP.S8N.MomentSignal

open Groundwork S8H0 RegisterMap NamedBlocks GateRoutes ResidueWires RangeRows HashRows
open S8H4.TracksPoly S8H4.TracksRowsSpec
open S8G.SeedAndAtomBank

abbrev W := ℕ → ℕ
abbrev Table := R
abbrev WordCode {α : Type} [Enc α] (f : α → W) := ∀ {i : α → ℕ}, PolyT i → PolyT fun x => f x (i x)
abbrev PathAt {l s : Shape} (f : Path l s) (off : ℕ) :=
  ∀ a : Addr l, (f a).index.val = off+a.index.val
abbrev WordAt {s : Shape} (f : W) (a : Word s) := ∀ i : ℕ, f i = (a i).source.val

def rowTable (n ar : ℕ) (name : ℕ → ℕ → ℕ) : R :=
  (n*ar,fun i => name (i/ar) (i%ar))

def tileTable (n edges : ℕ) (table : ℕ → R) : R :=
  (n*edges,fun i => (table (i/edges)).2 (i%edges))

theorem rowTracks {s : Shape} {n ar : ℕ} {name : ℕ → ℕ → ℕ} {r : Fin n → Fin ar → Ref s}
    (test) (H : ∀ i j, name i.val j.val = (r i j).source.val) :
    Tracks (rowTable n ar name) (rows n ar r test) :=
  ⟨rfl,fun i => H (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2⟩

private theorem manyTiles {s : Shape} (n edges : ℕ) (table : ℕ → R)
    (rows : Fin (n+1) → B (s.size+1)) (hlen : ∀ j, (table j).1 = edges)
    (H : ∀ j : Fin (n+1), Tracks (table j.val) (rows j)) :
    Tracks (tileTable (n+1) edges table) (many n rows) := by
  induction n generalizing table with
  | zero =>
    have h := H 0
    have sz : (rows 0).core.A.ne = edges := h.1.symm.trans (hlen 0)
    refine ⟨by simp [tileTable,sz,many],?_⟩
    intro i
    have hlt : i.val < edges := sz ▸ i.isLt
    change (table (i.val/edges)).2 (i.val%edges) = _
    rw [Nat.div_eq_of_lt hlt,Nat.mod_eq_of_lt hlt]
    exact h.2 i
  | succ n ih =>
    have first := H 0
    have p : (rows 0).core.A.ne = edges := first.1.symm.trans (hlen 0)
    have rest := ih (fun j => table (j+1)) (fun j => rows j.succ) (fun j => hlen (j+1)) (fun j => H j.succ)
    have joined := cat_ok first rest
    refine ⟨?_,?_⟩
    · apply Eq.trans _ joined.1
      change (n+1+1)*edges = (table 0).1 + (n+1)*edges
      rw [hlen,Nat.succ_mul,Nat.add_comm]
    · intro i
      change Fin ((rows 0).core.A.ne+(many n (fun j => rows j.succ)).core.A.ne) at i
      induction i using Fin.addCases with
      | left i =>
        have lt : i.val < edges := p ▸ i.isLt
        simp only [many,tileTable,joinB,Fin.addCases_left,Fin.val_castAdd,Nat.div_eq_of_lt lt,Nat.mod_eq_of_lt lt]
        exact first.2 i
      | right i =>
        have pos : 0 < edges := by
          by_contra h
          have eq : edges = 0 := by omega
          have lim : i.val < (n+1)*edges := lt_of_lt_of_eq i.isLt rest.1.symm
          simp [eq] at lim
        simp only [many,tileTable,joinB,Fin.addCases_right,Fin.val_natAdd,p,Nat.add_div_left _ pos,Nat.add_mod_left]
        exact rest.2 i

theorem tileTracks {s : Shape} (n edges : ℕ) (table : ℕ → R)
    (bs : Fin n → B (s.size+1)) (hlen : ∀ j, (table j).1 = edges)
    (h : ∀ j : Fin n, Tracks (table j.val) (bs j)) :
    Tracks (tileTable n edges table) (allRows n bs) := by
  cases n with
  | zero => exact ⟨Nat.zero_mul _,fun i => Fin.elim0 i⟩
  | succ n => exact manyTiles n edges table bs hlen h

theorem catGood {α : Type} [Enc α] {a b : α → R} (h : Good a) (j : Good b) :
    Good fun x => cat (a x) (b x) :=
  ⟨PolyT.add h.1 j.1, fun _i hi => PolyT.ite' (PolyT.decide_lt hi h.1)
    (h.2 _ hi) (j.2 _ (PolyT.sub hi h.1))⟩

theorem rowGood {α : Type} [Enc α] {n ar : α → ℕ} {f : α → ℕ → ℕ → ℕ}
    (hn : PolyT n) (har : PolyT ar) (hf : ∀ {i j : α → ℕ}, PolyT i → PolyT j → PolyT (fun x => f x (i x) (j x))) :
    Good fun x => rowTable (n x) (ar x) (f x) :=
  ⟨PolyT.mul hn har,fun _i hi => hf (PolyT.div hi har) (PolyT.mod hi har)⟩

theorem tileGood {α : Type} [Enc α] {n edges : α → ℕ} {f : α → ℕ → R}
    (hn : PolyT n) (he : PolyT edges) (hf : ∀ (j : α → ℕ), PolyT j → Good fun x => f x (j x)) :
    Good fun x => tileTable (n x) (edges x) (f x) :=
  ⟨PolyT.mul hn he,fun _i hi => (hf _ (PolyT.div hi he)).2 _ (PolyT.mod hi he)⟩

theorem wordGood {α : Type} [Enc α] {d tip off : α → ℕ}
    (hd : PolyT d) (ht : PolyT tip) (ho : PolyT off) : WordCode fun x => S8H4.TracksPoly.pad (d x) (tip x) (off x) :=
  fun hi => PolyT.ite' (PolyT.decide_lt hi hd) (PolyT.add ho hi) ht

theorem pathWord {n : ℕ} {s : Shape} (f : Path (.word n) s) (off : ℕ) (h : PathAt f off) :
    WordAt (S8H4.TracksPoly.pad n s.size off) (word f) := by
  intro i
  simp only [S8H4.TracksPoly.pad,word,padded_val]
  split
  · rename_i lt
    exact (h (.word ⟨i,lt⟩)).symm
  · rfl

theorem pathFst {l r s : Shape} {f : Path (.pair l r) s} {off : ℕ} (h : PathAt f off) :
    PathAt (fun a : Addr l => f (.fst a)) off := fun a => h (.fst a)

theorem pathSnd {l r s : Shape} {f : Path (.pair l r) s} {off : ℕ} (h : PathAt f off) :
    PathAt (fun a : Addr r => f (.snd a)) (off+l.size) := by
  intro a
  rw [h (.snd a)]
  exact (Nat.add_assoc _ _ _).symm

theorem pathVec {n : ℕ} {l s : Shape} {f : Path (.vec n l) s} {off : ℕ} (h : PathAt f off) (j : Fin n) :
    PathAt (fun a : Addr l => f (.vec j a)) (off+l.size*j.val) := by
  intro a
  rw [h (.vec j a)]
  change off+(a.index.val+l.size*j.val) = off+l.size*j.val+a.index.val
  omega

end DetDLP.S8N.MomentSignal
end

section
set_option autoImplicit false
namespace DetDLP.S8N.MomentSignal
open Groundwork S8H0 RegisterMap NamedBlocks GateRoutes S8H4.TracksPoly S8H4.TracksRowsSpec

def vectorRows {k : ℕ} (n : ℕ) (v : Fin k → W) : R :=
  rowTable n k fun i j => (List.ofFn fun z => v z i).getD j 0

theorem vectorTracks {s : Shape} {k n : ℕ} (v : Fin k → W) (f : Fin n → Fin k → Ref s)
    (t) (hf : ∀ j i, v j i.val = (f i j).source.val) : Tracks (vectorRows n v) (rows n k f t) := by
  apply rowTracks
  intro i j
  rw [List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]
  exact hf j i

private theorem pList {α : Type} [Enc α] {n : ℕ} (f : Fin n → α → ℕ) (h : ∀ j, PolyT (f j)) :
    PolyT fun x => List.ofFn fun j => f j x := by
  induction n with
  | zero => simpa only [List.ofFn_zero] using (PolyT.const (α:=α) ([] : List ℕ))
  | succ n ih =>
    rw [show (fun x => List.ofFn fun j => f j x) =
        (fun x => f 0 x :: List.ofFn fun j => f j.succ x) by funext x; apply List.ofFn_succ]
    exact P2M_Groundwork_PolyT_cons__3a60f43a3b86 (h 0) (ih (fun j => f j.succ) (fun j => h j.succ))

theorem vectorGood {α : Type} [Enc α] {k : ℕ} {n : α → ℕ} {v : α → Fin k → W}
    (hn : PolyT n) (hf : ∀ j, WordCode fun x => v x j) : Good fun x => vectorRows (n x) (v x) := by
  apply rowGood hn (PolyT.const _)
  intro i j hi hj
  exact PolyT.getD (pList (fun z x => v x z (i x)) (fun z => hf z hi)) hj (PolyT.const 0)

end DetDLP.S8N.MomentSignal
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace DetDLP.S8N.MomentSignal

open Groundwork S8H0 RegisterMap NamedBlocks GateRoutes ResidueWires RangeRows HashRows
open S8H4.TracksPoly S8H4.TracksRowsSpec S8M.ECMapRows
open private gw fstP sndP rwrd refw from Definitions.Def_DetDLP_S8M_ECMapRows

def triSize (d : ℕ) := 3*d+1
def runSize (d e : ℕ) := 11*d+2*e+3
def auxSize (d : ℕ) := 5*d+3

theorem triSize_eq (d : ℕ) : (triple d).size = triSize d := by
  simp only [triple,Shape.size,triSize]; omega
theorem runSize_eq (d e : ℕ) : (run d e).size = runSize d e := by
  simp only [run,RegisterMap.mul,Shape.size,triSize_eq,triSize,runSize]; omega
theorem auxSize_eq (d : ℕ) : (auxShape d).size = auxSize d := by
  simp only [auxShape,Shape.size,auxSize]; omega

def checkTile (d tip off : ℕ) : R :=
  plusRows (d+1) (S8H4.TracksPoly.pad d tip off) (S8H4.TracksPoly.pad d tip (off+d))
    (fun _ => tip) (fun i => off+d+d+i)

theorem checkTracks {s : Shape} {d : ℕ} (p off : ℕ) (f : Path (triple d) s) (hf : PathAt f off) :
    Tracks (checkTile d s.size off) (checker p f) := by
  apply plus_ok
  intro j
  refine ⟨?_,?_,rfl,?_⟩
  · simp only [S8H4.TracksPoly.pad,rpad_val]
    split
    · rename_i lt
      exact (hf (.fst (.word ⟨j.val,lt⟩))).symm
    · rfl
  · simp only [S8H4.TracksPoly.pad,rpad_val]
    split
    · change _ = (f _).index.val
      erw [hf]
      change off+d+j.val = off + (d+j.val)
      omega
    · rfl
  · change _ = (f _).index.val
    erw [hf]
    change _ = off + (d + (d + j.val))
    omega

def hashTile (d e tip off : ℕ) (a x b : W) : R :=
  let r := off + triSize d
  let q := r + triSize d
  let m := q + d
  let m' := m+(2*d+e)
  let u := off + runSize d e
  let pad := S8H4.TracksPoly.pad
  let p1 := pad (2*d) tip m
  let p2 := pad (2*d) tip m'
  let sum := pad (d+1) tip (u+2*d)
  cat (cat (prodR d e (m+2*d) a x p1) (prodR d e (m'+2*d) (pad d tip q) (fun _ => tip) p2))
    (cat (plusRows (2*d) p2 (pad d tip r) p1 (u+·))
      (cat (plusRows (d+1) (pad d tip r) b sum (u+2*d+(d+1)+·))
        (plusRows (d+1) (pad d tip off) (fun _ => m'+(2*d+e)) sum (u+2*d+(d+1)+(d+1)+·))))

theorem hashTracks {s : Shape} {d : ℕ} (hd : 1 ≤ d) (p off : ℕ)
    (f : Path (slot d (w4_M5GraphBounds.graph d hd).nE) s) (hf : PathAt f off)
    (a x b : W) (A X B : Word s) (ha : WordAt a A) (hx : WordAt x X) (hb : WordAt b B) :
    Tracks (hashTile d (w4_M5GraphBounds.graph d hd).nE s.size off a x b)
      (HashRows.block p (gw hd p A X B f)) := by
  unfold hashTile HashRows.block
  refine cat_ok (cat_ok (prod_ok ?_ ?_) (prod_ok ?_ ?_))
    (cat_ok (plus_ok _ ?_) (cat_ok (plus_ok _ ?_) (plus_ok _ ?_)))
  all_goals intro j; repeat' apply And.intro
  all_goals first | exact ha _ | exact hx _ | exact hb _ | rfl | skip
  all_goals dsimp only [gw,fstP,sndP,rwrd,refw,word]
  all_goals try simp only [rpad_val,padded_val,S8H4.TracksPoly.pad]
  all_goals try split <;> try simp_all only [↓reduceDIte,↓reduceIte]
  all_goals first | rfl | skip
  all_goals try dsimp only [Ref.source,Fin.castSucc,Fin.castAdd,Fin.last]
  all_goals try exact False.elim (by apply ‹¬ _›; exact j.isLt)
  all_goals erw [hf]
  all_goals try dsimp only [Addr.index,Fin.castSucc,Fin.castAdd,Fin.natAdd,Fin.castLE,run,RegisterMap.mul,
    auxShape,triple,Shape.size,runSize,triSize]
  all_goals first | rfl | omega

end DetDLP.S8N.MomentSignal
end

section
set_option autoImplicit false
namespace DetDLP.S8N.MomentSignal
open Groundwork S8H4.TracksPoly
open private plusP prodP from Definitions.Def_DetDLP_S8H4_TracksPoly

theorem checkGood {α : Type} [Enc α] {d tip off : α → ℕ}
    (hd : PolyT d) (ht : PolyT tip) (ho : PolyT off) : Good fun x => checkTile (d x) (tip x) (off x) := by
  exact @plusP α _ (fun z => d z+1)
    (fun z => S8H4.TracksPoly.pad (d z) (tip z) (off z))
    (fun z => S8H4.TracksPoly.pad (d z) (tip z) (off z+d z))
    (fun z _ => tip z) (fun z i => off z+d z+d z+i)
    (PolyT.add hd (PolyT.const 1)) (wordGood hd ht ho)
    (wordGood hd ht (PolyT.add ho hd)) (fun _ => ht)
    (fun hi => PolyT.add (PolyT.add (PolyT.add ho hd) hd) hi)

theorem hashGood {α : Type} [Enc α] {d e tip off : α → ℕ} {a x b : α → W}
    (hd : PolyT d) (he : PolyT e) (ht : PolyT tip) (ho : PolyT off)
    (ha : WordCode a) (hx : WordCode x) (hb : WordCode b) :
    Good fun z => hashTile (d z) (e z) (tip z) (off z) (a z) (x z) (b z) := by
  have one := PolyT.const (α:=α) 1
  have twod := PolyT.mul (PolyT.const 2) hd
  have d1 := PolyT.add hd one
  have tri := PolyT.add (PolyT.mul (PolyT.const 3) hd) one
  have run := PolyT.add (PolyT.add (PolyT.mul (PolyT.const 11) hd) (PolyT.mul (PolyT.const 2) he)) (PolyT.const 3)
  have r := PolyT.add ho tri
  have q := PolyT.add r tri
  have m := PolyT.add q hd
  have d2e := PolyT.add twod he
  have m' := PolyT.add m d2e
  have u := PolyT.add ho run
  have sum := PolyT.add u twod
  have p1 := @wordGood _ _ _ _ _ twod ht m
  have p2 := @wordGood _ _ _ _ _ twod ht m'
  have rs := @wordGood _ _ _ _ _ hd ht r
  have ss := @wordGood _ _ _ _ _ d1 ht sum
  exact catGood
    (catGood (prodP hd he (PolyT.add m twod) ha hx p1)
      (prodP hd he (PolyT.add m' twod) (wordGood hd ht q) (fun _ => ht) p2))
    (catGood (plusP twod p2 rs p1 (fun hi => PolyT.add u hi))
      (catGood (plusP d1 rs hb ss (fun hi => PolyT.add (PolyT.add sum d1) hi))
        (plusP d1 (wordGood hd ht ho) (fun _ => PolyT.add m' d2e) ss
          (fun hi => PolyT.add (PolyT.add (PolyT.add sum d1) d1) hi))))

end DetDLP.S8N.MomentSignal
end


