-- Prove2me | Definitions.Def_DetDLP_S8O_ECAddTile
-- name    : DetDLP_S8O_ECAddTile
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T07:39:24.852857+00:00
-- url     : https://prove2.me/theorems/5b18a2b8-ed73-4b3f-bf7d-7e2e2789f0f0
-- title:
--   Short-Weierstrass addition tile layout and evaluator
-- statement:
--   ## Short-Weierstrass addition tile layout and evaluator\n\nThis development formalizes a cyclic, columnar Boolean-circuit layout for short-Weierstrass elliptic-curve point addition. Each column carries 22 registers and reads five registers from its predecessor. The selector propagates input infinity flags, selects the chord or tangent slope branch, handles inverse-zero certificates, and constrains the output coordinates bit by bit.\n\nThe arithmetic bank is assembled from fourteen copies of the EC map tile's arithmetic atom. These copies encode the certificate computations for inverses, differences, chord and tangent numerators, squares, slopes, and output coordinates. The formal specification proves the layout and code model correspondence, uniformity, edge and shape bounds, and equivalence between acceptance of the encoded circuit and the addition checks.\n\nA local selector evaluator rejects malformed port words and evaluates a 27-bit selector word; its polynomial-time property is formalized. The branch selector's correctness is stated as equivalence with the certified inverse conditions and the expected point-addition output, including infinity and inverse-point cases.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8O_ECMapTile

/-! S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4 & Section 3.1–3.2, Lemma 2.4 & Theorem 3.1 (pp. 9–13). -/
set_option autoImplicit false
namespace DetDLP.S8O.ECAddTile
open S8H.PointAddresses S8J TileColumns

/-- The first five registers carry i,j,bx,by,outInf around the word. Registers
5–10 are the three coordinate pairs, 11–13 are chord,tangent,slope, 14–15
are the computed result, and 16–21 hold both inverse triples (u,v,u*v). -/
def select (one : Bool) (a : Fin 27 → Bool) :=
  let i := a 0; let j := a 1; let bx := a 2; let by' := a 3
  let inf := if i then j else if j then false else bx && by'
  let coord (p q r : Bool) := if i then q else if j then p else if bx && by' then false else r
  let inv (b u v prod : Bool) := if b then !u && !v else prod == one
  decide (i = a 22 ∧ j = a 23 ∧ bx = a 24 ∧ by' = a 25 ∧ a 4 = a 26 ∧
    a 4 = inf ∧ a 9 = coord (a 5) (a 7) (a 14) ∧ a 10 = coord (a 6) (a 8) (a 15) ∧
    a 13 = (if !i && !j && !bx then a 11 else if !i && !j && bx && !by' then a 12 else false) ∧
    inv bx (a 16) (a 17) (a 18) ∧ inv by' (a 19) (a 20) (a 21))

def selectors (d : ℕ) := TileColumns.layout d 22 5 (by decide)
def selectorTest (d : ℕ) : w3_factorTest (selectors d) := fun i x =>
  select (decide (i.val = 0)) (fun j => x ⟨idx i j,row_idx i j⟩)

def layout {d : ℕ} (hd : 1 ≤ d) := join (selectors d) (copies (ECMapTile.atom hd) 14)
def code (d : ℕ) := sum (TileColumns.code 22 5 d) (copiesCode (ECMapTile.atomCode d) 14)
theorem models {d : ℕ} (hd : 1 ≤ d) : Models (code d) (layout hd) :=
  sum_spec (TileColumns.models ..) (copies_spec (ECMapTile.atom_models hd) _)
theorem uniform : Uniform code := sum_poly (TileColumns.uniform ..) (copies_poly ECMapTile.atom_uniform _)
theorem edges {d : ℕ} (hd : 1 ≤ d) : (layout hd).ne < 76000*(d+3) := by
  change d*27 + (copies (ECMapTile.atom hd) 14).ne < _; rw [copies_ne]
  change _ + 15*((HashGateLayout.layout d hd).ne + (d+1)*5) < _
  have := HashGateLayout.edges hd; omega

theorem shape {d : ℕ} (hd : 1 ≤ d) : Shape (layout hd) (HashGateLayout.degreeCap d) 2 :=
  join_shape (TileColumns.shape (by decide) (ECMapTile.cap_large d)) (copies_shape (ECMapTile.atom_shape hd) _)

def reg {d : ℕ} (hd : 1 ≤ d) (i : Fin d) (j : Fin 22) : Fin (layout hd).nb := Fin.castAdd _ (idx i j)
def inPInf {d : ℕ} (hd : 1 ≤ d) := reg hd ⟨0,hd⟩ 0
def inQInf {d : ℕ} (hd : 1 ≤ d) := reg hd ⟨0,hd⟩ 1
def outRInf {d : ℕ} (hd : 1 ≤ d) := reg hd ⟨0,hd⟩ 4
def inPX {d : ℕ} (hd : 1 ≤ d) (i : Fin d) := reg hd i 5
def inPY {d : ℕ} (hd : 1 ≤ d) (i : Fin d) := reg hd i 6
def inQX {d : ℕ} (hd : 1 ≤ d) (i : Fin d) := reg hd i 7
def inQY {d : ℕ} (hd : 1 ≤ d) (i : Fin d) := reg hd i 8
def outRX {d : ℕ} (hd : 1 ≤ d) (i : Fin d) := reg hd i 9
def outRY {d : ℕ} (hd : 1 ≤ d) (i : Fin d) := reg hd i 10

open S8H.ECPointArithmetic S8K.ECAddArithmetic
variable {p : ℕ} [Fact p.Prime]
abbrev H (p : ℕ) := ECAddLayout.GateAux p
abbrev Aux (p : ℕ) := (H p × (H p × Unit) × H p × (H p × Unit) × H p × H p × H p × H p × H p × H p × H p × H p × H p × H p × H p × Unit) × Unit

noncomputable def tests (E : WeierstrassCurve (ZMod p)) (P Q : Coords p) (c : AddCert p) :
    w3_factorTest (layout (Nat.succ_pos (bitLen p))) :=
  let (i,x,y) := P; let (j,z,v) := Q
  let (ux,bx,uy,by₁,dy,chord,sq,num,tan,lsq,tx,X,dx,ty,Y,_) := c
  let l := if !i && !j && !bx.1 then chord.1 else if !i && !j && bx.1 && !by₁.1 then tan.1 else 0
  joinTest (selectorTest _) <|
    joinTest (ECMapTile.atomTest (-1) x ux) <|
    joinTest (ECMapTile.atomTest (ux.1) bx.2.1 bx.2.2) <|
    joinTest (ECMapTile.atomTest (1) y uy) <|
    joinTest (ECMapTile.atomTest (uy.1) by₁.2.1 by₁.2.2) <|
    joinTest (ECMapTile.atomTest (-1) y dy) <|
    joinTest (ECMapTile.atomTest (dy.1) bx.2.1 chord) <|
    joinTest (ECMapTile.atomTest (x) x sq) <|
    joinTest (ECMapTile.atomTest (3) sq.1 num) <|
    joinTest (ECMapTile.atomTest (num.1) by₁.2.1 tan) <|
    joinTest (ECMapTile.atomTest (l) l lsq) <|
    joinTest (ECMapTile.atomTest (-1) x tx) <|
    joinTest (ECMapTile.atomTest (-1) z X) <|
    joinTest (ECMapTile.atomTest (-1) X.1 dx) <|
    joinTest (ECMapTile.atomTest (l) dx.1 ty) <|
    ECMapTile.atomTest (-1) y Y

/-- The columns in the branch bank in physical register order. -/
def selBits (P Q out : Coords p) (c : AddCert p) : Fin (width p * 22) → Bool := fun addr =>
  let (i,x,y) := P; let (j,z,v) := Q
  let (ux,bx,uy,by₁,dy,chord,sq,num,tan,lsq,tx,X,dx,ty,Y,_) := c
  let l := if !i && !j && !bx.1 then chord.1 else if !i && !j && bx.1 && !by₁.1 then tan.1 else 0
  let (u,jj) := finProdFinEquiv.symm addr
  let atBit (a : ZMod p) := a.val.testBit u
  ![i,j,bx.1,by₁.1,out.1,atBit x,atBit y,atBit z,atBit v,atBit out.2.1,atBit out.2.2,
    atBit chord.1,atBit tan.1,atBit l,atBit X.1,atBit Y.1,atBit ux.1,atBit bx.2.1,atBit bx.2.2.1,
    atBit uy.1,atBit by₁.2.1,atBit by₁.2.2.1] jj

def encode (E : WeierstrassCurve (ZMod p)) (P Q out : Coords p) (c : AddCert p) (w : Aux p) :
    Fin (layout (Nat.succ_pos (bitLen p))).nb → Bool :=
  let (i,x,y) := P; let (j,z,v) := Q
  let (ux,bx,uy,by₁,dy,chord,sq,num,tan,lsq,tx,X,dx,ty,Y,_) := c
  let ((a,b,c₁,e,f,g,h,j₁,k,m,n,q,r,s,t,_),_) := w
  Fin.append (selBits P Q out c) <|
    Fin.append (ECMapTile.atomBits (z) ux a) <|
    Fin.append (ECMapTile.atomBits (0) bx.2.2 b.1) <|
    Fin.append (ECMapTile.atomBits (v) uy c₁) <|
    Fin.append (ECMapTile.atomBits (0) by₁.2.2 e.1) <|
    Fin.append (ECMapTile.atomBits (v) dy f) <|
    Fin.append (ECMapTile.atomBits (0) chord g) <|
    Fin.append (ECMapTile.atomBits (0) sq h) <|
    Fin.append (ECMapTile.atomBits (-27*E.c₄) num j₁) <|
    Fin.append (ECMapTile.atomBits (0) tan k) <|
    Fin.append (ECMapTile.atomBits (0) lsq m) <|
    Fin.append (ECMapTile.atomBits (lsq.1) tx n) <|
    Fin.append (ECMapTile.atomBits (tx.1) X q) <|
    Fin.append (ECMapTile.atomBits (x) dx r) <|
    Fin.append (ECMapTile.atomBits (0) ty s) <|
    ECMapTile.atomBits (ty.1) Y t

def eqWord (x y : ZMod p) := ∀ i : Fin (width p), x.val.testBit i = y.val.testBit i
def invWords (u : ZMod p) (b : ZeroInvCert p) := if b.1 then eqWord u 0 ∧ eqWord b.2.1 0 else eqWord b.2.2.1 1
def finalWords (a b : Coords p) := a.1 = b.1 ∧ eqWord a.2.1 b.2.1 ∧ eqWord a.2.2 b.2.2

def branchOK (P Q out : Coords p) (c : AddCert p) :=
  let (i,x,y) := P; let (j,_,_) := Q
  let (ux,bx,uy,by₁,_,_,_,_,_,_,_,X,_,_,Y,_) := c
  invWords ux.1 bx ∧ invWords uy.1 by₁ ∧ finalWords out
    (if i then Q else if j then (false,x,y) else if bx.1 && by₁.1 then (true,0,0) else (false,X.1,Y.1))

private theorem one_bit (j : ℕ) : (1 : ZMod p).val.testBit j = decide (j = 0) := by
  have h := (Fact.out : p.Prime).one_lt
  have h1 : (1 : ZMod p).val = 1 := by simpa using (ZMod.val_natCast_of_lt h)
  rw [h1]; cases j with
  | zero => decide
  | succ j => rw [Nat.testBit_succ]; simp

set_option maxHeartbeats 2200000 in
theorem selBits_iff (P Q out : Coords p) (c : AddCert p) :
    Accept _ (selectorTest _) (selBits P Q out c) ↔ branchOK P Q out c := by
  rcases P with ⟨i,x,y⟩; rcases Q with ⟨j,z,v⟩
  rcases c with ⟨ux,⟨bx,iv,pr⟩,uy,⟨by₁,iv',pr'⟩,dy,chord,sq,num,tan,lsq,tx,X,dx,ty,Y,e⟩
  unfold Accept selectorTest; change (∀ u : Fin (width p), select (decide (u.val = 0)) (fun k => selBits _ _ _ _ (bit (by decide : 5 ≤ 22) (idx u k))) = true) ↔ _
  simp only [select,bit_idx, decide_eq_true_eq]
  cases i <;> cases j <;> cases bx <;> cases by₁ <;>
    norm_num [selBits,idx,branchOK,finalWords,invWords,eqWord,one_bit,forall_and,and_comm,and_left_comm,and_assoc]

set_option maxHeartbeats 2600000 in
theorem encode_iff (E : WeierstrassCurve (ZMod p)) (P Q out : Coords p) (c : AddCert p) (w : Aux p) :
    Accept _ (tests E P Q c) (encode E P Q out c w) ↔ (ECAddLayout.addChecks E P Q out c).bits w := by
  rcases P with ⟨i,x,y⟩; rcases Q with ⟨j,z,v⟩
  rcases c with ⟨ux,bx,uy,by₁,dy,chord,sq,num,tan,lsq,tx,X,dx,ty,Y,ee⟩
  rcases w with ⟨⟨a,b,c₁,e,f,g,h,j₁,k,m,n,q,r,s,t,ww⟩,zz⟩
  let l := if !i && !j && !bx.1 then chord.1 else if !i && !j && bx.1 && !by₁.1 then tan.1 else 0
  let br := selBits_iff (i,x,y) (j,z,v) out (ux,bx,uy,by₁,dy,chord,sq,num,tan,lsq,tx,X,dx,ty,Y,ee)
  have h14 := ECMapTile.atomBits_iff (-1) y (ty.1) Y t
  have h13 := (HashGateLayout.joined ..).trans ((ECMapTile.atomBits_iff (l) dx.1 (0) ty s).and h14)
  have h12 := (HashGateLayout.joined ..).trans ((ECMapTile.atomBits_iff (-1) X.1 (x) dx r).and h13)
  have h11 := (HashGateLayout.joined ..).trans ((ECMapTile.atomBits_iff (-1) z (tx.1) X q).and h12)
  have h10 := (HashGateLayout.joined ..).trans ((ECMapTile.atomBits_iff (-1) x (lsq.1) tx n).and h11)
  have h9 := (HashGateLayout.joined ..).trans ((ECMapTile.atomBits_iff (l) l (0) lsq m).and h10)
  have h8 := (HashGateLayout.joined ..).trans ((ECMapTile.atomBits_iff (num.1) by₁.2.1 (0) tan k).and h9)
  have h7 := (HashGateLayout.joined ..).trans ((ECMapTile.atomBits_iff (3) sq.1 (-27*E.c₄) num j₁).and h8)
  have h6 := (HashGateLayout.joined ..).trans ((ECMapTile.atomBits_iff (x) x (0) sq h).and h7)
  have h5 := (HashGateLayout.joined ..).trans ((ECMapTile.atomBits_iff (dy.1) bx.2.1 (0) chord g).and h6)
  have h4 := (HashGateLayout.joined ..).trans ((ECMapTile.atomBits_iff (-1) y (v) dy f).and h5)
  have h3 := (HashGateLayout.joined ..).trans ((ECMapTile.atomBits_iff (uy.1) by₁.2.1 (0) by₁.2.2 e.1).and h4)
  have h2 := (HashGateLayout.joined ..).trans ((ECMapTile.atomBits_iff (1) y (v) uy c₁).and h3)
  have h1 := (HashGateLayout.joined ..).trans ((ECMapTile.atomBits_iff (ux.1) bx.2.1 (0) bx.2.2 b.1).and h2)
  have h0 := (HashGateLayout.joined ..).trans ((ECMapTile.atomBits_iff (-1) x (z) ux a).and h1)
  refine ((HashGateLayout.joined ..).trans (br.and h0)).trans ?_
  constructor
  · rintro ⟨⟨u,v',o⟩,A,B,C,D,F,G,I,J,K,L,M,N,O,R,S⟩
    exact ⟨⟨A,⟨B,u⟩,C,⟨D,v'⟩,F,G,I,J,K,L,M,N,O,R,S,trivial⟩,o⟩
  · rintro ⟨⟨A,⟨B,u⟩,C,⟨D,v'⟩,F,G,I,J,K,L,M,N,O,R,S,_⟩,o⟩
    exact ⟨⟨u,v',o⟩,A,B,C,D,F,G,I,J,K,L,M,N,O,R,S⟩

open Groundwork
def selectorEval (g : ℕ) (a : List Bool) := decide (a.length = 27) &&
  select (decide (g = 0)) (fun j => a[j.val]?.getD false)
theorem selectorEval_eq (g : ℕ) (a : Fin 27 → Bool) : selectorEval g (List.ofFn a) = select (decide (g = 0)) a := by
  unfold selectorEval; simp only [List.length_ofFn,decide_true,Bool.true_and]; congr 1; funext j
  simp only [List.getElem?_ofFn,dif_pos j.isLt,Option.getD_some]
attribute [local fun_prop] PolyT.const PolyT.comp PolyT.id' PolyT.length PolyT.fst PolyT.snd PolyT.prodMk P2M_Groundwork_PolyT_ite__226169acf219
set_option maxHeartbeats 1600000 in
theorem selectorEval_poly {α : Type} [Enc α] {a : α → List Bool} {g : α → ℕ} (hg : PolyT g) (ha : PolyT a) :
    PolyT fun x => selectorEval (g x) (a x) := by unfold selectorEval select; dsimp only; fun_prop
end DetDLP.S8O.ECAddTile


