-- Prove2me | Definitions.Def_DetDLP_M3B_ECAddRows
-- name    : DetDLP_M3B_ECAddRows
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T14:06:59.091546+00:00
-- url     : https://prove2.me/theorems/ae018062-01ed-4cb8-98fa-58b977004015
-- title:
--   EC unpinned addition rows
-- statement:
--   Unpinned S8H0 register block for short-Weierstrass point addition
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_M3B_ECMapRows

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 100000
namespace DetDLP.M3B.ECAddRows
open S8H0 RegisterMap NamedBlocks ResidueWires SignalBank HashRows RangeRows GateRoutes
open S8H.ECPointArithmetic S8K.ECAddArithmetic ECMapRows
variable {d e p : ℕ} {s : Shape} [Fact p.Prime]
def inv (u : ZMod p) (z : ZeroInvCert p) :=
  both (hash u z.2.1 0 z.2.2)
    (plain (if z.1 then u = 0 ∧ z.2.1 = 0 else z.2.2.1 = 1)
      (if z.1 then wordEq u 0 ∧ wordEq z.2.1 0 else wordEq z.2.2.1 1) (by simp only [← eq_bits]))

def addChecks' (E : WeierstrassCurve (ZMod p)) (P Q out : Coords p) (c : AddCert p) :=
  let (i,x,y) := P; let (j,z,w) := Q
  let (ux,bx,uy,by',dy,chord,sq,num,tan,lsq,tx,X,dx,ty,Y,_) := c
  let l := if !i && !j && !bx.1 then chord.1 else if !i && !j && bx.1 && !by'.1 then tan.1 else 0
  both (both (hash (-1) x z ux) <| both (inv ux.1 bx) <| both (hash 1 y w uy) <| both (inv uy.1 by') <|
    both (hash (-1) y w dy) <| both (hash dy.1 bx.2.1 0 chord) <| both (hash x x 0 sq) <|
    both (hash 3 sq.1 (-27*E.c₄) num) <| both (hash num.1 by'.2.1 0 tan) <| both (hash l l 0 lsq) <|
    both (hash (-1) x lsq.1 tx) <| both (hash (-1) z tx.1 X) <| both (hash (-1) X.1 x dx) <|
    both (hash l dx.1 0 ty) <| both (hash (-1) y ty.1 Y) (plain True True Iff.rfl))
    (finalCoords out (if i then Q else if j then (false,x,y) else if bx.1 && by'.1 then (true,0,0) else (false,X.1,Y.1)))

theorem addChecks_lift (E : WeierstrassCurve (ZMod p)) (P Q out : Coords p) (c : AddCert p) :
    w3_slotLift (swAddOK E P Q out c) (addChecks' E P Q out c).bits := (addChecks' E P Q out c).lift

private abbrev ctrl (d : ℕ) := Shape.pair .bit (triple d)
def addShape (d e : ℕ) := Shape.pair (.pair .bit (.pair (triple d) (triple d)))
  (.pair (.vec 2 (ctrl d)) (.pair (.word d) (.vec 15 (slot d e))))
private abbrev sp (f : Path (addShape d e) s) (k : Fin 15) : Path (slot d e) s := fun j => f (.snd (.snd (.snd (.vec k j))))
private abbrev cp (f : Path (addShape d e) s) (k : Fin 2) : Path (ctrl d) s := fun j => f (.snd (.fst (.vec k j)))
private abbrev lp (f : Path (addShape d e) s) := fstP (sndP (sndP f))
private abbrev bit (f : Path .bit s) : Ref s := .reg (f .bit)
private def slope {α : Type} (i j b c : Bool) (ch t zero : α) :=
  if !i && !j && !b then ch else if !i && !j && b && !c then t else zero
private def pick {α : Type} (i j b c : Bool) (q p zero r : α) := if i then q else if j then p else if b && c then zero else r
private def branch (n : ℕ) (i j b c : Ref s) (o q x z r : Word s) (sel : Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool) :=
  rows n 9 (fun k => ![i,j,b,c,o k,q k,x k,z k,r k]) (fun _ a => a 4 == sel (a 0) (a 1) (a 2) (a 3) (a 5) (a 6) (a 7) (a 8))
private def invRow (n : ℕ) (b : Ref s) (u a r one : Word s) := rows n 5
  (fun k => ![b,u k,a k,r k,one k]) (fun _ v => if v 0 then !v 1 && !v 2 else v 3 == v 4)
private def args {α : Type} (m o t c zero x y z w bx by' l : α) (g : Fin 15 → α) (k : Fin 15) : α × α × α :=
  match k.val with
  | 0 => (m,x,z) | 1 => (g 0,bx,zero) | 2 => (o,y,w) | 3 => (g 2,by',zero)
  | 4 => (m,y,w) | 5 => (g 4,bx,zero) | 6 => (x,x,zero) | 7 => (t,g 6,c)
  | 8 => (g 7,by',zero) | 9 => (l,l,zero) | 10 => (m,x,g 9) | 11 => (m,z,g 10)
  | 12 => (m,g 11,x) | 13 => (l,g 12,zero) | _ => (m,y,g 13)
private def ranges (p : ℕ) (f : Path (addShape d e) s) :=
  joinB (joinB (checker p (fstP (sndP (fstP f)))) (checker p (sndP (sndP (fstP f)))))
    (joinB (many 1 fun k => checker p (sndP (cp f k))) (many 14 fun k => joinB (checker p (result (sp f k))) (checker p (remain (sp f k)))))
def addBlock (hd : 1 ≤ d) (p minus1 one three c4term : ℕ) (i j : Ref s) (x y z w : Word s) (f : Path (addShape d e) s) :=
  let g := fun k => rwrd (result (sp f k)); let b := fun k => bit (fstP (cp f k)); let a := fun k => rwrd (sndP (cp f k))
  let l := word (lp f); let out := sndP (fstP f); let br := fun n => branch n i j (b 0) (b 1)
  let A := args (pub minus1) (pub one) (pub three) (pub c4term) (pub 0) x y z w (a 0) (a 1) l g
  joinB (ranges p f) <| joinB (many 14 fun k => slotBlock hd p (A k).1 (A k).2.1 (A k).2.2 (sp f k)) <|
    joinB (invRow d (b 0) (g 0) (a 0) (g 1) (pub one)) <| joinB (invRow d (b 1) (g 2) (a 1) (g 3) (pub one)) <|
    joinB (br d l (g 5) (g 8) (pub 0) (pub 0) (fun I J B C ch t zz _ => slope I J B C ch t zz)) <|
    joinB (br 1 (fun _ => bit (fstP (fstP f))) (fun _ => j) (pub 0) (pub 1) (pub 0) pick) <|
    joinB (br d (rwrd (fstP out)) z x (pub 0) (g 11) pick) (br d (rwrd (sndP out)) w y (pub 0) (g 14) pick)

noncomputable section
abbrev Bd (p : ℕ) := Bounded (d:=width p) p
structure Slice (p : ℕ) where
  out : Bool × Bd p × Bd p
  zi : Fin 2 → Bool × Bd p
  gates : Fin 15 → CheckedRun (width p) p (GateSemantics.hd p) × AuxBank (width p)
private abbrev runAt (u : Slice p) (k : Fin 15) := R (u.gates k).1
private abbrev res (u : Slice p) (k : Fin 15) := (runAt u k).1
private def selected (i j : Bool) (u : Slice p) := slope i j (u.zi 0).1 (u.zi 1).1 (res u 5) (res u 8) 0
def sliceData (i j : Bool) (u : Slice p) : (addShape (width p) (GateSemantics.e p)).Data :=
  ((u.out.1,u.out.2.1.val,u.out.2.2.val),(fun k => ((u.zi k).1,(u.zi k).2.val)),
    (fun k => (selected i j u).val.testBit k), fun k => (rawRun (u.gates k).1,(u.gates k).2))
def output (u : Slice p) : Coords p := (u.out.1,Z u.out.2.1,Z u.out.2.2)
private abbrev zi (u : Slice p) (k : Fin 2) (g : Fin 15) : ZeroInvCert p := ((u.zi k).1,Z (u.zi k).2,runAt u g)
def cert (u : Slice p) : AddCert p :=
  (runAt u 0,zi u 0 1,runAt u 2,zi u 1 3,runAt u 4,runAt u 5,runAt u 6,runAt u 7,runAt u 8,
   runAt u 9,runAt u 10,runAt u 11,runAt u 12,runAt u 13,runAt u 14,())
private abbrev ga (u : Slice p) (k : Fin 15) : GateAux p :=
  (auxEquiv _ (u.gates k).2,value (u.gates k).1.1.val.2.1,(u.gates k).1.1.val.2.2)
def auxBits (u : Slice p) := ((ga u 0,(ga u 1,()),ga u 2,(ga u 3,()),ga u 4,ga u 5,ga u 6,ga u 7,
  ga u 8,ga u 9,ga u 10,ga u 11,ga u 12,ga u 13,ga u 14,()),())

private theorem invSpec (v : Bits (s.size+1)) (f : Ref s) (a b r : Word s) (A B C : ZMod p)
    (ha : evalWord a v A.val) (hb : evalWord b v B.val) (hc : evalWord r v C.val) :
    (invRow (width p) f a b r (pub (1 : ZMod p).val)).OK v ↔
    if f.eval v then wordEq A 0 ∧ wordEq B 0 else wordEq C 1 := by
  have ha' : ∀ n, (a n).eval v = A.val.testBit n := ha
  have hb' : ∀ n, (b n).eval v = B.val.testBit n := hb
  have hc' : ∀ n, (r n).eval v = C.val.testBit n := hc
  rw [invRow, rows_iff]
  have rowAt (k : Fin (width p)) :
      (let g := fun j => (![f, a k.val, b k.val, r k.val, pub (1 : ZMod p).val k.val] j).eval v
       if g 0 then !g 1 && !g 2 else g 3 == g 4) =
      (if f.eval v then !(a k.val).eval v && !(b k.val).eval v
       else (r k.val).eval v == (1 : ZMod p).val.testBit k.val) := rfl
  simp only [rowAt]
  cases hf : f.eval v
  · simp only [Bool.false_eq_true, ↓reduceIte, beq_iff_eq, hc', wordEq]
  · simp only [↓reduceIte, Bool.and_eq_true, Bool.not_eq_true', ha', hb', wordEq,
      ZMod.val_zero, Nat.zero_testBit, forall_and]
theorem addBlock_iff (E : WeierstrassCurve (ZMod p)) (P Q : Coords p) (u : Slice p)
    (f : Path (addShape (width p) (GateSemantics.e p)) s) (v : Bits (s.size+1)) (i j : Ref s) (x y z w : Word s)
    (H : At f v (sliceData P.1 Q.1 u)) (I : i.eval v = P.1) (J : j.eval v = Q.1)
    (X : evalWord x v P.2.1.val) (Y : evalWord y v P.2.2.val) (D : evalWord z v Q.2.1.val) (W : evalWord w v Q.2.2.val) :
    (addBlock (GateSemantics.hd p) p (-1 : ZMod p).val (1 : ZMod p).val (3 : ZMod p).val (-27*E.c₄).val i j x y z w f).OK v ↔
    (addChecks' E P Q (output u) (cert u)).bits (auxBits u) := by
  have bound {k : Path (triple (width p)) s} (a : Bd p) (h : At k v a.val) := (checker_iff p k v a.val h).2 a.property
  have ev {k : Path (triple (width p)) s} (a : Bd p) (h : At k v a.val) : evalWord (rwrd k) v (Z a).val := by
    rw [GateSemantics.resVal a.val a.property]; exact wordAt (fun n => h (.fst n))
  have O (k : Fin 15) : evalWord (rwrd (result (sp f k))) v (res u k).val := ev _ (fun n => H (.snd (.snd (.snd (.vec k (.fst (.fst n)))))))
  have A (k : Fin 2) : evalWord (rwrd (sndP (cp f k))) v (Z (u.zi k).2).val := ev _ (fun n => H (.snd (.fst (.vec k (.snd n)))))
  have B (k : Fin 2) : (bit (fstP (cp f k))).eval v = (u.zi k).1 := H (.snd (.fst (.vec k (.fst .bit))))
  have Ox := ev u.out.2.1 (fun n => H (.fst (.snd (.fst n)))); have Oy := ev u.out.2.2 (fun n => H (.fst (.snd (.snd n))))
  have Of : (bit (fstP (fstP f))).eval v = u.out.1 := H (.fst (.fst .bit))
  have S : evalWord (word (lp f)) v (selected P.1 Q.1 u).val := by
    have a := wordAt (f:=lp f) (u:=fun k => (selected P.1 Q.1 u).val.testBit k) (fun n => H (.snd (.snd (.fst n))))
    exact (show (value _).val = (selected P.1 Q.1 u).val from congrArg Fin.val ((numBits _).apply_symm_apply ⟨_,(selected P.1 Q.1 u).val_lt.trans (fits p)⟩)) ▸ a
  have C : (ranges p f).OK v := by
    simp only [ranges,joinB_iff,many_iff]; exact ⟨⟨bound _ (fun n => H (.fst (.snd (.fst n)))),bound _ (fun n => H (.fst (.snd (.snd n))))⟩,
      (fun k => bound _ (fun n => H (.snd (.fst (.vec k (.snd n)))))),fun k => ⟨bound _ (fun n => H (.snd (.snd (.snd (.vec k (.fst (.fst n))))))),
      bound _ (fun n => H (.snd (.snd (.snd (.vec k (.fst (.snd (.fst (.fst n)))))))))⟩⟩
  have G (k : Fin 15) := @gateAt _ _ _ v (sp f k) (u.gates k).1 (u.gates k).2 (fun n => H (.snd (.snd (.snd (.vec k n)))))
  have L (k : Fin 15) : w3_slotLt _ (res u k).val p (ga u k).2 := by
    change w3_slotLt _ (Z _).val _ _; rw [GateSemantics.resVal]; exact (below_iff _ _).1 (u.gates k).1.1.property
  have K (n : ℕ) : evalWord (pub n) v n := fun _ => rfl
  have Vx := invSpec v (bit (fstP (cp f 0))) _ _ _ _ _ _ (O 0) (A 0) (O 1)
  have Vy := invSpec v (bit (fstP (cp f 1))) _ _ _ _ _ _ (O 2) (A 1) (O 3)
  simp only [B] at Vx Vy
  let br := fun n => branch n i j (bit (fstP (cp f 0))) (bit (fstP (cp f 1)))
  have brIff {n : ℕ} (o q a b r : Word s)
      (sel : Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool) :
      (br n o q a b r sel).OK v ↔ ∀ k : Fin n, (o k.val).eval v =
        sel (i.eval v) (j.eval v) ((bit (fstP (cp f 0))).eval v) ((bit (fstP (cp f 1))).eval v)
          ((q k.val).eval v) ((a k.val).eval v) ((b k.val).eval v) ((r k.val).eval v) := by
    dsimp only [br]; rw [branch, rows_iff]
    refine forall_congr' fun k => ?_
    have rowEq :
        (let g := fun m => (![i, j, bit (fstP (cp f 0)), bit (fstP (cp f 1)),
            o k.val, q k.val, a k.val, b k.val, r k.val] m).eval v
         g 4 == sel (g 0) (g 1) (g 2) (g 3) (g 5) (g 6) (g 7) (g 8)) =
        ((o k.val).eval v == sel (i.eval v) (j.eval v) ((bit (fstP (cp f 0))).eval v)
          ((bit (fstP (cp f 1))).eval v) ((q k.val).eval v) ((a k.val).eval v)
          ((b k.val).eval v) ((r k.val).eval v)) := rfl
    rw [rowEq, beq_iff_eq]
  have sl : (br (width p) (word (lp f)) (rwrd (result (sp f 5))) (rwrd (result (sp f 8))) (pub 0) (pub 0)
      (fun a b c d ch t zz _ => slope a b c d ch t zz)).OK v := by
    rw [brIff]; intro k; rw [I, J, B 0, B 1, S k, O 5 k, O 8 k, K 0 k]
    dsimp only [selected, slope]
    cases P.1 <;> cases Q.1 <;> cases (u.zi 0).1 <;> cases (u.zi 1).1 <;>
      simp [ZMod.val_zero]
  let expect := if P.1 then Q else if Q.1 then (false,P.2.1,P.2.2) else if (u.zi 0).1 && (u.zi 1).1 then (true,0,0) else (false,res u 11,res u 14)
  have outRows : ((br 1 (fun _ => bit (fstP (fstP f))) (fun _ => j) (pub 0) (pub 1) (pub 0) pick).OK v ∧
      (br (width p) (rwrd (fstP (sndP (fstP f)))) z x (pub 0) (rwrd (result (sp f 11))) pick).OK v ∧
      (br (width p) (rwrd (sndP (sndP (fstP f)))) w y (pub 0) (rwrd (result (sp f 14))) pick).OK v) ↔
      (finalCoords (output u) expect).bits () := by
    have Ox' (n : ℕ) : (rwrd (fstP (sndP (fstP f))) n).eval v = (Z u.out.2.1).val.testBit n := Ox n
    have Oy' (n : ℕ) : (rwrd (sndP (sndP (fstP f))) n).eval v = (Z u.out.2.2).val.testBit n := Oy n
    rw [brIff, brIff, brIff, Fin.forall_fin_one]
    simp only [Fin.val_zero, I, J, B 0, B 1, Of, Ox', Oy']
    rcases P with ⟨pi, px, py⟩; rcases Q with ⟨qj, qz, qw⟩
    have hX : ∀ n, (x n).eval v = px.val.testBit n := X
    have hY : ∀ n, (y n).eval v = py.val.testBit n := Y
    have hD : ∀ n, (z n).eval v = qz.val.testBit n := D
    have hW : ∀ n, (w n).eval v = qw.val.testBit n := W
    have h11 : ∀ n, (rwrd (result (sp f 11)) n).eval v = (res u 11).val.testBit n := O 11
    have h14 : ∀ n, (rwrd (result (sp f 14)) n).eval v = (res u 14).val.testBit n := O 14
    have hK0 : ∀ n, (pub 0 n).eval v = false := fun n => (K 0 n).trans (Nat.zero_testBit n)
    have hK1 : (pub 1 0).eval v = true := K 1 0
    cases pi <;> cases qj <;> cases h0 : (u.zi 0).1 <;> cases h1 : (u.zi 1).1 <;>
      simp [expect, h0, h1, pick, finalCoords, output, plain, wordEq, ZMod.val_zero,
        hX, hY, hD, hW, h11, h14, hK0, hK1]
  have many15 (F : Fin 15 → NamedBlocks.B (s.size+1)) : (many 14 F).OK v ↔
      (F ⟨0,by decide⟩).OK v ∧ (F ⟨1,by decide⟩).OK v ∧ (F ⟨2,by decide⟩).OK v ∧
      (F ⟨3,by decide⟩).OK v ∧ (F ⟨4,by decide⟩).OK v ∧ (F ⟨5,by decide⟩).OK v ∧
      (F ⟨6,by decide⟩).OK v ∧ (F ⟨7,by decide⟩).OK v ∧ (F ⟨8,by decide⟩).OK v ∧
      (F ⟨9,by decide⟩).OK v ∧ (F ⟨10,by decide⟩).OK v ∧ (F ⟨11,by decide⟩).OK v ∧
      (F ⟨12,by decide⟩).OK v ∧ (F ⟨13,by decide⟩).OK v ∧ (F ⟨14,by decide⟩).OK v := by
    simp only [many_iff, Fin.forall_fin_succ, Fin.forall_fin_zero, and_true]; rfl
  have tailEq : ((invRow (width p) (bit (fstP (cp f 0))) (rwrd (result (sp f 0))) (rwrd (sndP (cp f 0)))
        (rwrd (result (sp f 1))) (pub (1 : ZMod p).val)).OK v ∧
      (invRow (width p) (bit (fstP (cp f 1))) (rwrd (result (sp f 2))) (rwrd (sndP (cp f 1)))
        (rwrd (result (sp f 3))) (pub (1 : ZMod p).val)).OK v ∧
      (br (width p) (word (lp f)) (rwrd (result (sp f 5))) (rwrd (result (sp f 8))) (pub 0) (pub 0)
        (fun a b c d ch t zz _ => slope a b c d ch t zz)).OK v ∧
      (br 1 (fun _ => bit (fstP (fstP f))) (fun _ => j) (pub 0) (pub 1) (pub 0) pick).OK v ∧
      (br (width p) (rwrd (fstP (sndP (fstP f)))) z x (pub 0) (rwrd (result (sp f 11))) pick).OK v ∧
      (br (width p) (rwrd (sndP (sndP (fstP f)))) w y (pub 0) (rwrd (result (sp f 14))) pick).OK v) ↔
      (if (u.zi 0).1 then wordEq (res u 0) 0 ∧ wordEq (Z (u.zi 0).2) 0 else wordEq (res u 1) 1) ∧
      (if (u.zi 1).1 then wordEq (res u 2) 0 ∧ wordEq (Z (u.zi 1).2) 0 else wordEq (res u 3) 1) ∧
      (finalCoords (output u) expect).bits () := by
    rw [Vx, Vy, and_iff_right sl, outRows]
  dsimp only [addBlock]
  rw [joinB_iff, and_iff_right C, joinB_iff, many15]
  simp only [joinB_iff, slotBlock, GateSemantics.e, le_refl, ↓reduceIte, args]
  rw [tailEq, G ⟨0,by decide⟩ (K _) X D, G ⟨1,by decide⟩ (O 0) (A 0) (K _),
    G ⟨2,by decide⟩ (K _) Y W, G ⟨3,by decide⟩ (O 2) (A 1) (K _),
    G ⟨4,by decide⟩ (K _) Y W, G ⟨5,by decide⟩ (O 4) (A 0) (K _),
    G ⟨6,by decide⟩ X X (K _), G ⟨7,by decide⟩ (K _) (O 6) (K _),
    G ⟨8,by decide⟩ (O 7) (A 1) (K _), G ⟨9,by decide⟩ S S (K _),
    G ⟨10,by decide⟩ (K _) X (O 9), G ⟨11,by decide⟩ (K _) D (O 10),
    G ⟨12,by decide⟩ (K _) (O 11) X, G ⟨13,by decide⟩ S (O 12) (K _),
    G ⟨14,by decide⟩ (K _) Y (O 13)]
  simp only [addChecks', both, inv, ECMapRows.hash, plain, cert, zi, auxBits, L, and_true, ZMod.val_zero, ga]
  simp only [and_assoc]
  constructor
  · rintro ⟨g0,g1,g2,g3,g4,g5,g6,g7,g8,g9,g10,g11,g12,g13,g14,vx,vy,o⟩
    exact ⟨g0,g1,vx,g2,g3,vy,g4,g5,g6,g7,g8,g9,g10,g11,g12,g13,g14,o⟩
  · rintro ⟨g0,g1,vx,g2,g3,vy,g4,g5,g6,g7,g8,g9,g10,g11,g12,g13,g14,o⟩
    exact ⟨g0,g1,g2,g3,g4,g5,g6,g7,g8,g9,g10,g11,g12,g13,g14,vx,vy,o⟩

theorem addBlock_lift (E : WeierstrassCurve (ZMod p)) (P Q : Coords p) (u : Slice p)
    (f : Path (addShape (width p) (GateSemantics.e p)) s) (v : Bits (s.size+1)) (i j : Ref s) (x y z w : Word s)
    (H : At f v (sliceData P.1 Q.1 u)) (I : i.eval v = P.1) (J : j.eval v = Q.1)
    (X : evalWord x v P.2.1.val) (Y : evalWord y v P.2.2.val) (D : evalWord z v Q.2.1.val) (W : evalWord w v Q.2.2.val)
    (h : (addBlock (GateSemantics.hd p) p (-1 : ZMod p).val (1 : ZMod p).val (3 : ZMod p).val (-27*E.c₄).val i j x y z w f).OK v) :
    swAddOK E P Q (output u) (cert u) :=
  (addChecks_lift E P Q (output u) (cert u)).1 _ ((addBlock_iff E P Q u f v i j x y z w H I J X Y D W).mp h)

theorem addBlock_edges (hd : 1 ≤ d) (p m o t c : ℕ) (i j : Ref s) (x y z w : Word s) (f : Path (addShape d e) s) :
    (addBlock hd p m o t c i j x y z w f).core.A.ne ≤ 60*e + 1600*(d+2) := by
  by_cases h : (w4_M5GraphBounds.graph d hd).nE ≤ e <;>
    simp only [addBlock,ranges,slotBlock,h,if_true,if_false,branch,invRow,HashRows.block,many,joinB,HashRows.product,eqs,
      HashRows.sumRows,checker,NamedBlocks.add,rows,mapped,S8J.join,S8C.AddLayout.layout,w3_fpMulLayout,w3_m5Layout,w3_forgetSides] <;> omega
end
end DetDLP.M3B.ECAddRows


