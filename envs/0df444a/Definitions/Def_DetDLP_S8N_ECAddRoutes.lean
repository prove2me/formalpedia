-- Prove2me | Definitions.Def_DetDLP_S8N_ECAddRoutes
-- name    : DetDLP_S8N_ECAddRoutes
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T11:04:40.447834+00:00
-- url     : https://prove2.me/theorems/f834e8de-eb30-4af8-816e-fdd17c3dc576
-- title:
--   Fixed register routes for short-Weierstrass addition
-- statement:
--   The block wires fifteen modular hash slots to the addition certificate. For each inverse test, the zero branch requires both the operand and its proposed inverse to vanish; the other branch requires the product to equal $1$. The theorem `rows_iff_decoded` characterizes the range, hash, slope, and output rows on a decoded register bank.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8M_ECMapRows
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace DetDLP.S8N.ECAddRoutes
open S8H0 RegisterMap NamedBlocks ResidueWires SignalBank HashRows RangeRows GateRoutes S8M.ECMapRows S8H.ECPointArithmetic S8K.ECAddArithmetic S8O.ECAddLayout
variable {d e : ℕ} {s : Shape}
/-- Output flag; output x,y and inverse operands x,y; two zero flags; slope; fifteen hash slots. -/
def addShape (d e : ℕ) : Shape := .pair (.pair .bit (.vec 4 (triple d))) (.pair (.pair (.vec 2 .bit) (.word d)) (.vec 15 (slot d e)))
private abbrev fstP {a b : Shape} (f : Path (.pair a b) s) : Path a s := fun j => f (.fst j)
private abbrev sndP {a b : Shape} (f : Path (.pair a b) s) : Path b s := fun j => f (.snd j)
private abbrev rwrd (f : Path (triple d) s) := word (fstP f)
private abbrev refw {n : ℕ} (f : Path (.word n) s) (i : Fin n) : Ref s := .reg (f (.word i))
private def gw (hd : 1 ≤ d) (p : ℕ) (a x b : Word s) (f : Path (slot d e) s) : Wires d hd s :=
  let r := fstP f; let k := fstP (sndP r); let l := sndP k; let m := sndP l; let t := sndP f
  ⟨a,x,b,rwrd (fstP r),rwrd (fstP k),word (fstP l),word (fstP (fstP m)),word (fstP (sndP m)),word (fstP (sndP t)),fun i => .masked (p.testBit i) (sndP (sndP r) .bit),
   pad (refw (sndP (fstP m))),pad (refw (sndP (sndP m))),refw (fstP t),refw (fstP (sndP (sndP t))),refw (sndP (sndP (sndP t)))⟩
private abbrev regP (f : Path (addShape d e) s) (k : Fin 4) : Path (triple d) s := fun j => f (.fst (.snd (.vec k j)))
private abbrev sl (f : Path (addShape d e) s) (k : Fin 15) : Path (slot d e) s := fun j => f (.snd (.snd (.vec k j)))
private abbrev flag (f : Path (addShape d e) s) (k : Fin 2) : Ref s := .reg (f (.snd (.fst (.fst (.vec k .bit)))))
private abbrev slope (f : Path (addShape d e) s) : Path (.word d) s := sndP (fstP (sndP f))
private abbrev res (f : Path (slot d e) s) := fstP (fstP f)
private abbrev remP (f : Path (slot d e) s) := fstP (fstP (sndP (fstP f)))
-- ux, inverse check x, uy, inverse check y, dy, chord, sq, num, tan, lsq, tx, X, dx, ty, Y.
def args {α : Type} (n o t c z x y X Y l : α) (a : Fin 4 → α) (r : Fin 15 → α) : Fin 15 → α × α × α :=
  ![(n,x,X),(r 0,a 2,z),(o,y,Y),(r 2,a 3,z),(n,y,Y),(r 4,a 2,z),(x,x,z),(t,r 6,c),(r 7,a 3,z),(l,l,z),(n,x,r 9),(n,X,r 10),(n,r 11,x),(l,r 12,z),(n,y,r 13)]
private def invRows (d : ℕ) (b : Ref s) (a v r : Word s) := rows d 4 (fun k => ![b,a k,v k,r k])
  (fun k h => if h 0 then !h 1 && !h 2 else h 3 == (1 : ℕ).testBit k)
def mux (i j bx by' c t : Bool) : Bool := if !i && !j && !bx then c else if !i && !j && bx && !by' then t else false
def dest (i j bx by' x y z : Bool) : Bool := if i then y else if j then x else if bx && by' then false else z
private def selectRows (d : ℕ) (i j bx by' : Ref s) (x y z out : Word s) := rows d 8
  (fun k => ![i,j,bx,by',x k,y k,z k,out k]) (fun _ h => h 7 == dest (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6))
/-- Fixed routes: only the modulus, reduced coefficients and input addresses are parameters. -/
def addBlock (hd : 1 ≤ d) (p neg1 three c4Term : ℕ) (inFlagP : Ref s) (inXP inYP : Word s) (inFlagQ : Ref s) (inXQ inYQ : Word s) (path : Path (addShape d e) s) : B (s.size+1) :=
  let a := fun k => rwrd (regP path k); let r := fun k => rwrd (res (sl path k)); let l := word (slope path)
  let i := inFlagP; let j := inFlagQ; let bx := flag path 0; let by' := flag path 1
  let g := args (pub neg1) (pub 1) (pub three) (pub c4Term) (pub 0) inXP inYP inXQ inYQ l a r
  joinB (many 3 fun k => checker p (regP path k)) <| joinB (many 14 fun k => joinB (checker p (res (sl path k))) (checker p (remP (sl path k)))) <|
    joinB (many 14 fun k => HashRows.block p (gw hd p (g k).1 (g k).2.1 (g k).2.2 (sl path k))) <|
    joinB (invRows d bx (r 0) (a 2) (r 1)) <| joinB (invRows d by' (r 2) (a 3) (r 3)) <|
    joinB (rows d 7 (fun k => ![i,j,bx,by',r 5 k,r 8 k,l k]) (fun _ h => h 6 == mux (h 0) (h 1) (h 2) (h 3) (h 4) (h 5))) <|
    joinB (rows 1 5 (fun _ => ![i,j,bx,by',.reg (path (.fst (.fst .bit)))]) (fun _ h => h 4 == (if h 0 then h 1 else !h 1 && h 2 && h 3))) <|
    joinB (selectRows d i j bx by' inXP inXQ (r 11) (a 0)) (selectRows d i j bx by' inYP inYQ (r 14) (a 1))
variable {p : ℕ} [Fact p.Prime]
noncomputable section
private abbrev R := runEquiv (GateSemantics.hd p) (fits p).le
abbrev rawRun (r : CheckedRun (width p) p (GateSemantics.hd p)) : (run (width p) (GateSemantics.e p)).Data := (r.1.val,(r.2.1.1.val,r.2.1.2),r.2.2)
private theorem wordAt {n : ℕ} {f : Path (.word n) s} {v : Bits (s.size+1)} {u : Bits n} (h : At f v u) : evalWord (word f) v (value u).val := padded_spec _ _ _ fun i => h (.word i)
private theorem gateAt {v : Bits (s.size+1)} {f : Path (slot (width p) (GateSemantics.e p)) s} (r : CheckedRun (width p) p (GateSemantics.hd p)) (t : AuxBank (width p)) (h : At f v (rawRun r,t))
    {a x b : Word s} {A X B : ℕ} (ha : evalWord a v A) (hx : evalWord x v X) (hb : evalWord b v B) :
    (HashRows.block p (gw (GateSemantics.hd p) p a x b f)).OK v ↔ w3_slotHashBits (GateSemantics.hd p) A B X (R r).1.val (R r).2 (auxEquiv _ t) := by
  apply block_spec _ _ _ _ _ _ _ _ _ ha hx hb
  · change evalWord _ _ ((zmodEquiv (fits p).le) r.1).val; rw [GateSemantics.resVal]; exact wordAt (fun j => h (.fst (.fst (.fst j))))
  · change evalWord _ _ ((finEquiv (fits p).le) r.2.1.1).val; rw [finEquiv_val]; exact wordAt (fun j => h (.fst (.snd (.fst (.fst (.fst j))))))
  all_goals first | exact wordAt (fun j => h (.fst (.snd (.fst (.snd (.fst j)))))) | exact wordAt (fun j => h (.fst (.snd (.fst (.snd (.snd (.fst (.fst j)))))))) | exact wordAt (fun j => h (.fst (.snd (.fst (.snd (.snd (.snd (.fst j)))))))) | exact wordAt (fun j => h (.snd (.snd (.fst j)))) | skip
  · intro i; let j : Addr (slot (width p) (GateSemantics.e p)) := .fst (.snd (.snd .bit))
    change (p.testBit i && (Ref.reg (f j)).eval v) = (if r.2.2 then p else 0).testBit i
    rw [h j]; change (p.testBit i && r.2.2) = _; cases r.2.2 <;> simp
  all_goals funext i; first | simp only [gw,pad,dif_pos (show i.val < GateSemantics.e p from i.isLt)]; apply h | apply h
/-- Bit semantics on a decoded slice. The two inverse branches and all selectors are per-bit. -/
theorem rows_iff_decoded (neg1 three c4Term : ℕ) (i j : Ref s) (xp yp xq yq : Word s) (x y X Y : ℕ)
    (f : Path (addShape (width p) (GateSemantics.e p)) s) (u : Bits (s.size+1)) (o : Bool) (v : Fin 4 → Triple (width p))
    (b : Fin 2 → Bool) (l : Bits (width p)) (r : Fin 15 → CheckedRun (width p) p (GateSemantics.hd p)) (t : Fin 15 → AuxBank (width p))
    (H : At f u ((o,v),(b,l),fun k => (rawRun (r k),t k))) (hx : evalWord xp u x) (hy : evalWord yp u y) (hX : evalWord xq u X) (hY : evalWord yq u Y) :
    let a := fun k => (value (v k).1).val; let z := fun k => (R (r k)).1.val; let L := (value l).val
    let g := args neg1 1 three c4Term 0 x y X Y L a z; let I := i.eval u; let J := j.eval u
    let lt := fun (v : Triple (width p)) => w3_slotLt _ (value v.1).val p (value v.2.1,v.2.2)
    let invOK := fun (b : Bool) (a v r : ℕ) => ∀ k : Fin (width p), if b then a.testBit k = false ∧ v.testBit k = false else r.testBit k = (1 : ℕ).testBit k
    (addBlock (GateSemantics.hd p) p neg1 three c4Term i xp yp j xq yq f).OK u ↔
    (∀ k, lt (v k)) ∧ (∀ k, lt (r k).1.val ∧ lt (r k).2.1.1.val) ∧
    (∀ k, w3_slotHashBits (GateSemantics.hd p) (g k).1 (g k).2.2 (g k).2.1 (z k) (R (r k)).2 (auxEquiv _ (t k))) ∧
    invOK (b 0) (z 0) (a 2) (z 1) ∧ invOK (b 1) (z 2) (a 3) (z 3) ∧
    (∀ k : Fin (width p), L.testBit k = mux I J (b 0) (b 1) ((z 5).testBit k) ((z 8).testBit k)) ∧
    o = (if I then J else !J && b 0 && b 1) ∧
    (∀ k : Fin (width p), (a 0).testBit k = dest I J (b 0) (b 1) (x.testBit k) (X.testBit k) ((z 11).testBit k)) ∧
    (∀ k : Fin (width p), (a 1).testBit k = dest I J (b 0) (b 1) (y.testBit k) (Y.testBit k) ((z 14).testBit k)) := by
  dsimp only
  have A (k : Fin 4) : evalWord (rwrd (regP f k)) u (value (v k).1).val := wordAt (fun j => H (.fst (.snd (.vec k (.fst j)))))
  have Z (k : Fin 15) : evalWord (rwrd (res (sl f k))) u (R (r k)).1.val := by
    change evalWord _ _ ((zmodEquiv (fits p).le) (r k).1).val; rw [GateSemantics.resVal]; exact wordAt (fun j => H (.snd (.snd (.vec k (.fst (.fst (.fst j)))))))
  have L : evalWord (word (slope f)) u (value l).val := wordAt (fun j => H (.snd (.fst (.snd j))))
  have B (k : Fin 2) : (flag f k).eval u = b k := H (.snd (.fst (.fst (.vec k .bit))))
  have O : (Ref.reg (f (.fst (.fst .bit)))).eval u = o := H _
  have C (k : Fin 4) := (checker_iff p (regP f k) u (v k) (fun j => H (.fst (.snd (.vec k j))))).trans (below_iff _ _)
  have D (k : Fin 15) := (checker_iff p (res (sl f k)) u (r k).1.val (fun j => H (.snd (.snd (.vec k (.fst (.fst j))))))).trans (below_iff _ _)
  have E (k : Fin 15) := (checker_iff p (remP (sl f k)) u (r k).2.1.1.val (fun j => H (.snd (.snd (.vec k (.fst (.snd (.fst (.fst j))))))))).trans (below_iff _ _)
  let w := args (pub neg1) (pub 1) (pub three) (pub c4Term) (pub 0) xp yp xq yq (word (slope f)) (fun k => rwrd (regP f k)) (fun k => rwrd (res (sl f k)))
  let n := args neg1 1 three c4Term 0 x y X Y (value l).val (fun k => (value (v k).1).val) (fun k => (R (r k)).1.val)
  have P (n : ℕ) : evalWord (pub n) u n := fun _ => rfl
  have T (k : Fin 15) : evalWord (w k).1 u (n k).1 ∧ evalWord (w k).2.1 u (n k).2.1 ∧ evalWord (w k).2.2 u (n k).2.2 := by
    fin_cases k <;> refine ⟨?_,?_,?_⟩ <;> first | exact hx | exact hy | exact hX | exact hY | apply Z | apply A | exact L | apply P
  have G (k : Fin 15) := gateAt (f := sl f k) (r k) (t k) (fun j => H (.snd (.snd (.vec k j)))) (T k).1 (T k).2.1 (T k).2.2
  dsimp only [w,n] at G
  simp only [addBlock,joinB_iff,many_iff,C,D,E,G]
  unfold evalWord at A Z L hx hy hX hY
  simp [invRows,selectRows,rows_iff,B,O,A,Z,L,hx,hy,hX,hY]
end
end DetDLP.S8N.ECAddRoutes


