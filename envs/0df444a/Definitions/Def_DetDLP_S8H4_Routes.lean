-- Prove2me | Definitions.Def_DetDLP_S8H4_Routes
-- name    : DetDLP_S8H4_Routes
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T09:42:37.562568+00:00
-- url     : https://prove2.me/theorems/397354ef-8dce-4c17-9327-49041287533e
-- title:
--   Tag 4 register bank and declarative row network
-- statement:
--   **Register bank.** The Tag 4 bank extends the seven-gate bank by two $d$-bit operand registers and the difference and carry words for the threshold test. The network depends only on public parameters; the point coordinates and arithmetic witnesses are read from an assignment.
--
--   **Acceptance.** `network_iff` characterizes acceptance as the conjunction of the range, curve, and seven arithmetic checks with the following conditions. The low bit of $y$ selects $(a_0,b_0)$ or $(a_1,b_1)$ for gate 6. The point flag is false, the threshold witness satisfies `w3_slotLt` for $O_6$ and $T$, and the point encoding has prefix $\eta$. The encoding reads the flag first, followed by the big-endian $x$ and $y$ digits of width $\operatorname{bitLen}(p)$.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8H0_GateRoutes
import Definitions.Def_DetDLP_S8H_ECPointSlots

set_option autoImplicit false
namespace DetDLP.S8H4.Routes
open S8H0 RegisterMap NamedBlocks ResidueWires HashRows RangeRows
variable {d e : ℕ}

/-- The old bank, followed by the two seed words and the threshold subtraction witness. -/
def bank (d e : ℕ) : Shape := .pair (GateRoutes.S d e)
  (.pair (.word d) (.pair (.word d) (.pair (.word d) (.word (d+1)))))

def network (hd : 1 ≤ d) (p T a0 b0 a1 b1 : ℕ) (c : GateRoutes.Coeff) (η : List Bool) :
    B ((bank d (w4_M5GraphBounds.graph d hd).nE).size+1) :=
  let e := (w4_M5GraphBounds.graph d hd).nE
  let base := joinB (RangeRows.block d e p) <| joinB (many 5 fun g =>
    HashRows.block p (GateRoutes.wires hd p c g.castSucc)) (CurveRows.block d e)
  let mux := rows (s:=bank d e) d 3 (fun i => ![coord ya 0, a6Reg i, b6Reg i]) fun i r =>
    decide (r 1 = (if r 0 then a1 else a0).testBit i ∧ r 2 = (if r 0 then b1 else b0).testBit i)
  let ltT := NamedBlocks.add (s:=bank d e) (n:=d+1) true (pad fun i : Fin d => Ref.reg (.fst (oa 6 (.fst (.word i)))))
    (pad fun i : Fin d => .reg (.snd (.snd (.snd (.fst (.word i))))))
    (fun i => .pin (T.testBit i)) (fun i => .reg (.snd (.snd (.snd (.snd (.word i))))))
  let flag : Ref (bank d e) := .reg (.fst CurveRows.flag)
  let refs := digits (e:=e) (d:=d) (bitLen p)
  let pre := rows η.length 1 (fun i _ => refs[i.val]?.getD (.pin false))
    (fun i r => decide (i.val < refs.length ∧ r 0 = η[i]))
  joinB ⟨base.core, embed (d:=d) (e:=e) ∘ base.name⟩ <| joinB (HashRows.block p (six hd p c)) <| joinB mux <|
    joinB (rows 1 1 (fun _ _ => flag) (fun _ r => decide (r 0 = false))) (joinB ltT pre)
where
  embed {d e : ℕ} : Fin ((GateRoutes.S d e).size+1) → Fin ((bank d e).size+1) :=
    Fin.lastCases (Fin.last _) (fun i => (i.castAdd _).castSucc)
  a6Reg {d e : ℕ} (i : Fin d) : Ref (bank d e) := .reg (.snd (.fst (.word i)))
  b6Reg {d e : ℕ} (i : Fin d) : Ref (bank d e) := .reg (.snd (.snd (.fst (.word i))))
  coord {d e : ℕ} (a : GateRoutes.Path (triple d) (GateRoutes.S d e)) : Word (bank d e) :=
    GateRoutes.word fun j => .fst (a (.fst j))
  digits {d e : ℕ} (b : ℕ) : List (Ref (bank d e)) := .reg (.fst CurveRows.flag) ::
    (List.ofFn (fun i : Fin b => coord xa i.rev) ++ List.ofFn (fun i : Fin b => coord ya i.rev))
  six {d : ℕ} (hd : 1 ≤ d) (p : ℕ) (c : GateRoutes.Coeff) : Wires d hd (bank d (w4_M5GraphBounds.graph d hd).nE) :=
    let w := GateRoutes.wires hd p c 6
    let lift : Ref _ → Ref (bank d (w4_M5GraphBounds.graph d hd).nE) := fun r => match r with
      | .reg a => .reg (.fst a) | .masked b a => .masked b (.fst a) | .pin b => .pin b
    { a := padded a6Reg, x := coord xa, b := padded b6Reg, z := lift ∘ w.z, rem := lift ∘ w.rem
      quot := lift ∘ w.quot, prod1 := lift ∘ w.prod1, prod2 := lift ∘ w.prod2, sum := lift ∘ w.sum
      cp := lift ∘ w.cp, mul1 := lift ∘ w.mul1, mul2 := lift ∘ w.mul2, carry1 := lift ∘ w.carry1
      carry2 := lift ∘ w.carry2, carry3 := lift ∘ w.carry3 }

/-- The prefix is read in point-encoding order: flag, then the two big-endian digits. -/
theorem network_iff (hd : 1 ≤ d) (p T a0 b0 a1 b1 : ℕ) (c : GateRoutes.Coeff) (η : List Bool)
    (u : Bits ((bank d (w4_M5GraphBounds.graph d hd).nE).size+1)) :
    let e := (w4_M5GraphBounds.graph d hd).nE
    let v := (bank d e).decode (u ∘ Fin.castSucc)
    let x := u ∘ network.embed (d:=d) (e:=e)
    let X := (value v.1.1.2.1.1).val; let Y := (value v.1.1.2.2.1).val
    (network hd p T a0 b0 a1 b1 c η).OK u ↔
      (SignalBank.canonical p v.1 ∧ (∀ g : Fin 6, (HashRows.block p (GateRoutes.wires hd p c g.castSucc)).OK x) ∧
        CurveRows.rawCheck v.1) ∧ (HashRows.block p (network.six hd p c)).OK u ∧
      (∀ i : Fin d, v.2.1 i = (if Y.testBit 0 then a1 else a0).testBit i ∧
        v.2.2.1 i = (if Y.testBit 0 then b1 else b0).testBit i) ∧ v.1.1.1 = false ∧
      w3_slotLt d (value (v.1.2.1 6).1.1) T (value v.2.2.2.1,v.2.2.2.2) ∧
      (v.1.1.1 :: (M89S1.digitWord (bitLen p) X ++ M89S1.digitWord (bitLen p) Y)).take η.length = η := by
  let e := (w4_M5GraphBounds.graph d hd).nE
  let s := bank d e; let v := s.decode (u ∘ Fin.castSucc)
  let x := u ∘ network.embed (d:=d) (e:=e)
  have D : (RegisterMap.bank d (w4_M5GraphBounds.graph d hd).nE).decode (x ∘ Fin.castSucc) = v.1 := by
    apply congrArg ((GateRoutes.S d e).decode); funext i; exact congrArg u (Fin.lastCases_castSucc i)
  have R (j : Addr s) : (Ref.reg j).eval u = j.get v := (Addr.correct j (u ∘ Fin.castSucc)).symm
  have C (a : GateRoutes.Path (triple d) (GateRoutes.S d e)) :=
    GateRoutes.word_eval (fun j => (Addr.fst (a (.fst j)) : Addr s)) u
  have X := C xa v.1.1.2.1.1 (fun _ => rfl); have Y := C ya v.1.1.2.2.1 (fun _ => rfl)
  let refs := network.digits (d:=d) (e:=e) (bitLen p)
  have M : refs.map (fun r => r.eval u) = v.1.1.1 :: (M89S1.digitWord (bitLen p) (value v.1.1.2.1.1) ++
      M89S1.digitWord (bitLen p) (value v.1.1.2.2.1)) := by
    simp only [refs, network.digits, List.map_cons, List.map_append, List.map_ofFn, M89S1.digitWord]
    exact congrArg₂ List.cons (R _) (congrArg₂ List.append (congrArg List.ofFn (funext fun i => X _))
      (congrArg List.ofFn (funext fun i => Y _)))
  have P : (∀ i : Fin η.length, i.val < refs.length ∧ (refs[i.val]?.getD (.pin false)).eval u = η[i]) ↔
      (refs.map (fun r => r.eval u)).take η.length = η := by
    rw [eq_comm, ← List.prefix_iff_eq_take, List.prefix_iff_getElem]; simp only [List.length_map]
    constructor
    · intro h; refine ⟨?_, fun i hi => ?_⟩
      · by_contra! hn; exact Nat.lt_irrefl _ (h ⟨_,hn⟩).1
      · simpa [List.getElem?_eq_getElem (h ⟨i,hi⟩).1] using (h ⟨i,hi⟩).2.symm
    · rintro ⟨hl,h⟩ i; have hi := lt_of_lt_of_le i.isLt hl
      exact ⟨hi, by simpa [List.getElem?_eq_getElem hi] using (h i i.isLt).symm⟩
  have Z := pad_eval (n:=d+1) (fun i : Fin d => Ref.reg (.fst (oa 6 (.fst (.word i))))) u (v.1.2.1 6).1.1 (fun _ => R _)
  have L := pad_eval (n:=d+1) (fun i : Fin d => Ref.reg (.snd (.snd (.snd (.fst (.word i)))))) u v.2.2.2.1 (fun _ => R _)
  simp only [network, joinB_iff]; apply and_congr
  · change (joinB _ (joinB _ _)).OK x ↔ _
    simp only [joinB_iff, RangeRows.block_iff, CurveRows.block_iff, many_iff, D, SignalBank.canonical]; rfl
  · apply and_congr_right'; simp only [rows_iff, decide_eq_true_eq, add_iff]
    apply and_congr
    · apply forall_congr'; intro i
      have A : (network.a6Reg i).eval u = v.2.1 i := R _
      have B' : (network.b6Reg i).eval u = v.2.2.1 i := R _
      have H : (network.coord ya 0).eval u = (value v.1.1.2.2.1).val.testBit 0 := Y 0
      let f (a b y : Bool) := a = (if y then a1 else a0).testBit i ∧ b = (if y then b1 else b0).testBit i
      exact iff_of_eq ((congrArg₂ (fun a b => f a b ((network.coord ya 0).eval u)) A B').trans
        (congrArg (f (v.2.1 i) (v.2.2.1 i)) H))
    · apply and_congr
      · exact ⟨fun h => (R _).symm.trans (h 0), fun h _ => (R _).trans h⟩
      · apply and_congr _ (P.trans (by rw [M]; rfl))
        have cols := S8C.AddLayout.columns_iff (Nat.succ_pos d) (value (v.1.2.1 6).1.1) (value v.2.2.2.1) T true v.2.2.2.2
        apply Iff.trans _ cols; apply iff_of_eq; congr 1 <;> first | exact funext Z | exact funext L

end DetDLP.S8H4.Routes


