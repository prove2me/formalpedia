-- Prove2me | Definitions.Def_DetDLP_S8L_RowSound
-- name    : DetDLP_S8L_RowSound
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T08:30:28.496724+00:00
-- url     : https://prove2.me/theorems/318ce813-557f-4045-8dc2-87935b8e8f50
-- title:
--   Arithmetic semantics of the routed Tag 5 rows
-- statement:
--   For a register assignment at width $d$, the atom rows accept exactly when the decoded words satisfy the strict range checks, the nonzero successor equation, and the M5 affine hash constraints. Each product stage accepts exactly when both routed multiplications and their full-width addition agree with the designated input and output registers.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8L_Routes

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace DetDLP.S8L.RowSound
open S8H0 S8H0.RegisterMap S8H0.NamedBlocks S8H0.ResidueWires S8H0.SignalBank S8H0.HashRows S8H0.GateRoutes
variable {p m d : ℕ} {hd : 1 ≤ d}
abbrev Input (m d : ℕ) (hd : 1 ≤ d) := Bits ((Routes.bank m d (Routes.G hd)).size+1)
abbrev raw (u : Input m d hd) := (Routes.bank m d (Routes.G hd)).decode (u ∘ Fin.castSucc)
abbrev Atom (d : ℕ) (hd : 1 ≤ d) := (Routes.atom d (Routes.G hd)).Data
abbrev slot (v : Atom d hd) := v.2.2.2.1
abbrev bounds (p T : ℕ) (v : Atom d hd) := below p v.1 ∧ below (min T p) v.2.2.1 ∧ below p (slot v).1 ∧ below p (slot v).2.1.1
noncomputable abbrev cert (hp : p ≤ 2^d) (v : Atom d hd) (h : below p (slot v).2.1.1) : w3_fpHashCert d p hd :=
  let s := (slot v).2
  ((finEquiv hp ⟨s.1.1,h⟩,value s.1.2.1,mulEquiv hd s.1.2.2.1,mulEquiv hd s.1.2.2.2),s.2)
abbrev num {n : ℕ} (u : Bits n) := (value u).val
abbrev nz (v : Atom d hd) := w3_addColumns d (num v.2.1.1) 0 (num v.1.1) true v.2.1.2
abbrev constraint (hp : p ≤ 2^d) (T : ℕ) (c : ℕ × ℕ) (v : Atom d hd) :=
  ∃ h : bounds p T v, nz v ∧ (slot v).1.1 = v.2.2.1.1 ∧ w3_slotHashBits hd c.1 c.2 (num v.1.1)
    (num (slot v).1.1) (cert hp v h.2.2.2) (auxEquiv d v.2.2.2.2)
abbrev idx (i : Fin (2*m)) : Fin m := ⟨i%m,Nat.mod_lt _ (by clear * - i; have := i.isLt; omega)⟩

theorem atom_iff (hp : p ≤ 2^d) (T : ℕ) (cs : Fin m → ℕ × ℕ) (i : Fin (2*m)) (u : Input m d hd) :
    (Routes.atomRows hd p T cs i).OK u ↔ constraint hp T (cs (idx i)) ((raw u).1 i) := by
  let v := (raw u).1 i
  let c := cs (idx i)
  let w := Routes.hash hd p c i
  have reg (a : Addr (Routes.bank m d (Routes.G hd))) := (Addr.correct a (u ∘ Fin.castSucc)).symm
  have E := word_eval (n:=d) (fun j => Routes.A (e:=Routes.G hd) i (.fst (.fst j))) u v.1.1 (fun _ => rfl)
  have Z := word_eval (n:=d) (fun j => Routes.R (e:=Routes.G hd) i (.fst (.fst j))) u (slot v).1.1 (fun _ => rfl)
  have H (h : below p (slot v).2.1.1) : (HashRows.block p w).OK u ↔ w3_slotHashBits hd c.1 c.2 (num v.1.1)
      (num (slot v).1.1) (cert hp v h) (auxEquiv d v.2.2.2.2) := by
    apply block_spec hd _ u c.1 (num v.1.1) c.2 _ _ _ (fun _ => rfl) E (fun _ => rfl) Z
    · exact word_eval (fun j => Routes.R i (.snd (.fst (.fst (.fst j))))) u (slot v).2.1.1.1 (fun _ => rfl)
    · exact word_eval (fun j => Routes.R i (.snd (.fst (.snd (.fst j))))) u (slot v).2.1.2.1 (fun _ => rfl)
    · exact word_eval (fun j => Routes.M₁ i (.fst j)) u (slot v).2.1.2.2.1.1 (fun _ => rfl)
    · exact word_eval (fun j => Routes.M₂ i (.fst j)) u (slot v).2.1.2.2.2.1 (fun _ => rfl)
    · exact word_eval (fun j => Routes.H i (.snd (.fst j))) u v.2.2.2.2.2.1 (fun _ => rfl)
    · intro j; rw [← Ref.correct]; let flag : Bool := (slot v).2.2
      change (p.testBit j && flag) = (if flag then p else 0).testBit j
      cases flag <;> simp
    all_goals funext j; rw [← Ref.correct]; rfl
  have K := RangeRows.checker_iff p (fun j => Routes.A i (.fst j)) u v.1 (fun _ => reg _)
  have Kz := RangeRows.checker_iff p (fun j => Routes.R i (.fst j)) u (slot v).1 (fun _ => reg _)
  have Kr := RangeRows.checker_iff p (fun j => Routes.R i (.snd (.fst (.fst j)))) u (slot v).2.1.1 (fun _ => reg _)
  have Kt := RangeRows.checker_iff (min T p) (fun j => Routes.A i (.snd (.snd (.fst j)))) u v.2.2.1 (fun _ => reg _)
  simp only [Routes.atomRows,joinB_iff,K,Kz,Kr,Kt,add_iff,eqs_iff]
  have N := S8C.AddLayout.columns_iff hd (num v.2.1.1) 0 (num v.1.1) true v.2.1.2
  have V (b : Bits d) : (fun i : Fin d => (num b).testBit i.val) = b := funext (value_bit b)
  rw [V v.2.1.1,V v.1.1] at N; simp only [Nat.zero_testBit] at N
  have En (j : Fin d) : (Routes.elem i j).eval u = v.1.1 j := (E j).trans (value_bit _ j)
  have Zn (j : Fin d) : (w.z j).eval u = (slot v).1.1 j := (Z j).trans (value_bit _ j)
  simp only [En, ← Ref.correct, Ref.data] at *
  constructor
  · rintro ⟨hh,hx,hn,hz,hr,ht,he⟩
    exact ⟨⟨hx,ht,hz,hr⟩,N.mp hn,funext (fun j => (Zn j).symm.trans (he j)),(H hr).mp hh⟩
  · rintro ⟨⟨hx,ht,hz,hr⟩,hn,he,hh⟩
    exact ⟨(H hr).mpr hh,hx,N.mpr hn,hz,hr,ht,fun j => (Zn j).trans (congrFun he j)⟩

abbrev Stage (d : ℕ) (hd : 1 ≤ d) := (S8G.FpAtomRows.stageShape d (Routes.G hd)).Data
abbrev stepCert (s : Stage d hd) := (value s.1,mulEquiv hd s.2.1,mulEquiv hd s.2.2.1)
abbrev step (p x y z : ℕ) (s : Stage d hd) :=
  w3_slotMulInc hd x y (stepCert s).2.1 ∧ w3_slotMulInc hd (stepCert s).1.val p (stepCert s).2.2 ∧
  w3_addColumns (2*d) (num s.2.2.1.1) z (num s.2.1.1) false s.2.2.2
abbrev inputX (v : (Routes.bank m d (Routes.G hd)).Data) (i : Fin (2*m-1)) :=
  if h : i.val = 0 then num (v.1 ⟨0,by have := i.isLt; omega⟩).1.1 else num (v.2.2 ⟨i-1,by have := i.isLt; omega⟩).1
abbrev outputZ (X : ℕ) (v : (Routes.bank m d (Routes.G hd)).Data) (i : Fin (2*m-1)) :=
  if h : i.val < 2*m-2 then num (v.2.2 ⟨i,h⟩).1 else X

theorem stage_iff (p X : ℕ) (i : Fin (2*m-1)) (u : Input m d hd) :
    (Routes.stage hd p X i).OK u ↔ step p (inputX (raw u) i) (num ((raw u).1 ⟨i+1,by have := i.isLt; omega⟩).1.1)
      (outputZ X (raw u) i) ((raw u).2.1 i) := by
  let s := (raw u).2.1 i
  have E (k : Fin (2*m)) : evalWord (Routes.elem k) u (num ((raw u).1 k).1.1) :=
    word_eval _ u ((raw u).1 k).1.1 (fun _ => rfl)
  have I (k : Fin (2*m-2)) : evalWord (Routes.acc k) u (num ((raw u).2.2 k).1) :=
    word_eval _ u ((raw u).2.2 k).1 (fun _ => rfl)
  let a : Path (S8G.FpAtomRows.stageShape d (Routes.G hd)) (Routes.bank m d (Routes.G hd)) := fun j => .snd (.fst (.vec i j))
  have Q := word_eval (fun j => a (.fst j)) u s.1 (fun _ => rfl)
  have U := word_eval (fun j => a (.snd (.fst (.fst j)))) u s.2.1.1 (fun _ => rfl)
  have V := word_eval (fun j => a (.snd (.snd (.fst (.fst j))))) u s.2.2.1.1 (fun _ => rfl)
  unfold Routes.stage inputX outputZ; rw [S8G.FpAtomRows.stageBlock_iff]
  split_ifs
  all_goals rw [product_spec hd _ _ _ _ u (value s.2.1.1) (by first | exact E _ | exact I _) (E _) U,
    product_spec hd _ _ _ _ u (value s.2.2.1.1) Q (fun _ => rfl) V,
    sum_spec (by omega : 0 < 2*d) _ _ _ _ u V (by first | exact I _ | exact fun _ => rfl) U]
  all_goals simp only [← Ref.correct,Ref.data]; rfl

end DetDLP.S8L.RowSound


