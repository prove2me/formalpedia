-- Prove2me | Definitions.Def_DetDLP_S8H0_GateSemantics
-- name    : DetDLP_S8H0_GateSemantics
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T07:34:32.669847+00:00
-- url     : https://prove2.me/theorems/5e376afb-7a8f-46d8-8467-26d6cd32f7d7
-- title:
--   Correctness of elliptic-curve gate routing
-- statement:
--   For canonical assignments, the routed local tests at each of the seven gates are equivalent to the corresponding typed arithmetic verification steps.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8H0_GateRoutes

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace DetDLP.S8H0.GateSemantics
open RegisterMap NamedBlocks ResidueWires SignalBank HashRows RangeRows GateRoutes
open S8H.ECPointArithmetic S8H.ECPointSlots

variable {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))
abbrev d (p : ℕ) := width p
abbrev hd (p : ℕ) : 1 ≤ d p := Nat.succ_pos _
abbrev e (p : ℕ) := (w4_M5GraphBounds.graph (d p) (hd p)).nE
abbrev U (p : ℕ) := Bits ((S (d p) (e p)).size+1)
abbrev raw (u : U p) : Bank (d p) (hd p) := (S (d p) (e p)).decode (u ∘ Fin.castSucc)
noncomputable abbrev typed (u : U p) (h : canonical p (raw u)) := decode (p:=p) ⟨raw u,h⟩
def coeff := Coeff.mk E.a₁.val E.a₂.val E.a₃.val E.a₄.val E.a₆.val

theorem resVal (v : Triple (d p)) (h : below p v) :
    (zmodEquiv (fits p).le ⟨v,h⟩).val = (value v.1).val := by
  let r := finEquiv (fits p).le ⟨v,h⟩
  exact (ZMod.val_natCast_of_lt r.isLt).trans (finEquiv_val _ _)

variable (u : U p) (h : canonical p (raw u))

theorem coordX : (typed u h).1.2.1.val = (value (raw u).1.2.1.1).val := resVal _ h.1.1
theorem coordY : (typed u h).1.2.2.val = (value (raw u).1.2.2.1).val := resVal _ h.1.2
theorem outVal (g : Fin 7) : ((typed u h).2.1 g).1.val = (value ((raw u).2.1 g).1.1).val := resVal _ (h.2 g).1

private theorem rawR (a : Path (triple (d p)) (S (d p) (e p))) (r : Triple (d p))
    (hr : ∀ i : Fin (d p), (a (.fst (.word i))).get (raw u) = r.1 i) :
    evalWord (rword a) u (value r.1).val := word_eval _ u r.1 hr

private theorem inputs (g : Fin 7) :
    let a := SevenChecks.gateArgs E (typed u h).1 (typed u h).2 g
    evalWord ((operands (coeff E) g).1) u a.1.val ∧ evalWord ((operands (coeff E) g).2.1) u a.2.1.val ∧
      evalWord ((operands (coeff E) g).2.2) u a.2.2.val := by
  have X := rawR u xa (raw u).1.2.1 (fun _ => rfl)
  have Y := rawR u ya (raw u).1.2.2 (fun _ => rfl)
  have O (i : Fin 7) := rawR u (oa i) ((raw u).2.1 i).1 (fun _ => rfl)
  have O' (i : Fin 7) : evalWord (rword (oa i)) u ((typed u h).2.1 i).1.val := (outVal u h i).symm ▸ O i
  rw [←coordX u h] at X; rw [←coordY u h] at Y
  have P (n : ℕ) : evalWord (pub n) u n := fun _ => rfl
  have hone : (1 : ZMod p).val = 1 := by
    simpa only [Nat.cast_one] using (ZMod.val_natCast_of_lt (Fact.out : p.Prime).one_lt)
  fin_cases g <;> simp [SevenChecks.gateArgs,operands,args,coeff,hone] <;> exact ⟨by first | apply P | assumption | apply O', by first | apply P | assumption | apply O', by first | apply P | assumption | apply O'⟩

theorem hash_iff (g : Fin 7) :
    let v := typed u h; let a := SevenChecks.gateArgs E v.1 v.2 g
    (HashRows.block p (wires (hd p) p (coeff E) g)).OK u ↔
      w3_slotHashBits (hd p) a.1.val a.2.2.val a.2.1.val (v.2.1 g).1.val (v.2.1 g).2 (v.2.2 g) := by
  let v := typed u h; let a := SevenChecks.gateArgs E v.1 v.2 g
  have I := inputs E u h g
  apply block_spec (hd p) _ u a.1.val a.2.1.val a.2.2.val (v.2.1 g).1.val (v.2.1 g).2 (v.2.2 g) I.1 I.2.1 I.2.2
  · rw [outVal u h]; exact rawR u (oa g) ((raw u).2.1 g).1 (fun _ => rfl)
  · exact rawR u (ra g) ((raw u).2.1 g).2.1.1 (fun _ => rfl)
  · exact word_eval (fun a => runPath g (.snd (.fst (.snd (.fst a))))) u ((raw u).2.1 g).2.1.2.1 (fun _ => rfl)
  · exact word_eval (fun a => m1 g (.fst a)) u ((raw u).2.1 g).2.1.2.2.1.1 (fun _ => rfl)
  · exact word_eval (fun a => m2 g (.fst a)) u ((raw u).2.1 g).2.1.2.2.2.1 (fun _ => rfl)
  · exact word_eval (fun a => aux g (.snd (.fst a))) u ((raw u).2.2 g).2.1 (fun _ => rfl)
  · intro i
    have H := ((Ref.masked (p.testBit i) (cm g)).correct u).symm
    change ((Ref.masked (p.testBit i) (cm g)).eval u) = (if ((raw u).2.1 g).2.2 then p else 0).testBit i
    rw [H]; change (p.testBit i && ((raw u).2.1 g).2.2) = _
    cases ((raw u).2.1 g).2.2 <;> simp
  all_goals funext i; exact (Addr.correct _ (u ∘ Fin.castSucc)).symm

end DetDLP.S8H0.GateSemantics


