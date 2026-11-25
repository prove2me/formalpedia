-- Prove2me | Definitions.Def_DetDLP_S8G_ChainOnlyEquiv
-- name    : DetDLP_S8G_ChainOnlyEquiv
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T09:52:23.843291+00:00
-- url     : https://prove2.me/theorems/a593eeb0-3568-4083-87b2-6b791ca566d0
-- title:
--   Product-chain slice bijection for a fixed endpoint
-- statement:
--   Fix a prime $p$, a tuple of units $A_0,\ldots,A_n$ with $n>0$, and an endpoint $z$. The routed rows check the internal residues and multiplication stages, writing the last result directly to $z$. The physical slice and the accepted product runs are both empty unless $z$ represents $\prod_{i=0}^n A_i$. At that endpoint each has exactly one witness, yielding the equivalence `chainEquiv`.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8G_Routes
import Definitions.Def_DetDLP_S8L_ChainLift
import Theorems.Thm_DetDLP_w3_m5_modmul_r2

set_option autoImplicit false
namespace DetDLP.S8G.ChainSliceEquiv
open S8H0 RegisterMap NamedBlocks RangeRows HashRows GateRoutes ResidueWires Routes FpAtomRows
open S8L (ChainLift.Bank RowSound.step)
noncomputable section
variable {p n : ℕ} [Fact p.Prime] {s : Shape}
private abbrev d (p : ℕ) := S8C.atomWidth p
private abbrev hd (p : ℕ) : 1 ≤ d p := Nat.succ_pos _
abbrev Slice (p n : ℕ) := (chainShape n (d p) (edges (hd p))).Data
private def seq (A : Fin (n+1) → (ZMod p)ˣ) (k : ℕ) : ZMod p := if h : k < n+1 then A ⟨k,h⟩ else 1
abbrev chainValid (A : Fin (n+1) → (ZMod p)ˣ) (z : Fin p) (v : Slice p n) :=
  S8L.ChainLift.OK (n:=n+1) (seq A) (z.val : ZMod p) v

/-- A physical stage uses its two multiplication witnesses and the column carries of their sum. -/
private theorem stageRows (r : Path (stageShape (d p) (edges (hd p))) s) (v : S8L.RowSound.Stage (d p) (hd p))
    (u : Bits (s.size+1)) (hv : ∀ j, (r j).get (s.decode (u ∘ Fin.castSucc)) = j.get v)
    (x y z : Word s) {X Y Z : ℕ} (hx : evalWord x u X) (hy : evalWord y u Y) (hz : evalWord z u Z) :
    (stageBlock (hd p) p x y (word (n:=d p) fun a => r (.fst a))
      (word (n:=2*d p) fun a => r (.snd (.fst (.fst a)))) (word (n:=2*d p) fun a => r (.snd (.snd (.fst (.fst a))))) z
      (fun k => (word (n:=edges (hd p)) fun a => r (.snd (.fst (.snd a)))) k)
      (fun k => (word (n:=edges (hd p)) fun a => r (.snd (.snd (.fst (.snd a))))) k)
      (fun k => .reg (r (.snd (.snd (.snd (.word k))))))).OK u ↔ S8L.RowSound.step p X Y Z v := by
  have q := word_eval (fun a => r (.fst a)) u v.1 (fun i => hv (.fst (.word i)))
  have l := word_eval (fun a => r (.snd (.fst (.fst a)))) u v.2.1.1 (fun i => hv (.snd (.fst (.fst (.word i)))))
  have b := word_eval (fun a => r (.snd (.snd (.fst (.fst a))))) u v.2.2.1.1 (fun i => hv (.snd (.snd (.fst (.fst (.word i))))))
  rw [stageBlock_iff,product_spec _ _ _ _ _ _ _ hx hy l,product_spec _ _ _ _ _ _ _ q (fun _ => rfl) b,
    sum_spec (by have := hd p; omega) _ _ _ _ _ b hz l]
  have R (a) := ((Ref.reg (r a)).correct u).symm.trans (hv a)
  have W {k} (f : Path (.word k) (stageShape (d p) (edges (hd p)))) (i : Fin k) :
      (word (fun j => r (f j)) i).eval u = (f (.word i)).get v := by simpa [word,padded,i.isLt] using R (f (.word i))
  have a := funext (W (k:=edges (hd p)) (fun j => .snd (.fst (.snd j))))
  have b' := funext (W (k:=edges (hd p)) (fun j => .snd (.snd (.fst (.snd j)))))
  have c := funext (fun i : Fin (2*d p) => R (.snd (.snd (.snd (.word i)))))
  rw [a,b',c]; rfl

/-- Identify the routed predicate with the S8L chain predicate, including the last external output. -/
theorem chainRows (hn : 0 < n) (A : Fin (n+1) → (ZMod p)ˣ) (z : Fin p) (v : Slice p n)
    (q : Path (chainShape n (d p) (edges (hd p))) s) (u : Bits (s.size+1))
    (hv : ∀ j, (q j).get (s.decode (u ∘ Fin.castSucc)) = j.get v)
    (x : Word s) (ys : Fin n → Word s) (o : Word s) (hx : evalWord x u (w3_fpResidue (A 0)).val)
    (hy : ∀ i, evalWord (ys i) u (w3_fpResidue (A i.succ)).val) (ho : evalWord o u z.val) :
    (chainBlock (hd p) p x ys o q).OK u ↔ chainValid A z v := by
  rw [chainBlock_iff]; simp only [Nat.ne_of_gt hn,false_implies,true_and]
  have R (i) := checker_iff p (internal q i) u (v.2 i) (fun a => ((Ref.reg _).correct u).symm.trans (hv (.snd (.vec i a))))
  simp only [R]; apply and_congr_right; intro hr; apply forall_congr'; intro i
  have E (k) := word_eval (fun a => internal q k (.fst a)) u (v.2 k).1 (fun j => hv (.snd (.vec k (.fst (.word j)))))
  have B (k) : (value (v.2 k).1).val < p := (finEquiv (S8C.primeFitsAtom p).le ⟨v.2 k,hr k⟩).isLt
  unfold stageAt; apply stageRows _ _ u (fun j => hv (.fst (.vec i j)))
  · unfold S8L.ChainLift.acc; split_ifs <;> first
      | simpa [seq,w3_fpResidue] using hx
      | rw [ZMod.val_natCast_of_lt (B _)]; exact E _
      | omega
  · unfold seq; rw [dif_pos (show i.val+1 < n+1 by omega)]; exact hy i
  · unfold S8L.ChainLift.acc; rw [dif_neg (Nat.succ_ne_zero i.val)]; by_cases H : i.val < n-1
    · rw [dif_pos H,dif_pos (show i.val+1 < n+1-1 by omega),ZMod.val_natCast_of_lt (B _)]; exact E _
    · rw [dif_neg H,dif_neg (show ¬i.val+1 < n+1-1 by omega),ZMod.val_natCast_of_lt z.isLt]; exact ho

/-- Both fibers are empty off the product, and each has exactly one inhabitant at the product. -/
def chainEquiv (hn : 0 < n) (A : Fin (n+1) → (ZMod p)ˣ) (z : Fin p) :
    {v : Slice p n // chainValid A z v} ≃ {r : S8C.ProductRun p // FpMoment.chainOK A z r} := by
  have L := S8L.ChainLift.chainLift (seq A) (z.val : ZMod p) (n:=n+1) (by omega)
  have P : S8L.ChainLift.partialProd (seq A) n = ((∏ i, A i : (ZMod p)ˣ) : ZMod p) := by
    rw [S8L.ChainLift.partialProd,← Fin.prod_univ_eq_prod_range,Units.coe_prod]; exact Finset.prod_congr rfl (fun i _ => dif_pos i.isLt)
  have H : (z.val : ZMod p) = S8L.ChainLift.partialProd (seq A) (n+1-1) ↔ z = w3_fpResidue (∏ i, A i) := by
    rw [Nat.add_sub_cancel,P,← (ZMod.val_injective p).eq_iff,ZMod.val_natCast_of_lt z.isLt]; exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  have U := FpMoment.chainUnique w3_m5_modmul_r2 A
  by_cases h : z = w3_fpResidue (∏ i, A i)
  · subst z; have V := L.2 (H.mpr rfl)
    exact ⟨fun _ => ⟨_,U.exists.choose_spec⟩,fun _ => ⟨_,V.exists.choose_spec⟩,
      fun v => Subtype.ext (V.unique V.exists.choose_spec v.prop),fun r => Subtype.ext (U.unique U.exists.choose_spec r.prop)⟩
  · exact ⟨fun v => False.elim (h (H.mp (L.1 _ v.prop))),fun r => False.elim (h (FpMoment.chainSound w3_m5_modmul_r2 _ _ _ r.prop)),
      fun v => False.elim (h (H.mp (L.1 _ v.prop))),fun r => False.elim (h (FpMoment.chainSound w3_m5_modmul_r2 _ _ _ r.prop))⟩
end
end DetDLP.S8G.ChainSliceEquiv


