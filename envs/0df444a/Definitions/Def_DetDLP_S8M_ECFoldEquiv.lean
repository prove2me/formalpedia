-- Prove2me | Definitions.Def_DetDLP_S8M_ECFoldEquiv
-- name    : DetDLP_S8M_ECFoldEquiv
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T12:34:14.205186+00:00
-- url     : https://prove2.me/theorems/9504b286-43ca-4d24-b4fa-8d829beab077
-- title:
--   Iterated short-Weierstrass addition chain slice uniqueness
-- statement:
--   **Theorem.** Let $P_0,P_1,\ldots,P_n,R$ be points on the short-Weierstrass curve associated to $E$ over $\mathbb F_p$. With the initial, operand, and target wires fixed to their coordinate encodings, the fold block admits an accepted register slice if and only if $P_0+\sum_{i=1}^{n}P_i=R$. In that case the entire slice is unique, including all auxiliary registers. The proof proceeds by induction on the prefix length: single-addition uniqueness fixes the next slice, and its decoded output is the next partial sum. For $n=0$ the final pins compare the initial point directly with $R$.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8M_ECFoldRoutes
import Definitions.Def_DetDLP_S8N_ECAddEquiv

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace DetDLP.S8M.ECFoldEquiv
open S8H0 RegisterMap NamedBlocks ResidueWires SignalBank HashRows RangeRows GateRoutes
open S8H.ECPointArithmetic S8K.ECAddArithmetic S8O.ECAddLayout S8N.ECAddRoutes S8M.ECMapRows
open S8N.ECAddEquiv ECFoldRoutes
open private DetDLP.S8N.ECAddEquiv.decodeAccepted DetDLP.S8N.ECAddEquiv.rows_iff from Definitions.Def_DetDLP_S8N_ECAddEquiv
open private DetDLP.S8M.ECFoldRoutes.foldStep DetDLP.S8M.ECFoldRoutes.outputFlag DetDLP.S8M.ECFoldRoutes.outputX DetDLP.S8M.ECFoldRoutes.outputY from Definitions.Def_DetDLP_S8M_ECFoldRoutes
noncomputable section
variable {p n : ℕ} [Fact p.Prime] {s : Shape}
private abbrev oneShape (p : ℕ) := addShape (width p) (GateSemantics.e p)
abbrev FoldSlice (p n : ℕ) := (foldShape n (width p) (GateSemantics.e p)).Data
private abbrev Point (E : WeierstrassCurve (ZMod p)) := (S8K.SWEquiv.short E).toAffine.Point
abbrev Wires (s : Shape) := Ref s × Word s × Word s
/-- The flag is read directly and both coordinate words represent canonical field values. -/
def Reads (a : Wires s) (v : Bits (s.size+1)) (c : Coords p) : Prop :=
  a.1.eval v = c.1 ∧ evalWord a.2.1 v c.2.1.val ∧ evalWord a.2.2 v c.2.2.val
private abbrev stage (E : WeierstrassCurve (ZMod p)) (a b : Wires s) :=
  @addBlock (width p) (GateSemantics.e p) s (GateSemantics.hd p) p (-1 : ZMod p).val (3 : ZMod p).val (-27*E.c₄).val a.1 a.2.1 a.2.2 b.1 b.2.1 b.2.2
private def canonical (E : WeierstrassCurve (ZMod p)) (P Q : Point E) : (oneShape p).Data :=
  (acceptedSlice_unique E P Q).1.exists.choose
private theorem stage_iff (E : WeierstrassCurve (ZMod p)) (P Q : Point E) (a b : Wires s)
    (f : Path (oneShape p) s) (v : Bits (s.size+1)) (w : (oneShape p).Data) (h : At f v w)
    (ha : Reads a v (coords P)) (hb : Reads b v (coords Q)) :
    (stage E a b f).OK v ↔ w = canonical E P Q := by
  let U := (acceptedSlice_unique E P Q).1
  have hw : Accepted E (coords P) (coords Q) (canonical E P Q) := U.exists.choose_spec
  constructor
  · intro ok; exact U.unique ⟨_,f,v,_,_,_,_,_,_,h,ha.1,hb.1,ha.2.1,ha.2.2,hb.2.1,hb.2.2,ok⟩ hw
  · rintro rfl
    obtain ⟨u,hu,checks⟩ := DetDLP.S8N.ECAddEquiv.decodeAccepted _ _ _ _ hw
    rw [← hu] at h
    exact (DetDLP.S8N.ECAddEquiv.rows_iff _ _ _ u _ f v _ _ _ _ _ _ h ha.1 hb.1 ha.2.1 ha.2.2 hb.2.1 hb.2.2).2 ⟨rfl,checks⟩
private abbrev output (f : Path (oneShape p) s) : Wires s :=
  (.reg (f (.fst (.fst .bit))),word (fun j : Addr (.word (width p)) => f (.fst (.snd (.vec 0 (.fst j))))),
    word (fun j : Addr (.word (width p)) => f (.fst (.snd (.vec 1 (.fst j))))))
private theorem stage_out (E : WeierstrassCurve (ZMod p)) (P Q : Point E) (f : Path (oneShape p) s)
    (v : Bits (s.size+1)) (h : At f v (canonical E P Q)) : Reads (output f) v (coords (P+Q)) := by
  let w := canonical E P Q
  have ho := (acceptedSlice_unique E P Q).2 w (acceptedSlice_unique E P Q).1.exists.choose_spec
  have words (k : Fin 4) := word_eval (fun j : Addr (.word (width p)) => f (.fst (.snd (.vec k (.fst j))))) v (w.1.2 k).1
    (fun i => ((Ref.reg _).correct v).trans (h (.fst (.snd (.vec k (.fst (.word i)))))))
  have hx : (value (w.1.2 0).1).val = (coords (P+Q)).2.1.val := congrArg (fun z : Bool × ℕ × ℕ => z.2.1) ho
  have hy : (value (w.1.2 1).1).val = (coords (P+Q)).2.2.val := congrArg (fun z : Bool × ℕ × ℕ => z.2.2) ho
  exact ⟨(h (.fst (.fst .bit))).trans (congrArg Prod.fst ho),hx ▸ words 0,hy ▸ words 1⟩
private def accum {E : WeierstrassCurve (ZMod p)} (P : Point E) (Ps : Fin n → Point E) (k : ℕ) (hk : k ≤ n) : Point E :=
  P + ∑ j : Fin k, Ps ⟨j.val,by omega⟩
private theorem accum_succ {E : WeierstrassCurve (ZMod p)} (P : Point E) (Ps : Fin n → Point E) (k : Fin n) :
    accum P Ps (k.val+1) k.isLt = accum P Ps k.val k.isLt.le + Ps k := by
  simp [accum, Fin.sum_univ_castSucc,add_assoc]
private abbrev part (q : Path (foldShape n (width p) (GateSemantics.e p)) s) (i : Fin n) : Path (oneShape p) s := fun j => q (.vec i j)
private def wireAt (a : Wires s) (q : Path (foldShape n (width p) (GateSemantics.e p)) s) (k : ℕ) (hk : k ≤ n) : Wires s :=
  if h : k = 0 then a else output (part q ⟨k-1,by omega⟩)
private def transcript {E : WeierstrassCurve (ZMod p)} (P : Point E) (Ps : Fin n → Point E) : FoldSlice p n :=
  fun k => canonical E (accum P Ps k.val k.isLt.le) (Ps k)
private theorem chain {E : WeierstrassCurve (ZMod p)} (P : Point E) (Ps : Fin n → Point E) (a : Wires s) (b : Fin n → Wires s)
    (q : Path (foldShape n (width p) (GateSemantics.e p)) s) (v : Bits (s.size+1)) (w : FoldSlice p n) (h : At q v w)
    (ha : Reads a v (coords P)) (hb : ∀ i, Reads (b i) v (coords (Ps i))) (k : ℕ) (hk : k ≤ n) :
    ((∀ i : Fin n, i.val < k → (stage E (wireAt a q i.val i.isLt.le) (b i) (part q i)).OK v) ↔
      (∀ i : Fin n, i.val < k → w i = transcript P Ps i)) ∧
    ((∀ i : Fin n, i.val < k → w i = transcript P Ps i) → Reads (wireAt a q k hk) v (coords (accum P Ps k hk))) := by
  induction k with
  | zero => simpa [wireAt,accum] using ha
  | succ k ih =>
    let i : Fin n := ⟨k,hk⟩
    obtain ⟨iffPre,outPre⟩ := ih (by omega)
    have H (j : Fin n) : At (part q j) v (w j) := fun t => h (.vec j t)
    have last (pre : ∀ j : Fin n, j.val < k → w j = transcript P Ps j) :=
      stage_iff E (accum P Ps k (by omega)) (Ps i) (wireAt a q k (by omega)) (b i) (part q i) v (w i) (H i) (outPre pre) (hb i)
    constructor
    · constructor
      · intro ok
        have pre := iffPre.mp (fun j hj => ok j (by omega))
        intro j hj; by_cases hlt : j.val < k
        · exact pre j hlt
        · have eq : j = i := Fin.ext (by change j.val = k; omega)
          subst j; exact (last pre).mp (ok i (Nat.lt_succ_self _))
      · intro eq
        have pre := fun j (hj : j.val < k) => eq j (by omega)
        intro j hj; by_cases hlt : j.val < k
        · exact iffPre.mpr pre j hlt
        · have hji : j = i := Fin.ext (by change j.val = k; omega)
          subst j; exact (last pre).mpr (eq i (Nat.lt_succ_self _))
    · intro eq
      have ht := H i
      rw [eq i (Nat.lt_succ_self _)] at ht
      change Reads (wireAt a q (i.val+1) _) v (coords (accum P Ps (i.val+1) _))
      rw [accum_succ]; simpa [wireAt] using stage_out E (accum P Ps k (by omega)) (Ps i) (part q i) v ht
private theorem val_eq (x y : ZMod p) (h : ∀ i : Fin (width p), x.val.testBit i = y.val.testBit i) : x = y := by
  apply ZMod.val_injective; apply Nat.eq_of_testBit_eq; intro i
  by_cases hi : i < width p
  · exact h ⟨i,hi⟩
  · have bound : p < 2^i := (fits p).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    rw [Nat.testBit_lt_two_pow (x.val_lt.trans bound),Nat.testBit_lt_two_pow (y.val_lt.trans bound)]
private theorem pins_iff {E : WeierstrassCurve (ZMod p)} (P R : Point E) (a b : Wires s) (v : Bits (s.size+1))
    (ha : Reads a v (coords P)) (hb : Reads b v (coords R)) :
    (a.1.eval v = b.1.eval v ∧ (∀ i : Fin (width p), (a.2.1 i).eval v = (b.2.1 i).eval v) ∧
        (∀ i : Fin (width p), (a.2.2 i).eval v = (b.2.2 i).eval v)) ↔ P = R := by
  simp only [ha.1,hb.1,show ∀ j, _ from fun (j : ℕ) => ha.2.1 j,
    show ∀ j, _ from fun (j : ℕ) => hb.2.1 j,show ∀ j, _ from fun (j : ℕ) => ha.2.2 j,
    show ∀ j, _ from fun (j : ℕ) => hb.2.2 j]
  constructor
  · rintro ⟨hf,hx,hy⟩
    have h : coords P = coords R := Prod.ext hf (Prod.ext (val_eq _ _ hx) (val_eq _ _ hy))
    cases P <;> cases R <;> simp_all [coords]
  · rintro rfl; simp
private abbrev routed (E : WeierstrassCurve (ZMod p)) (a : Wires s) (b : Fin n → Wires s) (t : Wires s) :=
  @foldBlock s n (width p) (GateSemantics.e p) (GateSemantics.hd p) p (-1 : ZMod p).val (3 : ZMod p).val (-27*E.c₄).val
    a.1 a.2.1 a.2.2 (fun i => (b i).1) (fun i => (b i).2.1) (fun i => (b i).2.2) t.1 t.2.1 t.2.2
/-- Acceptance is realizability of the physical fold block with all external triples fixed. -/
def FoldAccepted (E : WeierstrassCurve (ZMod p)) (P : Point E) (Ps : Fin n → Point E) (R : Point E) (w : FoldSlice p n) : Prop :=
  ∃ (s : Shape) (q : Path (foldShape n (width p) (GateSemantics.e p)) s) (v : Bits (s.size+1))
    (a : Wires s) (b : Fin n → Wires s) (t : Wires s), At q v w ∧ Reads a v (coords P) ∧
    (∀ i, Reads (b i) v (coords (Ps i))) ∧ Reads t v (coords R) ∧ (routed E a b t q).OK v
/-- Characterization in an arbitrary bank, even if the register path aliases addresses. -/
theorem foldRows (E : WeierstrassCurve (ZMod p)) (P : Point E) (Ps : Fin n → Point E) (R : Point E)
    (a : Wires s) (b : Fin n → Wires s) (t : Wires s) (q : Path (foldShape n (width p) (GateSemantics.e p)) s)
    (v : Bits (s.size+1)) (w : FoldSlice p n) (h : At q v w) (ha : Reads a v (coords P))
    (hb : ∀ i, Reads (b i) v (coords (Ps i))) (ht : Reads t v (coords R)) :
    (routed E a b t q).OK v ↔ w = transcript P Ps ∧ P + ∑ i, Ps i = R := by
  rw [foldBlock_iff]
  have step (i : Fin n) : (DetDLP.S8M.ECFoldRoutes.foldStep (GateSemantics.hd p) p (-1 : ZMod p).val (3 : ZMod p).val (-27*E.c₄).val a.1 a.2.1 a.2.2 (fun j => (b j).1) (fun j => (b j).2.1) (fun j => (b j).2.2) q i).OK v ↔
      (stage E (wireAt a q i.val i.isLt.le) (b i) (part q i)).OK v := by
    by_cases hi : i.val = 0 <;> simp [DetDLP.S8M.ECFoldRoutes.foldStep,wireAt,hi,stage,part,output]
  simp only [step]
  have C := chain P Ps a b q v w h ha hb n le_rfl
  simp only [Fin.is_lt, forall_const] at C
  have out (hw : ∀ i, w i = transcript P Ps i) := pins_iff (accum P Ps n le_rfl) R (wireAt a q n le_rfl) t v (C.2 hw) ht
  have pin (hw : ∀ i, w i = transcript P Ps i) := out hw
  constructor
  · rintro ⟨oks,hf,hx,hy⟩
    have hw := C.1.mp oks
    refine ⟨funext hw,(pin hw).mp ?_⟩
    by_cases hn : n = 0 <;> simpa [wireAt,DetDLP.S8M.ECFoldRoutes.outputFlag,DetDLP.S8M.ECFoldRoutes.outputX,DetDLP.S8M.ECFoldRoutes.outputY,hn] using And.intro hf (And.intro hx hy)
  · rintro ⟨rfl,hs⟩
    have hw := fun i => (rfl : transcript P Ps i = _)
    refine ⟨C.1.mpr hw,?_⟩
    have eq := (pin hw).mpr hs
    by_cases hn : n = 0 <;> simpa [wireAt,DetDLP.S8M.ECFoldRoutes.outputFlag,DetDLP.S8M.ECFoldRoutes.outputX,DetDLP.S8M.ECFoldRoutes.outputY,hn] using eq
private def pins (c : Coords p) : Wires s := (.pin c.1,pub c.2.1.val,pub c.2.2.val)
omit [Fact p.Prime] in
private theorem pins_read (c : Coords p) (v : Bits (s.size+1)) : Reads (pins c) v c := ⟨rfl,fun _ => rfl,fun _ => rfl⟩
/-- The fiber of the pinned fold block is empty off the sum and a singleton on it. -/
theorem foldSlice_unique (E : WeierstrassCurve (ZMod p)) (P : (S8K.SWEquiv.short E).toAffine.Point)
    (Ps : Fin n → (S8K.SWEquiv.short E).toAffine.Point) (R : (S8K.SWEquiv.short E).toAffine.Point) :
    ((∃ w : FoldSlice p n, FoldAccepted E P Ps R w) ↔ P + ∑ i, Ps i = R) ∧
    (P + ∑ i, Ps i = R → ∃! w : FoldSlice p n, FoldAccepted E P Ps R w) := by
  let w := transcript P Ps
  have sound {z} (hz : FoldAccepted E P Ps R z) : z = w ∧ P + ∑ i, Ps i = R := by
    obtain ⟨s,q,v,a,b,t,h,ha,hb,ht,ok⟩ := hz
    exact (foldRows E P Ps R a b t q v z h ha hb ht).mp ok
  have complete (hs : P + ∑ i, Ps i = R) : FoldAccepted E P Ps R w := by
    let S := foldShape n (width p) (GateSemantics.e p)
    let v : Bits (S.size+1) := Fin.lastCases false (S.decode.symm w)
    have h : At id v w := by intro j; change v j.index.castSucc = _; simp [v,← Addr.correct j (S.decode.symm w)]
    exact ⟨S,id,v,pins _,fun i => pins (coords (Ps i)),pins _,h,pins_read _ _,fun _ => pins_read _ _,pins_read _ _,
      (foldRows E P Ps R _ _ _ id v w h (pins_read _ _) (fun _ => pins_read _ _) (pins_read _ _)).mpr ⟨rfl,hs⟩⟩
  exact ⟨⟨fun ⟨_,hz⟩ => (sound hz).2,fun hs => ⟨w,complete hs⟩⟩,fun hs => ⟨w,complete hs,fun _ hz => (sound hz).1⟩⟩
end
end DetDLP.S8M.ECFoldEquiv


