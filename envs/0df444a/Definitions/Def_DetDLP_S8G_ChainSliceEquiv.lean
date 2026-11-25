-- Prove2me | Definitions.Def_DetDLP_S8G_ChainSliceEquiv
-- name    : DetDLP_S8G_ChainSliceEquiv
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T10:21:01.72015+00:00
-- url     : https://prove2.me/theorems/7584d6b2-16a9-432d-8548-f98274e6c895
-- title:
--   Tag 1 product-chain slice bijection and full Transcript runs equivalence
-- statement:
--   Let $p$ be prime, $m=\operatorname{blockCount}(\operatorname{bitLen}(p))$, and $T\le p$. For each $j\in\{0,1,2,3\}$ and admissible prefix $\eta$, `runs` gives a bijection from satisfying Boolean assignments of the moment layout to `FpMoment.Transcript` at tag $j$. The seed and atom rows recover the coefficients and checked atom runs. At tag $3$, both chains have $m-1$ stages and finish at the same range-checked residue; the transcript retains both product runs.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8G_SeedSliceEquiv
import Definitions.Def_DetDLP_S8G_AtomSliceEquiv
import Theorems.Thm_DetDLP_w3_m5_modmul_r2
import Definitions.Def_DetDLP_S8G_ChainOnlyEquiv

set_option autoImplicit false
set_option maxHeartbeats 350000
namespace DetDLP.S8G.ChainSliceEquiv
open S8H0 S8C RegisterMap NamedBlocks RangeRows HashRows GateRoutes ResidueWires SeedAndAtomBank Routes
open SignalBank SeedSliceEquiv AtomSliceEquiv FpMoment
noncomputable section
private abbrev D := atomWidth
private abbrev H (p : ℕ) : 1 ≤ D p := Nat.succ_pos _
private abbrev G (p : ℕ) := edges (H p)
variable {p n : ℕ} [Fact p.Prime] {s : Shape}

/-- Convert the atom bank's physical rows to the predicates used by its decoding equivalence. -/
theorem atomRows (S : FpSeed p n) (T : ℕ) (q : Path (atomBankShape n (D p) (G p)) s)
    (u : Bits (s.size+1)) (v : (atomBankShape n (D p) (G p)).Data)
    (hv : ∀ j, (q j).get (s.decode (u ∘ Fin.castSucc)) = j.get v) (a b : Fin n → Word s)
    (ha : ∀ i, evalWord (a i) u ((S i).1.val+1)) (hb : ∀ i, evalWord (b i) u (S i).2.val) :
    (atomBankBlock (H p) p n T a b q).OK u ↔ atomBankOK S T v := by
  rw [atomBank_iff]; apply forall_congr'; intro i
  let t := v i; let r := t.2.2.2.1; let w := t.2.2.2.2; let f := fun j => q (.vec i j)
  have reg (j) := ((Ref.reg (f j)).correct u).symm.trans (hv (.vec i j))
  have W {k} (g : Path (.word k) (atomSlot (D p) (G p))) (t' : Bits k) (h : ∀ j, (g (.word j)).get t = t' j) :=
    word_eval (fun j => f (g j)) u t' (fun i' => (hv (.vec i _)).trans (h i'))
  have X := W (fun j => .fst (.fst j)) t.1.1 (fun _ => rfl)
  unfold atomSlotBlock; dsimp only; simp only [joinB_iff]; rw [checker_iff _ _ _ t.1 (fun j => reg (.fst j)),
    orRows_iff _ _ _ _ _ _ (fun j => X j), checker_iff _ _ _ r.1 (fun j => reg (.snd (.snd (.snd (.fst (.fst j)))))),
    checker_iff _ _ _ (r.1.1,t.2.2.1) (fun j => by cases j <;> apply reg),
    checker_iff _ _ _ r.2.1.1 (fun j => reg (.snd (.snd (.snd (.fst (.snd (.fst (.fst j))))))))]
  have orE := funext (fun j : Fin (D p) => reg (.snd (.fst (.word j))))
  rw [orE,below_iff T]; let hp := (primeFitsAtom p).le
  have B (z : Triple (D p)) (h : below p z) : (value z.1).val < p := (finEquiv hp ⟨z,h⟩).isLt
  have F (z : Triple (D p)) (h : below p z) : ((zmodFin p) (finEquiv hp ⟨z,h⟩)).val = (value z.1).val := ZMod.val_natCast_of_lt (B z h)
  let cert (hr : below p r.2.1.1) : w3_fpHashCert (D p) p (H p) :=
    ((finEquiv hp ⟨r.2.1.1,hr⟩,value r.2.1.2.1,mulEquiv _ r.2.1.2.2.1,mulEquiv _ r.2.1.2.2.2),r.2.2)
  have mask (b : Bool) (j : ℕ) : (p.testBit j && b) = (if b then p else 0).testBit j := by cases b <;> simp
  have NZ := w3_slotOr_spec false (value t.1.1).isLt
  constructor
  · rintro ⟨hx,o,hz,l,hr,hh⟩; have hn := (NZ.1 _ o).resolve_left (by decide)
    refine ⟨⟨hx,hn,hz,hr⟩,?_⟩
    change w3_slotOr _ ((zmodFin p) (finEquiv hp ⟨t.1,hx⟩)).val false _ ∧ w3_slotLt _ ((zmodFin p) (finEquiv hp ⟨r.1,hz⟩)).val _ _ ∧ w3_slotHashBits _ _ _ ((zmodFin p) (finEquiv hp ⟨t.1,hx⟩)).val ((zmodFin p) (finEquiv hp ⟨r.1,hz⟩)).val (cert hr) (auxEquiv _ w)
    rw [F _ hx,F _ hz]; refine ⟨o,l,?_⟩; apply Iff.mp _ hh
    apply block_spec <;> dsimp only <;> first | exact ha i | exact X | exact hb i | apply word_eval; exact fun j => hv (.vec i _) | exact funext (fun j => reg _) | skip
    case hp =>
      intro j; rw [← Ref.correct]; change (p.testBit j && _) = _; apply Eq.trans (congrArg (fun b => p.testBit j && b) (hv (.vec i Addr.bit.snd.snd.fst.snd.snd.snd))); exact mask _ _
    all_goals funext k; simp only [GateRoutes.word,padded,dif_pos (show k.val < G p from k.isLt)]; exact reg _
  · rintro ⟨⟨hx,hn,hz,hr⟩,h⟩
    change w3_slotOr _ ((zmodFin p) (finEquiv hp ⟨t.1,hx⟩)).val false _ ∧ w3_slotLt _ ((zmodFin p) (finEquiv hp ⟨r.1,hz⟩)).val _ _ ∧ w3_slotHashBits _ _ _ ((zmodFin p) (finEquiv hp ⟨t.1,hx⟩)).val ((zmodFin p) (finEquiv hp ⟨r.1,hz⟩)).val (cert hr) (auxEquiv _ w) at h
    rw [F _ hx,F _ hz] at h; refine ⟨hx,h.1,hz,h.2.1,hr,?_⟩; apply Iff.mpr _ h.2.2
    apply block_spec <;> dsimp only <;> first | exact ha i | exact X | exact hb i | apply word_eval; exact fun j => hv (.vec i _) | exact funext (fun j => reg _) | skip
    case hp =>
      intro j; rw [← Ref.correct]; change (p.testBit j && _) = _; apply Eq.trans (congrArg (fun b => p.testBit j && b) (hv (.vec i Addr.bit.snd.snd.fst.snd.snd.snd))); exact mask _ _
    all_goals funext k; simp only [GateRoutes.word,padded,dif_pos (show k.val < G p from k.isLt)]; exact reg _

private def split {α β γ : Type} {P : α → Prop} (e : Subtype P ≃ γ) (Q : γ → β → Prop) :
    {w : α × β // ∃ h : P w.1, Q (e ⟨w.1,h⟩) w.2} ≃ Σ c, {b // Q c b} :=
  (show _ ≃ Σ a : Subtype P, {b // Q (e a) b} from
    ⟨fun w => ⟨⟨_,w.prop.choose⟩,_,w.prop.choose_spec⟩,fun ⟨a,b⟩ => ⟨(a.val,b.val),a.prop,b.prop⟩,fun _ => rfl,fun _ => rfl⟩).trans (Equiv.sigmaCongrLeft (β:=fun c => {b // Q c b}) e)
private def packed (j : Fin 4) (T : ℕ) (η : List Bool) := Σ S : Mass p (n+1) η,
  Σ a : Fin (copies j) → Checked S.val T, Fin (outputs j) → Σ z : Fin p,
    (k : Fin (copies j)) → {r // chainOK (a k).val.1 z r}
private def emptyTail {α : Type} (F : α → Type) : (Σ a : α, Fin 0 → F a) ≃ α := Equiv.sigmaUnique _ _
private def finish (j : Fin 4) (T : ℕ) (η : List Bool) : packed (p:=p) (n:=n) j T η ≃ Transcript p n T η j := by
  apply Classical.choice; fin_cases j <;> apply Nonempty.intro
  · exact (Equiv.sigmaCongrRight fun _ => emptyTail _).trans (emptyTail _)
  · exact Equiv.sigmaCongrRight fun _ => (emptyTail _).trans (Equiv.funUnique (Fin 1) _)
  · exact Equiv.sigmaCongrRight fun _ => (emptyTail _).trans (finTwoArrowEquiv _)
  · refine Equiv.sigmaCongrRight fun S => (Equiv.sigmaCongrRight fun _ => Equiv.funUnique (Fin 1) _).trans ?_
    let F (ab : Checked S.val T × Checked S.val T) := Σ z : Fin p, {r // chainOK ab.1.val.1 z r} × {r // chainOK ab.2.val.1 z r}
    refine (Equiv.sigmaCongr (β₂:=F) (finTwoArrowEquiv _) (fun a => Equiv.sigmaCongrRight fun z => piFinTwoEquiv _)).trans ?_
    exact ⟨fun ⟨ab,z,r,s⟩ => ⟨(ab,z,r.val,s.val),r.prop,s.prop⟩,fun v => ⟨v.val.1,v.val.2.1,⟨_,v.prop.1⟩,⟨_,v.prop.2⟩⟩,fun _ => rfl,fun _ => rfl⟩

private theorem peel {P R : Prop} {Q : P → Prop} (h : ∀ a, R ↔ Q a) : P ∧ R ↔ ∃ a, Q a :=
  ⟨fun ⟨a,b⟩ => ⟨a,(h a).mp b⟩,fun ⟨a,b⟩ => ⟨a,(h a).mpr b⟩⟩

private def assemble (hn : 0 < n) (j : Fin 4) {T : ℕ} (hT : T ≤ p) (η : List Bool) (hη : η.length ≤ (n+1)*2*bitLen p) :
    {v : (Semantics.shape p (n+1) j).Data // (Routes.network (H p) p (n+1) j T η).OK
      (Fin.lastCases (motive:=fun _ => Bool) false ((Semantics.shape p (n+1) j).decode.symm v))} ≃ packed (p:=p) (n:=n) j T η := by
  let E := seedEquiv p (n+1) η hη
  let A (S : Mass p (n+1) η) : {v : Fin (copies j) → (atomBankShape (n+1) (D p) (G p)).Data // ∀ k, atomBankOK S.val T (v k)} ≃ (Fin (copies j) → Checked S.val T) := Equiv.subtypePiEquivPi.trans (Equiv.piCongrRight fun _ : Fin (copies j) => atomBankEquiv S.val hT)
  let Z : {w : Triple (D p) // below p w} ≃ Fin p := finEquiv (primeFitsAtom p).le
  let Q (S : Mass p (n+1) η) (a : Fin (copies j) → Checked S.val T) (z : Fin p) (c : Fin (copies j) → Slice p n) := ∀ k, chainValid (a k).val.1 z (c k)
  let O (S : Mass p (n+1) η) (a : Fin (copies j) → Checked S.val T) := fun t : (productShape j (n+1) (D p) (G p)).Data => ∃ h : below p t.1, Q S a (Z ⟨t.1,h⟩) t.2
  let B (S : Mass p (n+1) η) := fun w : ((Shape.vec (copies j) (atomBankShape (n+1) (D p) (G p))).pair (.vec (outputs j) (productShape j (n+1) (D p) (G p)))).Data =>
    ∃ h : ∀ k, atomBankOK S.val T (w.1 k), ∀ t, O S (A S ⟨w.1,h⟩) (w.2 t)
  refine (Equiv.subtypeEquivRight (q:=fun v : (Semantics.shape p (n+1) j).Data => ∃ h, B (E ⟨v.1,h⟩) v.2) ?_).trans ?_
  swap
  · refine (split E B).trans (Equiv.sigmaCongrRight fun S => ?_)
    refine (split (A S) (fun a (w : Fin (outputs j) → _) => ∀ t, O S a (w t))).trans (Equiv.sigmaCongrRight fun a => ?_)
    refine Equiv.subtypePiEquivPi.trans (Equiv.piCongrRight fun t => ?_)
    exact (split Z (Q S a)).trans (Equiv.sigmaCongrRight fun z => Equiv.subtypePiEquivPi.trans (Equiv.piCongrRight fun k => chainEquiv hn (a k).val.1 z))
  intro v; let s := Semantics.shape p (n+1) j; let u := Fin.lastCases (motive:=fun _ => Bool) false (s.decode.symm v)
  have raw : s.decode (u ∘ Fin.castSucc) = v := by simp [u,Function.comp_def,Fin.lastCases_castSucc]
  have readR (a : Addr s) : a.get (s.decode (u ∘ Fin.castSucc)) = a.get v := congrArg a.get raw
  have seed := seedOK_iff seeds u v.1 (fun a => readR (.fst a)) hη
  unfold Routes.network; simp only [joinB_iff,allRows_iff]; rw [seed]; apply peel; intro hs
  let S := E ⟨v.1,hs⟩; have W := seedEquiv_words seeds u v.1 (fun a => readR (.fst a)) hη hs
  have bankR (k) := atomRows S.val T (atoms k) u (v.2.1 k) (fun a => readR (.snd (.fst (.vec k a)))) coeffA coeffB (fun i => (W i).1) (fun i => (W i).2)
  rw [show (∀ k, _) ↔ (∀ k, atomBankOK S.val T (v.2.1 k)) from forall_congr' bankR]; apply peel; intro ha; apply forall_congr'; intro t
  have R (a) := readR (.snd (.snd (.vec t (.fst a))))
  rw [checker_iff p (Routes.result t) u (v.2.2 t).1 (fun a => ((Ref.reg _).correct u).symm.trans (R a))]; apply peel; intro hz
  apply forall_congr'; intro k; let b := (A S ⟨v.2.1,ha⟩ k).val.1
  have atomW (i) := atomBankEquiv_word_eval S.val hT ⟨v.2.1 k,ha k⟩ i (fun j => atoms k (.vec i (.fst (.fst j)))) u (fun l => readR _)
  let q := stages (m:=n+1) (d:=D p) (e:=G p) t k
  have input : evalWord (initial k) u (w3_fpResidue (b 0)).val := by rw [initial,dif_pos (Nat.succ_pos _)]; exact atomW 0
  have output := word_eval (fun j => Routes.result (m:=n+1) (d:=D p) (e:=G p) t (.fst j)) u (v.2.2 t).1.1 (fun i => R (.fst (.word i)))
  let ys := Routes.tail (m:=n+1) (d:=D p) (e:=G p) k
  have yval (i : Fin n) : evalWord (ys i) u (w3_fpResidue (b i.succ)).val := atomW i.succ
  have endRow := chainRows (s:=s) hn b (Z ⟨_,hz⟩) ((v.2.2 t).2 k) q u (fun a => readR (.snd (.snd (.vec t (.snd (.vec k a)))))) (initial k) ys (residueWord (Routes.result t)) input yval output
  exact endRow

/-- Satisfying assignments give precisely the transcripts of the selected moment query. -/
noncomputable def runs {p : ℕ} [Fact p.Prime] (j : Fin 4) {T : ℕ} (hT : T ≤ p)
    (η : List Bool) (hη : η.length ≤ blockCount (bitLen p) * 2 * bitLen p) :
    let m := blockCount (bitLen p)
    {x : Fin (Semantics.layout p m j T η).nb → Bool // ∀ g, Semantics.tests p m j T η g
      (fun e => x ((Semantics.layout p m j T η).bit e.val)) = true} ≃ Transcript p (m-1) T η j := by
  have hm : 2 ≤ blockCount (bitLen p) := le_max_left ..
  generalize he : blockCount (bitLen p) = m at *; cases m with
  | zero => omega
  | succ n => exact (Semantics.assignments ..).trans ((assemble (by omega) j hT η hη).trans (finish ..))
end
end DetDLP.S8G.ChainSliceEquiv


