-- Prove2me | Definitions.Def_DetDLP_S8H_ECPointArithmetic
-- name    : DetDLP_S8H_ECPointArithmetic
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T04:52:25.027918+00:00
-- url     : https://prove2.me/theorems/87f83b54-d73b-4a48-8f37-93951f989fce
-- title:
--   Deterministic EC-point arithmetic transcripts
-- statement:
--   Seven canonical modular multiply-add transcripts determine the Weierstrass equation and the parity-selected affine hash value, with unique witnesses.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4 & Section 3.1–3.2, Lemma 2.4 & Theorem 3.1 (pp. 9–13)

import Definitions.Def_DetDLP_W3_FpHashPins
import Definitions.Def_DetDLP_S8H_ECPointGadget

set_option autoImplicit false
namespace DetDLP.S8H.ECPointArithmetic

variable {p : ℕ} [Fact p.Prime]

abbrev width (p : ℕ) := bitLen p + 1
abbrev Cert (p : ℕ) := w3_fpHashCert (width p) p (Nat.succ_pos _)

theorem fits (p : ℕ) : p < 2 ^ width p :=
  (Nat.le_pow_clog (by decide : 1 < 2) p).trans_lt
    (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))

/-- A single multiply-and-add on canonical residues, retaining both M5 transcripts. -/
def gate (a x b z : ZMod p) (c : Cert p) :=
  w3_fpHashCheck (Nat.succ_pos (bitLen p)) a.val b.val x.val z.val c

private def fin (x : ZMod p) : Fin p := ⟨x.val,x.val_lt⟩

private theorem val_madd (a x b : ZMod p) : (a*x+b).val = (a.val*x.val+b.val)%p := by
  rw [← ZMod.val_natCast, Nat.cast_add, Nat.cast_mul]; simp

theorem gate_sound (mul : w3_modMulInterface) {a x b z : ZMod p} {c : Cert p}
    (h : gate a x b z c) : z = a*x+b := by
  apply ZMod.val_injective p
  rw [val_madd]
  exact w3_fpHash_sound _ (Fact.out : p.Prime).two_le (fits p) mul (fin a) (fin b) (fin x) (fin z) c h

theorem gate_unique (mul : w3_modMulInterface) (a x b : ZMod p) : ∃! c, gate a x b (a*x+b) c :=
  w3_fpHash_unique _ (Fact.out : p.Prime).two_le (fits p) mul (fin a) (fin b) (fin x) (fin (a*x+b)) (val_madd ..)

abbrev Args (p : ℕ) := ZMod p × ZMod p × ZMod p
abbrev Run (p : ℕ) := ZMod p × Cert p

def applyArgs (v : Args p) := v.1*v.2.1+v.2.2

def validRun (v : Args p) (r : Run p) := gate v.1 v.2.1 v.2.2 r.1 r.2

theorem run_unique (mul : w3_modMulInterface) (v : Args p) : ∃! r, validRun v r := by
  obtain ⟨c,hc,uc⟩ := gate_unique mul v.1 v.2.1 v.2.2
  refine ⟨(applyArgs v,c),hc,?_⟩
  rintro ⟨z,t⟩ ht
  obtain rfl : z = applyArgs v := gate_sound mul ht
  exact Prod.ext rfl (uc t ht)

/-- Seven multiply-add gates. Gate outputs 2 and 5 are the two sides of
    the curve equation; output 6 is the parity-selected affine hash. -/
def args (E : WeierstrassCurve (ZMod p)) (x y α β : ZMod p)
    (v : Fin 7 → ZMod p) : Fin 7 → Args p :=
  ![(E.a₁,x,y), (1,v 0,E.a₃), (v 1,y,0), (1,x,E.a₂),
    (v 3,x,E.a₄), (v 4,x,E.a₆), (α,x,β)]

def outputs (E : WeierstrassCurve (ZMod p)) (x y α β : ZMod p) : Fin 7 → ZMod p :=
  let t := E.a₁*x+y
  let l := t+E.a₃
  let r := x+E.a₂
  let m := r*x+E.a₄
  ![t,l,l*y,r,m,m*x+E.a₆,α*x+β]

theorem outputs_fixed (E : WeierstrassCurve (ZMod p)) (x y α β : ZMod p) (i : Fin 7) :
    outputs E x y α β i = applyArgs (args E x y α β (outputs E x y α β) i) := by
  fin_cases i <;> simp [args,outputs,applyArgs]

/-- Determinacy does not require the point to pass the final equality test. -/
theorem only_outputs (E : WeierstrassCurve (ZMod p)) (x y α β : ZMod p) (v : Fin 7 → ZMod p)
    (h : ∀ i, v i = applyArgs (args E x y α β v i)) : v = outputs E x y α β := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  have h4 := h 4; have h5 := h 5; have h6 := h 6
  simp [args,applyArgs] at h0 h1 h2 h3 h4 h5 h6
  funext i; fin_cases i <;> simp [outputs,h0,h1,h2,h3,h4,h5,h6]

def runsOK (E : WeierstrassCurve (ZMod p)) (x y α β : ZMod p) (r : Fin 7 → Run p) :=
  ∀ i, validRun (args E x y α β (fun j => (r j).1) i) (r i)

theorem runs_unique (mul : w3_modMulInterface) (E : WeierstrassCurve (ZMod p)) (x y α β : ZMod p) :
    ∃! r, runsOK E x y α β r := by
  classical
  let o := outputs E x y α β
  let a := args E x y α β o
  have ex (i : Fin 7) : ∃! c, gate (a i).1 (a i).2.1 (a i).2.2 (o i) c := by
    have hf : o i = applyArgs (a i) := outputs_fixed E x y α β i
    rw [hf]; exact gate_unique mul _ _ _
  choose c hc using fun i => (ex i).exists
  refine ⟨fun i => (o i,c i),hc,?_⟩
  intro r hr
  have hv : (fun j => (r j).1) = o := only_outputs E x y α β _ (fun i => gate_sound mul (hr i))
  funext i
  apply (run_unique mul (a i)).unique (y₁ := r i) (y₂ := (o i,c i)) ?_ ?_
  · have hs := hr i
    unfold validRun at hs
    rw [show (fun j => (r j).1) = o from hv] at hs
    exact hs
  · change gate (a i).1 (a i).2.1 (a i).2.2 (o i) (c i)
    exact hc i

theorem curve_iff (E : WeierstrassCurve (ZMod p)) (x y α β : ZMod p) :
    outputs E x y α β 2 = outputs E x y α β 5 ↔ E.toAffine.Equation x y := by
  rw [E.toAffine.equation_iff]
  simp [outputs]; constructor <;> intro h <;> linear_combination h

@[simp] theorem hash_value (E : WeierstrassCurve (ZMod p)) (x y α β : ZMod p) :
    (outputs E x y α β 6).val = (α.val*x.val+β.val)%p := val_madd ..

def coords {E : WeierstrassCurve (ZMod p)} : E.toAffine.Point → Bool × ZMod p × ZMod p
  | .zero => (true,0,0)
  | .some x y _ => (false,x,y)

def alpha {m : ℕ} (S : ECSeed p m) (i : Fin m) (y : ZMod p) : ZMod p :=
  ((S i (decide (y.val%2 = 1))).1.val+1 : ℕ)

def beta {m : ℕ} (S : ECSeed p m) (i : Fin m) (y : ZMod p) : ZMod p :=
  (S i (decide (y.val%2 = 1))).2.val

theorem outputs_mem {E : WeierstrassCurve (ZMod p)} {m : ℕ} (S : ECSeed p m) (i : Fin m)
    (T : ℕ) (P : E.toAffine.Point) :
    (let c := coords P
     c.1 = false ∧ (outputs E c.2.1 c.2.2 (alpha S i c.2.2) (beta S i c.2.2) 6).val < T) ↔
    ecFactorMem T S i P = true := by
  cases P with
  | zero => simp [coords,ecFactorMem]
  | some x y h =>
    have ha : (S i (decide (y.val%2 = 1))).1.val+1 < p := by
      have := (S i (decide (y.val%2 = 1))).1.isLt; omega
    have hb := (S i (decide (y.val%2 = 1))).2.isLt
    have ea : (alpha S i y).val = (S i (decide (y.val%2 = 1))).1.val+1 := ZMod.val_natCast_of_lt ha
    have eb : (beta S i y).val = (S i (decide (y.val%2 = 1))).2.val := ZMod.val_natCast_of_lt hb
    change (false = false ∧ (outputs E x y (alpha S i y) (beta S i y) 6).val < T) ↔ _
    rw [hash_value, ea, eb]
    simp [ecFactorMem]

/-- Tag 4 has exactly one arithmetic witness for each point passing the affine hash
    and prefix tests, and no witness for a rejected point. -/
def elemRuns {E : WeierstrassCurve (ZMod p)} {m : ℕ} (S : ECSeed p m) (i : Fin m)
    (b T : ℕ) (η : List Bool) (P : E.toAffine.Point) (r : Fin 7 → Run p) : Prop :=
  let c := coords P
  runsOK E c.2.1 c.2.2 (alpha S i c.2.2) (beta S i c.2.2) r ∧
    c.1 = false ∧ (r 2).1 = (r 5).1 ∧ (r 6).1.val < T ∧ (M89S1.ecWord b P).take η.length = η

theorem elemRuns_iff (mul : w3_modMulInterface) {E : WeierstrassCurve (ZMod p)}
    {m : ℕ} (S : ECSeed p m) (i : Fin m) (b T : ℕ) (η : List Bool) (P : E.toAffine.Point) :
    (∃! r, elemRuns S i b T η P r) ↔ ECPointGadget.elemPin b T S i η P = true := by
  let c := coords P
  let v := outputs E c.2.1 c.2.2 (alpha S i c.2.2) (beta S i c.2.2)
  have eqs (r : Fin 7 → Run p) (hr : runsOK E c.2.1 c.2.2 (alpha S i c.2.2) (beta S i c.2.2) r) :
      ∀ j, (r j).1 = v j := fun j => congrFun (only_outputs _ _ _ _ _ _ (fun k => gate_sound mul (hr k))) j
  have hcurve (hn : c.1 = false) : v 2 = v 5 := by
    apply (curve_iff ..).mpr
    cases P with
    | zero => contradiction
    | some _ _ h => exact h.1
  simp only [ECPointGadget.elemPin,Bool.and_eq_true,decide_eq_true_eq]
  rw [← outputs_mem S i T P]
  change _ ↔ (c.1 = false ∧ (v 6).val < T) ∧ _
  constructor
  · rintro ⟨r,⟨hr,hn,_,ht,hpre⟩,_⟩
    exact ⟨⟨hn,eqs r hr 6 ▸ ht⟩,hpre⟩
  · rintro ⟨⟨hn,ht⟩,hpre⟩
    obtain ⟨r,hr,ur⟩ := runs_unique mul E c.2.1 c.2.2 (alpha S i c.2.2) (beta S i c.2.2)
    exact ⟨r,⟨hr,hn,(eqs r hr 2).trans ((hcurve hn).trans (eqs r hr 5).symm),eqs r hr 6 ▸ ht,hpre⟩,
      fun s hs => ur s hs.1⟩

end DetDLP.S8H.ECPointArithmetic


