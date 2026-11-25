-- Prove2me | Definitions.Def_DetDLP_S8O_ECMapTile
-- name    : DetDLP_S8O_ECMapTile
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T07:36:20.085282+00:00
-- url     : https://prove2.me/theorems/b2d0af99-68c4-4cee-9239-c7b3ab1beadf
-- title:
--   EC to short-Weierstrass tile layout and evaluator
-- statement:
--   ## EC-to-short-Weierstrass tile layout and evaluator\n\nThis development formalizes a bounded-width, columnar Boolean-circuit layout for an elliptic-curve conversion to short-Weierstrass form. Each column uses eight registers and reads two predecessor registers; the cyclic predecessor convention also handles the one-column boundary. The selector enforces consistent infinity flags and gates the converted coordinates to zero at infinity.\n\nThe local arithmetic atom combines the hash-gate layout with the addition circuit's less-than block. The composed layout and its specification connect selector constraints and arithmetic witnesses to the conversion checks. The evaluator represents gate programs as opcodes, local indices, port permutations, and external pin requirements; its polynomial-time property follows from the component evaluators and list operations.\n\nThe formal results establish layout correctness, uniformity, edge and degree bounds, and equivalence between the encoded circuit acceptance condition and the map checks. In particular, the selector's bitwise equations express \(I_{out}=I_{in}\) and, coordinatewise, \(x_{out}=\neg I_{in}\,X\), \(y_{out}=\neg I_{in}\,Y\), with Boolean multiplication interpreted as the stated conditional.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8O_ECAddLayout
import Definitions.Def_DetDLP_S8H_PointAddresses
import Definitions.Def_DetDLP_S8J_CircuitRealizes
import Definitions.Def_DetDLP_S8J_HashGatePoly

/-! S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4 & Section 3.1–3.2, Lemma 2.4 & Theorem 3.1 (pp. 9–13). -/
set_option autoImplicit false
namespace DetDLP.S8O.TileColumns
open S8J S8H.PointAddresses Groundwork

/-- Each column owns `k` registers and additionally reads the first `f` registers
of its predecessor. The boundary wraps, including in a one-column word. -/
def row {n k : ℕ} (e : Fin (n*k)) : Fin n := ⟨e.val/k, by have := e.isLt; exact Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using this)⟩
def idx {n k : ℕ} (i : Fin n) (j : Fin k) : Fin (n*k) := finProdFinEquiv (i,j)
@[simp] theorem idx_val {n k : ℕ} (i : Fin n) (j : Fin k) : (idx i j).val = k*i.val+j.val := Nat.add_comm ..
@[simp] theorem row_idx {n k : ℕ} (i : Fin n) (j : Fin k) : row (idx i j) = i := by
  apply Fin.ext; change (idx i j).val / k = i.val; rw [idx_val]; have hk : 0 < k := Nat.zero_lt_of_lt j.isLt
  rw [Nat.mul_add_div hk,Nat.div_eq_of_lt j.isLt,Nat.add_zero]
def prev {n : ℕ} (i : Fin n) := S8C.AddLayout.prev i
private theorem prev_inj {n : ℕ} : Function.Injective (@prev n) := by
  intro i j h; have he := congrArg Fin.val h; simp only [prev,S8C.AddLayout.prev] at he
  apply Fin.ext; split_ifs at he <;> omega

def dst (n k f e : ℕ) := let i := e/(k+f); let j := e%(k+f)
  if j < k then k*i+j else k*(if i=0 then n-1 else i-1)+(j-k)
def bit {n k f : ℕ} (hf : f ≤ k) (e : Fin (n*(k+f))) : Fin (n*k) :=
  let i := row e
  let j := e.val%(k+f)
  if h : j < k then idx i ⟨j,h⟩ else idx (prev i) ⟨j-k,by
    have he := e.isLt; have hp : 0 < k+f := Nat.pos_of_ne_zero (by intro hz; simp [hz] at he)
    have := Nat.mod_lt e.val hp; dsimp [j] at *; omega⟩
theorem bit_idx {n k f : ℕ} (hf : f ≤ k) (i : Fin n) (j : Fin (k+f)) :
    bit hf (idx i j) = if h : j.val < k then idx i ⟨j.val,h⟩ else idx (prev i) ⟨j.val-k,by omega⟩ := by
  have h : (idx i j).val % (k+f) = j.val := by simp [Nat.mul_add_mod,Nat.mod_eq_of_lt j.isLt]
  simp only [bit,h,row_idx]

def layout (n k f : ℕ) (hf : f ≤ k) : w3_FactorLayout where
  ng := n
  nb := n*k
  ne := n*(k+f)
  gate := row
  bit := bit hf
  rep b := let p := finProdFinEquiv.symm b; idx p.1 (Fin.castLE (Nat.le_add_right k f) p.2)
  rep_bit b := by
    obtain ⟨⟨i,j⟩,rfl⟩ := finProdFinEquiv.surjective b
    simp only [Equiv.symm_apply_apply,bit_idx,Fin.coe_castLE,dif_pos j.isLt]; rfl

def code (k f n : ℕ) : Code := ⟨n,n*k,n*(k+f), (·/(k+f)), dst n k f⟩
theorem models (n k f : ℕ) (hf : f ≤ k) : Models (code k f n) (layout n k f hf) := by
  refine ⟨rfl,rfl,rfl,fun _ => rfl,?_⟩; intro e
  change dst n k f e.val = (bit hf e).val
  by_cases h : e.val%(k+f) < k <;> simp [dst,bit,h,prev,S8C.AddLayout.prev,row]
attribute [local fun_prop] PolyT.mul PolyT.div PolyT.mod PolyT.const PolyT.id'
  P2M_Groundwork_PolyT_ite__226169acf219

theorem uniform (k f : ℕ) : Uniform (code k f) := by
  constructor <;> intros <;> simp only [code,dst] <;> fun_prop

def test {n k f : ℕ} (hf : f ≤ k) (check : (Fin (k+f) → Bool) → Bool) :
    w3_factorTest (layout n k f hf) := fun i x => check (fun j => x ⟨idx i j,row_idx i j⟩)

theorem test_iff {n k f : ℕ} (hf : f ≤ k) (check : (Fin (k+f) → Bool) → Bool) (x : Fin (n*k) → Bool) :
    Accept (layout n k f hf) (test hf check) x ↔ ∀ i, check (fun j => x (bit hf (idx i j))) = true := Iff.rfl

private theorem cardBound {m b s : ℕ} (g : Fin m → Fin b) (i : Fin b) (key : Fin m → Fin s)
    (hinj : ∀ a c, g a = i → g c = i → key a = key c → a = c) : degreeOf g i ≤ s := by
  let l := (List.finRange m).filter fun j => decide (g j = i)
  have hh := Fintype.card_le_of_injective (fun x : ↥l.toFinset => key x.val) (by
    intro x y h; apply Subtype.ext; exact hinj _ _ (by simpa [l] using x.2) (by simpa [l] using y.2) h)
  rwa [Fintype.card_coe,List.toFinset_card_of_nodup ((List.nodup_finRange _).filter _),Fintype.card_fin] at hh

theorem shape {n k f : ℕ} (hf : f ≤ k) {D : ℝ} (hd : (k+f : ℕ) < D) : Shape (layout n k f hf) D 2 := by
  constructor
  · intro i; apply lt_of_le_of_lt _ hd; apply Nat.cast_le.mpr
    apply cardBound row i (fun e => (finProdFinEquiv.symm e).2)
    rintro a c ha hc hk
    obtain ⟨⟨u,j⟩,rfl⟩ := finProdFinEquiv.surjective a
    obtain ⟨⟨v,l⟩,rfl⟩ := finProdFinEquiv.surjective c
    simp only [Equiv.symm_apply_apply] at hk
    change row (idx u j) = i at ha; change row (idx v l) = i at hc
    simp only [row_idx] at ha hc; subst u; subst v; subst l; rfl
  · intro b; apply cardBound (bit hf) b (fun e => if (finProdFinEquiv.symm e).2.val < k then 0 else 1)
    rintro a c ha hc hk
    obtain ⟨⟨u,j⟩,rfl⟩ := finProdFinEquiv.surjective a
    obtain ⟨⟨v,l⟩,rfl⟩ := finProdFinEquiv.surjective c
    have eq := ha.trans hc.symm
    change bit hf (idx u j) = bit hf (idx v l) at eq
    simp only [bit_idx,Equiv.symm_apply_apply] at eq hk
    split_ifs at eq hk <;> try contradiction
    all_goals
      have hp := finProdFinEquiv.injective eq
      have hu := congrArg Prod.fst hp; have hj := congrArg (fun x => x.2.val) hp
      apply congrArg finProdFinEquiv; apply Prod.ext
      · first | exact hu | exact prev_inj hu
      · apply Fin.ext; change j.val = l.val; dsimp at hj; omega

end DetDLP.S8O.TileColumns
namespace DetDLP.S8O.ECMapTile
open S8J S8H.PointAddresses TileColumns

/-- Per-column: input infinity, output infinity, x, y, converted X, Y, output x, y.
Ports 8 and 9 read the predecessor flags. -/
def select (a : Fin 10 → Bool) := decide (a 0 = a 8 ∧ a 1 = a 9 ∧ a 1 = a 0 ∧
  a 6 = (if a 0 then false else a 4) ∧ a 7 = (if a 0 then false else a 5))
def selectors (d : ℕ) := TileColumns.layout d 8 2 (by decide)
def selectorTest (d : ℕ) : w3_factorTest (selectors d) := TileColumns.test (by decide) select

def atom {d : ℕ} (hd : 1 ≤ d) := join (HashGateLayout.layout d hd) (CircuitRealizes.lessBlock d).A
def atomCode (d : ℕ) := sum (hash d) (add (d+1))
theorem atom_models {d : ℕ} (hd : 1 ≤ d) : Models (atomCode d) (atom hd) := sum_spec (hash_spec hd) (add_spec _)
theorem atom_uniform : Uniform atomCode := sum_poly hash_poly (add_poly _ (by intro α _ d hd; exact Groundwork.PolyT.add hd (Groundwork.PolyT.const 1)))
open S8H.ECPointArithmetic S8K.ECAddArithmetic
variable {p : ℕ} [Fact p.Prime]
noncomputable def atomTest (a x : ZMod p) (r : Run p) : w3_factorTest (atom (Nat.succ_pos (bitLen p))) :=
  joinTest (HashGateLayout.tests _ a.val x.val r.2) (S8C.AddLayout.test true)

def atomBits (b : ZMod p) (r : Run p) (w : ECAddLayout.GateAux p) : Fin (atom (Nat.succ_pos (bitLen p))).nb → Bool :=
  Fin.append (HashGateLayout.encode _ b.val r.1.val r.2 w.1)
    (HashGateLayout.addBits r.1.val w.2.1.val p w.2.2)

theorem atomBits_iff (a x b : ZMod p) (r : Run p) (w : ECAddLayout.GateAux p) :
    Accept _ (atomTest a x r) (atomBits b r w) ↔
      w3_slotHashBits (Nat.succ_pos _) a.val b.val x.val r.1.val r.2 w.1 ∧ w3_slotLt (width p) r.1.val p w.2 :=
  (HashGateLayout.joined ..).trans ((HashGateLayout.encode_iff ..).and (CircuitRealizes.lessBlock_iff ..))

def layout {d : ℕ} (hd : 1 ≤ d) := join (selectors d) (copies (atom hd) 3)
def code (d : ℕ) := sum (TileColumns.code 8 2 d) (copiesCode (atomCode d) 3)
theorem models {d : ℕ} (hd : 1 ≤ d) : Models (code d) (layout hd) :=
  sum_spec (TileColumns.models ..) (copies_spec (atom_models hd) _)
theorem uniform : Uniform code := sum_poly (TileColumns.uniform ..) (copies_poly atom_uniform _)
theorem edges {d : ℕ} (hd : 1 ≤ d) : (layout hd).ne < 25000*(d+3) := by
  change d*10 + (copies (atom hd) 3).ne < _; rw [copies_ne]
  change _ + 4*((HashGateLayout.layout d hd).ne + (d+1)*5) < _
  have := HashGateLayout.edges hd; omega

theorem cap_large (d : ℕ) : (27 : ℝ) < HashGateLayout.degreeCap d := by
  have h := Real.one_le_rpow (by linarith [Nat.cast_nonneg (α := ℝ) d] : 1 ≤ (d:ℝ)+1) (by norm_num : (0:ℝ) ≤ 3/4)
  apply lt_of_lt_of_le _ (le_max_right ..); linarith

theorem atom_shape {d : ℕ} (hd : 1 ≤ d) : Shape (atom hd) (HashGateLayout.degreeCap d) 2 := by
  apply join_shape (HashGateLayout.shape hd)
  constructor
  · intro g; have h := (w3_gateDegree (S8C.AddLayout.layout (d+1)) g).symm.le.trans (S8C.AddLayout.gateDegree g)
    exact (Nat.cast_le.mpr h).trans_lt ((by norm_num : (5:ℝ) < 27).trans (cap_large d))
  · intro b; exact (w3_bitDegree _ _).symm.le.trans (S8C.AddLayout.bitDegree b)
theorem shape {d : ℕ} (hd : 1 ≤ d) : Shape (layout hd) (HashGateLayout.degreeCap d) 2 :=
  join_shape (TileColumns.shape (by decide) ((by norm_num : ((8+2 : ℕ):ℝ) < 27).trans (cap_large d)))
    (copies_shape (atom_shape hd) _)

def reg {d : ℕ} (hd : 1 ≤ d) (i : Fin d) (j : Fin 8) : Fin (layout hd).nb := Fin.castAdd _ (idx i j)
def inInf {d : ℕ} (hd : 1 ≤ d) := reg hd ⟨0,hd⟩ 0
def outInf {d : ℕ} (hd : 1 ≤ d) := reg hd ⟨0,hd⟩ 1
def inX {d : ℕ} (hd : 1 ≤ d) (i : Fin d) := reg hd i 2
def inY {d : ℕ} (hd : 1 ≤ d) (i : Fin d) := reg hd i 3
def outX {d : ℕ} (hd : 1 ≤ d) (i : Fin d) := reg hd i 6
def outY {d : ℕ} (hd : 1 ≤ d) (i : Fin d) := reg hd i 7

noncomputable def tests (E : WeierstrassCurve (ZMod p)) (P : Coords p) (c : MapCert p) :
    w3_factorTest (layout (Nat.succ_pos (bitLen p))) :=
  let (X,t,u,Y,_) := c
  joinTest (selectorTest _) (joinTest (atomTest 36 P.2.1 X) (joinTest (atomTest E.a₁ P.2.1 t)
    (joinTest (atomTest 2 P.2.2 u) (atomTest 108 u.1 Y))))

def selBits (P out : Coords p) (X Y : ZMod p) : Fin (width p * 8) → Bool := fun b =>
  let (i,j) := finProdFinEquiv.symm b
  ![P.1,out.1,P.2.1.val.testBit i,P.2.2.val.testBit i,X.val.testBit i,Y.val.testBit i,
    out.2.1.val.testBit i,out.2.2.val.testBit i] j

theorem selBits_iff (P out : Coords p) (X Y : ZMod p) :
    Accept (selectors (width p)) (selectorTest _) (selBits P out X Y) ↔
      out.1 = P.1 ∧ (∀ i : Fin (width p), out.2.1.val.testBit i = (if P.1 then false else X.val.testBit i)) ∧
      (∀ i : Fin (width p), out.2.2.val.testBit i = (if P.1 then false else Y.val.testBit i)) := by
  change (∀ i : Fin (width p), select (fun j => selBits P out X Y (bit (by decide : 2 ≤ 8) (idx i j))) = true) ↔ _
  simp only [select,decide_eq_true_eq,bit_idx]
  norm_num [selBits,idx,forall_and]

abbrev Aux (p : ℕ) := (ECAddLayout.GateAux p × ECAddLayout.GateAux p × ECAddLayout.GateAux p × ECAddLayout.GateAux p × Unit) × Unit

def encode (E : WeierstrassCurve (ZMod p)) (P out : Coords p) (c : MapCert p) (w : Aux p) :
    Fin (layout (Nat.succ_pos (bitLen p))).nb → Bool :=
  let (X,t,u,Y,_) := c; let ((a,b,f,g,_),_) := w
  Fin.append (selBits P out X.1 Y.1) (Fin.append (atomBits (3*E.b₂) X a)
    (Fin.append (atomBits E.a₃ t b) (Fin.append (atomBits t.1 u f) (atomBits 0 Y g))))

set_option maxHeartbeats 2400000 in
theorem encode_iff (E : WeierstrassCurve (ZMod p)) (P out : Coords p) (c : MapCert p) (w : Aux p) :
    Accept _ (tests E P c) (encode E P out c w) ↔ (ECAddLayout.mapChecks E P out c).bits w := by
  rcases P with ⟨i,x,y⟩; rcases c with ⟨X,t,u,Y,_⟩; rcases w with ⟨⟨a,b,f,g,_⟩,_⟩
  let h₁ := atomBits_iff 36 x (3*E.b₂) X a
  let h₂ := atomBits_iff E.a₁ x E.a₃ t b
  let h₃ := atomBits_iff 2 y t.1 u f
  let h₄ := atomBits_iff 108 u.1 0 Y g
  let h₅ := selBits_iff (i,x,y) out X.1 Y.1
  have cd := (HashGateLayout.joined ..).trans (h₃.and h₄)
  have bcd := (HashGateLayout.joined ..).trans (h₂.and cd)
  have abcd := (HashGateLayout.joined ..).trans (h₁.and bcd)
  have all := (HashGateLayout.joined ..).trans (h₅.and abcd)
  refine all.trans ?_
  cases i <;> constructor
  · rintro ⟨h,A,B,C,D⟩; exact ⟨⟨A,B,C,D,trivial⟩,h⟩
  · rintro ⟨⟨A,B,C,D,_⟩,h⟩; exact ⟨h,A,B,C,D⟩
  · rintro ⟨⟨hi,hx,hy⟩,A,B,C,D⟩
    refine ⟨⟨A,B,C,D,trivial⟩,hi,fun j => ?_,fun j => ?_⟩
    · change out.2.1.val.testBit j = (0 : ZMod p).val.testBit j; simpa using hx j
    · change out.2.2.val.testBit j = (0 : ZMod p).val.testBit j; simpa using hy j
  · rintro ⟨⟨A,B,C,D,_⟩,hi,hx,hy⟩
    refine ⟨⟨hi,fun j => ?_,fun j => ?_⟩,A,B,C,D⟩
    · have h : out.2.1.val.testBit j = (0 : ZMod p).val.testBit j := hx j; simpa using h
    · have h : out.2.2.val.testBit j = (0 : ZMod p).val.testBit j := hy j; simpa using h

open Groundwork
/-- Local gate query in ascending incidence order, rejecting malformed port words. -/
def selectorEval (a : List Bool) := decide (a.length = 10) && select (fun j => a[j.val]?.getD false)
theorem selectorEval_eq (a : Fin 10 → Bool) : selectorEval (List.ofFn a) = select a := by
  simp [selectorEval,select]
attribute [local fun_prop] PolyT.const PolyT.comp PolyT.id' PolyT.length PolyT.fst PolyT.snd PolyT.prodMk P2M_Groundwork_PolyT_ite__226169acf219
theorem selectorEval_poly {α : Type} [Enc α] {a : α → List Bool} (ha : PolyT a) :
    PolyT fun x => selectorEval (a x) := by unfold selectorEval select; fun_prop

end DetDLP.S8O.ECMapTile

namespace DetDLP.S8O.TileEval
open Groundwork S8J
/-- A local program contains an opcode, the primitive's local index, a port
permutation, and the external M5 pin requirements (in physical port order). -/
abbrev Plan := ℕ × ℕ × List ℕ × List (ℕ × Bool)
def reorder (a : List Bool) (l : List ℕ) := l.map fun i => a[i]?.getD false
def pins (a : List Bool) (l : List (ℕ × Bool)) := l.all fun p => (a[p.1]?.getD false) == p.2

def column (n g : ℕ) (cin : Bool) (a : List Bool) :=
  let get (j : ℕ) := a[j]?.getD false
  let carry := if g=0 then cin else get 4
  decide (a.length = 5 ∧ (get 0).toNat + (get 1).toNat + carry.toNat = (get 2).toNat + 2*(get 3).toNat ∧
    (g+1 = n → get 3 = false))
theorem column_eq {n : ℕ} (g : Fin n) (cin : Bool) (x : {e // (S8C.AddLayout.layout n).gate e = g} → Bool) :
    column n g.val cin (List.ofFn fun j : Fin 5 => x ⟨S8C.AddLayout.pos g j,S8C.AddLayout.col_pos g j⟩) =
      S8C.AddLayout.test cin g x := by simp [column,S8C.AddLayout.test]

/-- Opcodes: multiplier, product adder, residue adder, range adder, selector. -/
def run (selector : ℕ → List Bool → Bool) (d : ℕ) (p : Plan) (a : List Bool) :=
  let w := reorder a p.2.2.1; let g := p.2.1
  pins a p.2.2.2 && (if p.1 = 0 then HashGatePoly.mulLayoutCheck d g w else
    if p.1 = 1 then column (2*d) g false w else if p.1 = 2 then column (d+1) g false w else
    if p.1 = 3 then column (d+1) g true w else selector g w)

attribute [local fun_prop] PolyT.const PolyT.comp PolyT.id' PolyT.fst PolyT.snd PolyT.prodMk PolyT.mul PolyT.length
  P2M_Groundwork_PolyT_ite__226169acf219 P2M_Groundwork_PolyT_id__1c5d0f44cc8f

theorem reorder_poly {α : Type} [Enc α] {a : α → List Bool} {l : α → List ℕ} (ha : PolyT a) (hl : PolyT l) :
    PolyT fun x => reorder (a x) (l x) := by
  apply PolyT.map (f := fun x i => (a x)[i]?.getD false) _ hl
  have hh : PolyT fun z : α × ℕ => a z.1 := PolyT.comp ha (by fun_prop); fun_prop

theorem pins_poly {α : Type} [Enc α] {a : α → List Bool} {l : α → List (ℕ × Bool)} (ha : PolyT a) (hl : PolyT l) :
    PolyT fun x => pins (a x) (l x) := by
  apply PolyT.all (f := fun x (i : ℕ × Bool) => ((a x)[i.1]?.getD false) == i.2) _ hl
  have hh : PolyT fun z : α × (ℕ × Bool) => a z.1 := PolyT.comp ha (by fun_prop); fun_prop

theorem column_poly {α : Type} [Enc α] {n g : α → ℕ} {a : α → List Bool} {b : α → Bool}
    (hn : PolyT n) (hg : PolyT g) (hb : PolyT b) (ha : PolyT a) : PolyT fun x => column (n x) (g x) (b x) (a x) := by
  unfold column; simp only [imp_iff_not_or]; fun_prop

attribute [local fun_prop] column_poly

theorem run_poly {α : Type} [Enc α] {d : α → ℕ} {p : α → Plan} {a : α → List Bool} {s : ℕ → List Bool → Bool}
    (hu : Unary d) (hd : PolyT d) (hp : PolyT p) (ha : PolyT a)
    (hs : ∀ {g : α → ℕ} {v : α → List Bool}, PolyT g → PolyT v → PolyT fun x => s (g x) (v x)) :
    PolyT fun x => run s (d x) (p x) (a x) := by
  have hw := reorder_poly ha (l := fun x => (p x).2.2.1) (by fun_prop)
  have hg : PolyT fun x => (p x).2.1 := by fun_prop
  have hb := pins_poly ha (l := fun x => (p x).2.2.2) (by fun_prop)
  unfold run; dsimp only
  have hm := HashGatePoly.mulLayoutCheck_poly hu hg hw
  apply PolyT.and' hb
  apply PolyT.ite' (c := fun x => (p x).1 = 0) (by fun_prop) hm
  apply PolyT.ite' (c := fun x => (p x).1 = 1) (by fun_prop) (column_poly (by fun_prop) hg (PolyT.const false) hw)
  apply PolyT.ite' (c := fun x => (p x).1 = 2) (by fun_prop) (column_poly (by fun_prop) hg (PolyT.const false) hw)
  exact PolyT.ite' (c := fun x => (p x).1 = 3) (by fun_prop) (column_poly (by fun_prop) hg (PolyT.const true) hw) (hs hg hw)

/-- Gate tables are concatenated in exactly the same order as `join`. -/
def columns (opcode n k : ℕ) : List Plan := (List.range n).map fun i => (opcode,i,List.range k,[])

def mulPlans {d : ℕ} (hd : 1 ≤ d) (x y z : ℕ) : List Plan := List.ofFn fun g : Fin (w3_fpMulLayout d hd).ng =>
  let G := w3_forgetSides (w4_M5GraphBounds.graph d hd)
  let A := w3_fpMulLayout d hd
  let V := Fin.castAdd A.nb g
  let order := List.ofFn fun j : Fin (G.deg g) =>
    let e := w3_m5LocalInc G g j
    ((w3_factorGraph A).portIndex V e.val (w3_gateInc A g e.val e.2)).val
  let pp := (List.finRange (4*d)).filterMap fun i =>
    let e : Fin G.nE := w4_M5PortTensor.ext hd i
    if h : e ∈ G.ports g then some (order[G.portIndex g e h |>.val]?.getD 0, w3_mulBus d x y z i) else none
  (0,g.val,order,pp)

open S8H.ECPointArithmetic S8K.ECAddArithmetic
variable {p : ℕ} [Fact p.Prime]
def atomPlans (a x : ZMod p) (r : Run p) :=
  let d := width p; let m := r.2.1.2
  mulPlans (d := d) (Nat.succ_pos (bitLen p)) a.val x.val m.2.1.1.val ++ mulPlans (Nat.succ_pos (bitLen p)) m.1.val p m.2.2.1.val ++
    columns 1 (2*d) 5 ++ columns 2 (d+1) 5 ++ columns 2 (d+1) 5 ++ columns 3 (d+1) 5

def gateEval (selector : ℕ → List Bool → Bool) (d : ℕ) (plans : List Plan) (g : ℕ) (a : List Bool) :=
  if g < plans.length then run selector d (plans[g]?.getD (0,0,[],[])) a else false

theorem gateEval_poly {α : Type} [Enc α] {d g : α → ℕ} {t : α → List Plan} {a : α → List Bool}
    {s : ℕ → List Bool → Bool} (hu : Unary d) (hd : PolyT d) (ht : PolyT t) (hg : PolyT g) (ha : PolyT a)
    (hs : ∀ {g : α → ℕ} {v : α → List Bool}, PolyT g → PolyT v → PolyT fun x => s (g x) (v x)) :
    PolyT fun x => gateEval s (d x) (t x) (g x) (a x) := by
  apply PolyT.ite' (c := fun x => g x < (t x).length) (by fun_prop) _ (PolyT.const false)
  exact run_poly hu hd (p := fun x => (t x)[g x]?.getD (0,0,[],[])) (by fun_prop) ha hs
end DetDLP.S8O.TileEval

namespace DetDLP.S8O.ECMapTile
open S8H.ECPointArithmetic S8K.ECAddArithmetic Groundwork TileEval
variable {p : ℕ} [Fact p.Prime]
def plans (E : WeierstrassCurve (ZMod p)) (P : Coords p) (c : MapCert p) :=
  let (X,t,u,Y,_) := c
  columns 4 (width p) 10 ++ atomPlans 36 P.2.1 X ++ atomPlans E.a₁ P.2.1 t ++ atomPlans 2 P.2.2 u ++ atomPlans 108 u.1 Y

def eval (E : WeierstrassCurve (ZMod p)) (P : Coords p) (c : MapCert p) : ℕ → List Bool → Bool :=
  gateEval (fun _ => selectorEval) (width p) (plans E P c)

theorem eval_poly (E : WeierstrassCurve (ZMod p)) (P : Coords p) (c : MapCert p)
    {α : Type} [Enc α] {g : α → ℕ} {a : α → List Bool} (hg : PolyT g) (ha : PolyT a) :
    PolyT fun x => eval E P c (g x) (a x) :=
  gateEval_poly (PolyT.const _) (PolyT.const _) (PolyT.const _) hg ha (fun _ hv => selectorEval_poly hv)
end DetDLP.S8O.ECMapTile


