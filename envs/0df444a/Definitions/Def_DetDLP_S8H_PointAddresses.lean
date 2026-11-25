-- Prove2me | Definitions.Def_DetDLP_S8H_PointAddresses
-- name    : DetDLP_S8H_PointAddresses
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T05:50:39.586354+00:00
-- url     : https://prove2.me/theorems/737028f2-4402-44ab-bffd-aabb56902693
-- title:
--   Polynomial-time addresses for the seven elliptic curve arithmetic blocks
-- statement:
--   A numeric descriptor records the number of gates, bits, and incidences and their two owner maps. The M5 multiplier and column-addition descriptors agree with the formal factor layouts at every valid incidence. Disjoint sum and fixed replication preserve these properties and polynomial-time computability. Seven affine hash blocks have fewer than 35000(d+2) incidences and inherit the one-block degree bounds. These are the independent arithmetic blocks before adding shared buses and public query pins.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4 & Section 3.1–3.2, Lemma 2.4 & Theorem 3.1 (pp. 9–13)

import Definitions.Def_DetDLP_S8J_HashGateLayout
import Definitions.Def_DetDLP_W4_M5EdgeNat

set_option autoImplicit false
namespace DetDLP.S8H.PointAddresses
open S8J w4_M5GraphBounds w4_MulParams w4_M5Evaluator Groundwork
attribute [-simp] Fin.natAdd_eq_addNat

/-- All addresses are total functions of natural numbers, including out-of-range queries. -/
structure Code where
  ng : ℕ
  nb : ℕ
  ne : ℕ
  gate : ℕ → ℕ
  bit : ℕ → ℕ

structure Models (c : Code) (A : w3_FactorLayout) : Prop where
  ng : c.ng = A.ng
  nb : c.nb = A.nb
  ne : c.ne = A.ne
  gate : ∀ e : Fin A.ne, c.gate e.val = (A.gate e).val
  bit : ∀ e : Fin A.ne, c.bit e.val = (A.bit e).val

def sum (a b : Code) : Code := ⟨a.ng+b.ng,a.nb+b.nb,a.ne+b.ne,
  fun e => if e < a.ne then a.gate e else a.ng+b.gate (e-a.ne),
  fun e => if e < a.ne then a.bit e else a.nb+b.bit (e-a.ne)⟩

theorem sum_spec {a b : Code} {A B : w3_FactorLayout} (h : Models a A) (k : Models b B) :
    Models (sum a b) (join A B) := by
  refine ⟨congrArg₂ (·+·) h.ng k.ng,congrArg₂ (·+·) h.nb k.nb,congrArg₂ (·+·) h.ne k.ne,?_,?_⟩
  all_goals intro e; induction e using Fin.addCases with
    | left i => simp [sum,join,splitMap,h.ne,i.isLt,h.gate,h.bit]
    | right i => simp [sum,join,splitMap,h.ne,h.ng,h.nb,k.gate,k.bit]

def add (n : ℕ) : Code := ⟨n,n*4,n*5,(·/5),fun e =>
  if e%5 < 4 then 4*(e/5)+e%5 else 4*(if e/5=0 then n-1 else e/5-1)+3⟩

theorem add_spec (n : ℕ) : Models (add n) (S8C.AddLayout.layout n) := by
  refine ⟨rfl,rfl,rfl,fun _ => rfl,?_⟩
  intro e
  by_cases h : e.val%5 < 4 <;> simp [add,S8C.AddLayout.layout,S8C.AddLayout.bit,h,S8C.AddLayout.reg,S8C.AddLayout.prev,S8C.AddLayout.col]

def wires (d : ℕ) := 4*d+(6*(L1 d*L2 d)+8*n0 d-2)*(J d+1)
theorem wires_eq {d : ℕ} (hd : 1 ≤ d) : wires d = (graph d hd).nE := by rw [graph_nE hd,wires,L1_mul_L2]

def mul (d : ℕ) : Code := ⟨vertexCount d,wires d,wires d+wires d,
  fun e => if e < wires d then w4_M5EdgeNat.srcNat d e else w4_M5EdgeNat.dstNat d (e-wires d),
  fun e => if e < wires d then e else e-wires d⟩

theorem mul_spec {d : ℕ} (hd : 1 ≤ d) : Models (mul d) (w3_fpMulLayout d hd) := by
  have hw := wires_eq hd
  refine ⟨rfl,hw,congrArg₂ (·+·) hw hw,?_,?_⟩
  · change ∀ e : Fin ((graph d hd).nE+(graph d hd).nE), (mul d).gate e.val = (Fin.addCases (motive := fun _ => Fin (graph d hd).nV) (fun i => ((graph d hd).endpoints i).1) (fun i => ((graph d hd).endpoints i).2) e).val
    intro e; induction e using Fin.addCases with
    | left i =>
      simp only [mul,Fin.val_castAdd,Fin.addCases_left,hw,if_pos i.isLt]
      exact congrArg Prod.fst (w4_M5EdgeNat.endpointsNat_eq hd i)
    | right i =>
      simp [mul,hw]
      exact congrArg Prod.snd (w4_M5EdgeNat.endpointsNat_eq hd i)
  · change ∀ e : Fin ((graph d hd).nE+(graph d hd).nE), (mul d).bit e.val = (Fin.addCases (motive := fun _ => Fin (graph d hd).nE) id id e).val
    intro e; induction e using Fin.addCases with
    | left i => simp [mul,hw,i.isLt]
    | right i => simp [mul,hw]

def hash (d : ℕ) := sum (sum (mul d) (mul d)) (sum (add (2*d)) (sum (add (d+1)) (add (d+1))))

theorem hash_spec {d : ℕ} (hd : 1 ≤ d) : Models (hash d) (HashGateLayout.layout d hd) :=
  sum_spec (sum_spec (mul_spec hd) (mul_spec hd)) (sum_spec (add_spec _) (sum_spec (add_spec _) (add_spec _)))

attribute [local fun_prop] PolyT.mul PolyT.div PolyT.mod PolyT.const PolyT.comp PolyT.id'
  P2M_Groundwork_PolyT_ite__226169acf219 L1_poly L2_poly J_poly n0_poly vertexCount_poly
  w4_M5EdgeNat.srcNat_poly w4_M5EdgeNat.dstNat_poly

structure Uniform (c : ℕ → Code) : Prop where
  ng : ∀ {α : Type} [Enc α] {d : α → ℕ}, PolyT d → PolyT fun x => (c (d x)).ng
  nb : ∀ {α : Type} [Enc α] {d : α → ℕ}, PolyT d → PolyT fun x => (c (d x)).nb
  ne : ∀ {α : Type} [Enc α] {d : α → ℕ}, PolyT d → PolyT fun x => (c (d x)).ne
  gate : ∀ {α : Type} [Enc α] {d e : α → ℕ}, PolyT d → PolyT e → PolyT fun x => (c (d x)).gate (e x)
  bit : ∀ {α : Type} [Enc α] {d e : α → ℕ}, PolyT d → PolyT e → PolyT fun x => (c (d x)).bit (e x)

theorem sum_poly {a b : ℕ → Code} (h : Uniform a) (k : Uniform b) : Uniform (fun d => sum (a d) (b d)) := by
  constructor
  · intro α _ d hd; exact PolyT.add (h.ng hd) (k.ng hd)
  · intro α _ d hd; exact PolyT.add (h.nb hd) (k.nb hd)
  · intro α _ d hd; exact PolyT.add (h.ne hd) (k.ne hd)
  · intro α _ d e hd he; apply PolyT.ite' (c := fun x => e x < (a (d x)).ne) _ (h.gate hd he) (PolyT.add (h.ng hd) (k.gate hd (PolyT.sub he (h.ne hd)))); have := h.ne hd; fun_prop
  · intro α _ d e hd he; apply PolyT.ite' (c := fun x => e x < (a (d x)).ne) _ (h.bit hd he) (PolyT.add (h.nb hd) (k.bit hd (PolyT.sub he (h.ne hd)))); have := h.ne hd; fun_prop

theorem add_poly (n : ℕ → ℕ) (hn : ∀ {α : Type} [Enc α] {d : α → ℕ}, PolyT d → PolyT fun x => n (d x)) : Uniform (fun d => add (n d)) := by
  constructor <;> intros <;> simp only [add] <;> fun_prop (disch := solve_by_elim)

theorem mul_poly : Uniform mul := by
  constructor <;> intros <;> simp only [mul,wires] <;> fun_prop

theorem hash_poly : Uniform hash := sum_poly (sum_poly mul_poly mul_poly)
  (sum_poly (add_poly _ (by intros; fun_prop)) (sum_poly (add_poly _ (by intros; fun_prop)) (add_poly _ (by intros; fun_prop))))

/-- `copies n` consists of one initial block and `n` additional blocks. -/
def copies (A : w3_FactorLayout) : ℕ → w3_FactorLayout
  | 0 => A
  | n+1 => join A (copies A n)

def copiesCode (c : Code) : ℕ → Code
  | 0 => c
  | n+1 => sum c (copiesCode c n)

theorem copies_spec {a : Code} {A : w3_FactorLayout} (h : Models a A) (n : ℕ) : Models (copiesCode a n) (copies A n) := by
  induction n with
  | zero => exact h
  | succ n ih => exact sum_spec h ih

theorem copies_poly {a : ℕ → Code} (h : Uniform a) (n : ℕ) : Uniform fun d => copiesCode (a d) n := by
  induction n with
  | zero => exact h
  | succ n ih => exact sum_poly h ih

def seven {d : ℕ} (hd : 1 ≤ d) := copies (HashGateLayout.layout d hd) 6
def sevenCode (d : ℕ) := copiesCode (hash d) 6
theorem seven_spec {d : ℕ} (hd : 1 ≤ d) : Models (sevenCode d) (seven hd) := copies_spec (hash_spec hd) 6
theorem seven_poly : Uniform sevenCode := copies_poly hash_poly 6

theorem copies_ne (A : w3_FactorLayout) (n : ℕ) : (copies A n).ne = (n+1)*A.ne := by
  induction n with
  | zero => simp [copies]
  | succ n ih => simp only [copies,join,ih,Nat.succ_mul]; omega

theorem seven_edges {d : ℕ} (hd : 1 ≤ d) : (seven hd).ne < 35000*(d+2) := by
  rw [seven,copies_ne]; have := HashGateLayout.edges hd; omega

theorem copies_shape {A : w3_FactorLayout} {D : ℝ} {b : ℕ} (h : Shape A D b) (n : ℕ) : Shape (copies A n) D b := by
  induction n with
  | zero => exact h
  | succ n ih => exact join_shape h ih

theorem seven_shape {d : ℕ} (hd : 1 ≤ d) : Shape (seven hd) (HashGateLayout.degreeCap d) 2 := copies_shape (HashGateLayout.shape hd) 6

end DetDLP.S8H.PointAddresses


