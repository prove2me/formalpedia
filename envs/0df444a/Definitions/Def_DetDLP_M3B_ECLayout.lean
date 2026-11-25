-- Prove2me | Definitions.Def_DetDLP_M3B_ECLayout
-- name    : DetDLP_M3B_ECLayout
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T10:09:04.688628+00:00
-- url     : https://prove2.me/theorems/f7ff21d5-e58a-413d-9732-0752d5c6614f
-- title:
--   Stage II separator read-only lookup layout
-- statement:
--   Adds exact-arity lookup gates to an arithmetic layout, preserves accepted bit assignments, and supplies uniform polynomial-time incidence addressing.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8J_HashGateLayout
import Definitions.Def_DetDLP_S8H_PointAddresses

set_option autoImplicit false
namespace DetDLP.M3B.ECLayout
open S8J S8H.PointAddresses
attribute [-simp] Fin.natAdd_eq_addNat

/- Append `n` read-only lookup gates to a layout. Each reads `k` possibly
    non-contiguous registers, and no register or witness is added. -/
variable (A : w3_FactorLayout) {n k : ℕ} (bus : Fin n → Fin k → Fin A.nb)

def row (e : Fin (n*k)) : Fin n := (finProdFinEquiv.symm e).1
def column (e : Fin (n*k)) : Fin k := (finProdFinEquiv.symm e).2

def layout : w3_FactorLayout where
  ng := A.ng + n
  ne := A.ne + n*k
  nb := A.nb
  gate := splitMap A.gate row
  bit := Fin.addCases A.bit (fun e => bus (row e) (column e))
  rep := Fin.castAdd _ ∘ A.rep
  rep_bit b := by simp [A.rep_bit]

def test (t : w3_factorTest A) : w3_factorTest (layout A bus) := Fin.addCases
  (fun g x => t g fun e => x ⟨Fin.castAdd _ e.1, by simp [layout,splitMap,e.2]⟩)
  (fun _ _ => true)

theorem accept_iff (t : w3_factorTest A) (x : Fin A.nb → Bool) :
    Accept (layout A bus) (test A bus t) x ↔ Accept A t x := by
  constructor
  · intro h g
    simpa [layout,test,splitMap] using h (Fin.castAdd n g)
  · intro h g
    induction g using Fin.addCases with
    | left g => simpa [layout,test,splitMap] using h g
    | right i => simp [layout,test]

def acceptEquiv (t : w3_factorTest A) : {x // Accept (layout A bus) (test A bus t) x} ≃
    {x // Accept A t x} := Equiv.subtypeEquivRight (accept_iff A bus t)

private theorem degCard {a b : ℕ} (f : Fin a → Fin b) (v : Fin b) :
    degreeOf f v = Fintype.card {e // f e = v} := by
  rw [Fintype.card_subtype, degreeOf, ← List.toFinset_card_of_nodup ((List.nodup_finRange _).filter _)]
  apply congrArg Finset.card
  ext; simp

def rowEquiv (i : Fin n) : {e : Fin (n*k) // row e = i} ≃ Fin k where
  toFun e := column e.1
  invFun j := ⟨finProdFinEquiv (i,j), by simp [row]⟩
  left_inv e := by
    apply Subtype.ext
    apply finProdFinEquiv.symm.injective
    simp only [Equiv.symm_apply_apply]
    exact Prod.ext e.2.symm rfl
  right_inv j := by simp [column]

theorem lookup_degree (i : Fin n) :
    (w3_factorGraph (layout A bus)).deg (Fin.castAdd A.nb (Fin.natAdd A.ng i)) = k := by
  apply (w3_gateDegree (layout A bus) (Fin.natAdd A.ng i)).trans
  change degreeOf (splitMap A.gate (@row n k)) (Fin.natAdd A.ng i) = k
  rw [degree_right,degCard,Fintype.card_congr (rowEquiv i),Fintype.card_fin]

theorem ordinary_degree (g : Fin A.ng) :
    (w3_factorGraph (layout A bus)).deg (Fin.castAdd A.nb (Fin.castAdd n g)) =
    (w3_factorGraph A).deg (Fin.castAdd A.nb g) := by
  exact (w3_gateDegree (layout A bus) (Fin.castAdd n g)).trans
    ((degree_left A.gate (@row n k) g).trans (w3_gateDegree A g).symm)

def edge (i : Fin n) (j : Fin k) : Fin (layout A bus).ne :=
  Fin.natAdd A.ne (finProdFinEquiv (i,j))

def vertex (i : Fin n) : Fin (w3_factorGraph (layout A bus)).nV :=
  Fin.castAdd A.nb (Fin.natAdd A.ng i)

theorem incidence (i : Fin n) (j : Fin k) : edge A bus i j ∈
    (w3_factorGraph (layout A bus)).ports (vertex A bus i) := by
  apply w3_gateInc
  simp [edge,layout,splitMap,row]

theorem read_bit (i : Fin n) (j : Fin k) : (layout A bus).bit (edge A bus i j) = bus i j := by
  simp only [layout,edge,Fin.addCases_right,row,column,Equiv.symm_apply_apply]

/-- Port order is not assumed to coincide with significance order. -/
def port (i : Fin n) (j : Fin k) := (w3_factorGraph (layout A bus)).portIndex
  (vertex A bus i) (edge A bus i j) (incidence A bus i j)

theorem read_local (x : Fin (layout A bus).ne → Bool) (i : Fin n) (j : Fin k) :
    w3_wireLocal _ (vertex A bus i) x (port A bus i j) = x (edge A bus i j) := by
  exact congrArg x (w3_factorGet (layout A bus) _ _ (incidence A bus i j))

theorem read_accepted (t : w3_factorTest A)
    (x : {x // (w3_factorGraph (layout A bus)).Satisfies (w3_factorChecks _ (test A bus t)) x})
    (i : Fin n) (j : Fin k) : w3_wireLocal _ (vertex A bus i) x.1 (port A bus i j) =
      (w3_factorEquiv _ _ x).1 (bus i j) := by
  apply (read_local A bus x.1 i j).trans
  have h := ((w3_factorSatisfies _ _ _).mp x.2).2 (edge A bus i j)
  rw [read_bit] at h
  exact h

/-- A separate equivalence supplies the EC block/slot/side numbering. -/
def gateSlots {q : w3_Query} (num : Fin n ≃ w3_lookupSlot q) :
    Fin (layout A bus).ng ≃ (w3_lookupSlot q ⊕ Fin A.ng) :=
  finSumFinEquiv.symm.trans ((Equiv.sumComm _ _).trans (Equiv.sumCongr num (Equiv.refl _)))

/-- Total indexing formulas for the graph builder, valid on malformed inputs too. -/
def code (a : Code) (n k : ℕ) (addr : ℕ → ℕ → ℕ) : Code :=
  ⟨a.ng+n, a.nb, a.ne+n*k,
   fun e => if e < a.ne then a.gate e else a.ng + (e-a.ne)/k,
   fun e => if e < a.ne then a.bit e else addr ((e-a.ne)/k) ((e-a.ne)%k)⟩

theorem models {a : Code} (h : Models a A) (addr : ℕ → ℕ → ℕ)
    (ha : ∀ i j, addr i.val j.val = (bus i j).val) :
    Models (code a n k addr) (layout A bus) := by
  refine ⟨congrArg (·+n) h.ng, h.nb, congrArg (·+n*k) h.ne, ?_, ?_⟩
  · intro e
    induction e using Fin.addCases with
    | left u => simp [code,layout,splitMap,h.ne,u.isLt,h.gate]
    | right u => simp [code,layout,splitMap,h.ne,h.ng,row,Fin.divNat]
  · intro e
    induction e using Fin.addCases with
    | left u => simp [code,layout,splitMap,h.ne,u.isLt,h.bit]
    | right u => simpa [code,layout,h.ne,row,column,Fin.divNat,Fin.modNat] using ha (row u) (column u)

open Groundwork
attribute [local fun_prop] PolyT.const PolyT.mul PolyT.div PolyT.mod PolyT.comp
  P2M_Groundwork_PolyT_ite__226169acf219

theorem uniform {a : ℕ → Code} (ha : Uniform a) {n k : ℕ → ℕ} {addr : ℕ → ℕ → ℕ → ℕ}
    (hn : ∀ {α : Type} [Enc α] {d : α → ℕ}, PolyT d → PolyT fun x => n (d x))
    (hk : ∀ {α : Type} [Enc α] {d : α → ℕ}, PolyT d → PolyT fun x => k (d x))
    (hr : ∀ {α : Type} [Enc α] {d i j : α → ℕ}, PolyT d → PolyT i → PolyT j →
      PolyT fun x => addr (d x) (i x) (j x)) :
    Uniform fun d => code (a d) (n d) (k d) (addr d) := by
  constructor
  · intros; exact PolyT.add (ha.ng ‹_›) (hn ‹_›)
  · intros; exact ha.nb ‹_›
  · intros; exact PolyT.add (ha.ne ‹_›) (PolyT.mul (hn ‹_›) (hk ‹_›))
  · intro α _ d e hd he
    have hne := ha.ne hd
    apply PolyT.ite' (c := fun x => e x < (a (d x)).ne) _ (ha.gate hd he)
      (PolyT.add (ha.ng hd) (PolyT.div (PolyT.sub he hne) (hk hd)))
    fun_prop
  · intro α _ d e hd he
    have hne := ha.ne hd
    apply PolyT.ite' (c := fun x => e x < (a (d x)).ne) _ (ha.bit hd he)
      (hr hd (PolyT.div (PolyT.sub he hne) (hk hd)) (PolyT.mod (PolyT.sub he hne) (hk hd)))
    fun_prop

end DetDLP.M3B.ECLayout


