-- Prove2me | Definitions.Def_DetDLP_W4_M5PortEval
-- name    : DetDLP_W4_M5PortEval
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T02:00:15.213962+00:00
-- url     : https://prove2.me/theorems/e9bac233-a998-428f-950e-3bd04795ef31
-- title:
--   Polynomial-time port enumeration and wire lookup
-- statement:
--   Enumerating incident edges by their natural-number endpoints reproduces the graph port order. Wire lookup and unary-bounded port enumeration preserve polynomial time.

import Definitions.Def_DetDLP_W4_M5EvalFrontend

set_option autoImplicit false
namespace DetDLP.w4_M5PortEval
open Groundwork Groundwork.PolyT w4_M5GraphBounds w4_M5PortTensor w4_MulParams

private theorem vals_range (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem
  · simp
  · intro i h h'; simp

private theorem map_filter_val {n} (l : List (Fin n)) (p : Fin n → Bool) (q : ℕ → Bool)
    (hq : ∀ i, p i = q i.val) : (l.filter p).map Fin.val = (l.map Fin.val).filter q := by
  induction l with
  | nil => rfl
  | cons i l ih => cases h : p i <;> simp [h,ih,← hq i]

private theorem idxOf_val {n} (l : List (Fin n)) (i : Fin n) :
    (l.map Fin.val).idxOf i.val = l.idxOf i := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    by_cases hj : j = i
    · subst j; simp
    · have hval : j.val ≠ i.val := fun h => hj (Fin.ext h)
      simp [hj, hval, ih]

def portsNat (ne v : ℕ) (src dst : ℕ → ℕ) : List ℕ :=
  (List.range ne).filter (fun e => decide (src e = v ∨ dst e = v))

theorem portsNat_eq (G : BipartiteMultigraph) (v : Fin G.nV) (src dst : ℕ → ℕ)
    (hs : ∀ e : Fin G.nE, src e.val = (G.endpoints e).1.val)
    (ht : ∀ e : Fin G.nE, dst e.val = (G.endpoints e).2.val) :
    portsNat G.nE v.val src dst = (G.ports v).map Fin.val := by
  unfold portsNat BipartiteMultigraph.ports
  rw [← vals_range G.nE]
  symm
  apply map_filter_val
  intro i; simp [hs,ht,Fin.ext_iff]

def readNat (ports : List ℕ) (a : List Bool) (edge : ℕ) : Bool :=
  a[ports.idxOf edge]?.getD false

theorem readNat_eq {d : ℕ} (hd : 1 ≤ d) (v : Fin (graph d hd).nV)
    (a : Fin ((graph d hd).deg v) → Bool) (e : Edge d (W d)) :
    readNat (((graph d hd).ports v).map Fin.val) (List.ofFn a) (edgeIndex d (W d) e).val = readWire hd v a e := by
  unfold readNat readWire
  rw [idxOf_val ((graph d hd).ports v) (edgeIndex d (W d) e)]
  rfl

attribute [local fun_prop] Groundwork.PolyT.comp Groundwork.PolyT.const Groundwork.PolyT.fst Groundwork.PolyT.snd Groundwork.PolyT.prodMk
  Groundwork.PolyT.filter Groundwork.PolyT.idxOf P2M_Groundwork_PolyT_id__1c5d0f44cc8f

theorem readNat_poly {α} [Enc α] {p : α → List ℕ} {a : α → List Bool} {e : α → ℕ}
    (hp : PolyT p) (ha : PolyT a) (he : PolyT e) : PolyT (fun x => readNat (p x) (a x) (e x)) := by
  unfold readNat; fun_prop

theorem portsNat_poly {α} [Enc α] {ne v : α → ℕ} {s t : α → ℕ → ℕ}
    (hn : Unary ne) (hv : PolyT v) (hs : PolyT fun p : α × ℕ => s p.1 p.2)
    (ht : PolyT fun p : α × ℕ => t p.1 p.2) :
    PolyT (fun x => portsNat (ne x) (v x) (s x) (t x)) := by
  apply Groundwork.PolyT.filter (hl := Groundwork.PolyT.range hn)
  change PolyT (fun p : α × ℕ => decide (s p.1 p.2 = v p.1 ∨ t p.1 p.2 = v p.1))
  have hv' : PolyT (fun p : α × ℕ => v p.1) := Groundwork.PolyT.comp hv (by fun_prop)
  have a : PolyT (fun p : α × ℕ => decide (s p.1 p.2 = v p.1)) := by fun_prop
  have b : PolyT (fun p : α × ℕ => decide (t p.1 p.2 = v p.1)) := by fun_prop
  have c : PolyT (fun p : α × ℕ => decide (s p.1 p.2 = v p.1) || decide (t p.1 p.2 = v p.1)) := by fun_prop
  exact c.congr fun p => by simp

end DetDLP.w4_M5PortEval


