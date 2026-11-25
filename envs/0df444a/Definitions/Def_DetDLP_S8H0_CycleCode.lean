-- Prove2me | Definitions.Def_DetDLP_S8H0_CycleCode
-- name    : DetDLP_S8H0_CycleCode
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T06:51:30.875378+00:00
-- url     : https://prove2.me/theorems/153ab921-e83e-4e41-a9e7-e1026a4b1bba
-- title:
--   Polynomial-time endpoints for named copy-cycle wiring
-- statement:
--   Compute a signal occurrence’s successor by filtering the finite range of occurrence indices for its signal name, then taking the next index cyclically. This equals the successor permutation in the named-wire construction. From any numerical model of a factor layout and a polynomial-time signal name function, obtain numerical endpoints of the copy-cycle graph; its endpoint computations are polynomial-time when the occurrence count is unary bounded.
-- source:
--   DetDLP S8H named-wire copy-cycle implementation accompanying s8h_ec_order_query, UUID f0e81f0e-6143-4672-a126-0c2b5aa2d552.

import Definitions.Def_DetDLP_S8H_NamedWires
import Definitions.Def_DetDLP_S8H_PointAddresses

set_option autoImplicit false
namespace DetDLP.S8H0.CycleCode
open S8H S8H.PointAddresses Groundwork
attribute [-simp] Fin.natAdd_eq_addNat

def fiber (n : ℕ) (name : ℕ → ℕ) (i : ℕ) := (List.range n).filter fun j => decide (name j = name i)

def next (n : ℕ) (name : ℕ → ℕ) (i : ℕ) :=
  let l := fiber n name i
  l.getD ((l.idxOf i+1)%l.length) i

theorem fiber_eq {n : ℕ} (name : ℕ → ℕ) (i : Fin n) :
    fiber n name i.val = (NamedWires.fiber (fun z : Fin n => name z.val) (name i.val)).map Fin.val := by
  unfold fiber NamedWires.fiber
  have hr : List.range n = (List.finRange n).map Fin.val := by simp
  rw [hr, List.filter_map]; rfl

theorem next_eq {n : ℕ} (name : ℕ → ℕ) (i : Fin n) :
    next n name i.val = (NamedWires.next (fun z : Fin n => name z.val) i).val := by
  let N := fun z : Fin n => name z.val
  let l := NamedWires.fiber N (N i)
  have hi : i ∈ l := by simp [l]
  have hp : 0 < l.length := List.length_pos_of_mem hi
  have hk : l.idxOf i < l.length := List.idxOf_lt_length_of_mem hi
  have hm : i.val ∈ l.map Fin.val := List.mem_map_of_mem hi
  let k := (l.map Fin.val).idxOf i.val
  have ht : k < l.length := by simpa [k] using List.idxOf_lt_length_of_mem hm
  have hval : (l[k]).val = i.val := by
    simpa only [List.getElem_map,k] using List.getElem_idxOf (List.idxOf_lt_length_of_mem hm)
  have hget : l[k] = i := Fin.ext hval
  have H := List.formPerm_apply_getElem l (NamedWires.fiber_nodup N _) k ht
  rw [hget] at H
  unfold next; rw [fiber_eq]; change (l.map Fin.val).getD ((k+1)%(l.map Fin.val).length) i.val = (l.formPerm i).val
  rw [H,List.length_map,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simpa using Nat.mod_lt (k+1) hp)]
  simp

attribute [local fun_prop] PolyT.comp PolyT.const PolyT.fst PolyT.snd PolyT.prodMk PolyT.length PolyT.mod PolyT.id'
  P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_ite__226169acf219

theorem next_poly {α : Type} [Enc α] {n i : α → ℕ} {name : α → ℕ → ℕ}
    (hn : Unary n) (hi : PolyT i) (hs : PolyT fun z : α × ℕ => name z.1 z.2) :
    PolyT fun x => next (n x) (name x) (i x) := by
  have hsi := PolyT.comp hs (PolyT.prodMk PolyT.id' hi)
  have hsi' : PolyT fun z : α × ℕ => name z.1 (i z.1) := PolyT.comp hsi (by fun_prop)
  have hl : PolyT fun x => fiber (n x) (name x) (i x) := by
    apply PolyT.filter (hl := PolyT.range hn); fun_prop
  unfold next; apply PolyT.getD hl _ hi
  exact PolyT.mod (PolyT.add (PolyT.idxOf hi hl) (PolyT.const 1)) (PolyT.length hl)

def code (c : Code) (name : ℕ → ℕ) : Code :=
  ⟨c.ng+c.ne,c.ne,c.ne+(c.ne+c.ne),
    fun e => if e < c.ne then c.gate e else c.ng+(if e-c.ne < c.ne then e-c.ne else e-c.ne-c.ne),
    fun e => if e < c.ne then e else if e-c.ne < c.ne then e-c.ne else next c.ne name (e-c.ne-c.ne)⟩

theorem models {c : Code} {A : w3_FactorLayout} (h : Models c A) (name : ℕ → ℕ) :
    Models (code c name) (CopyCycle.layout A.gate (NamedWires.next fun e : Fin A.ne => name e.val)) := by
  refine ⟨congrArg₂ (·+·) h.ng h.ne,h.ne,by simp [code,h.ne],?_,?_⟩
  all_goals intro e; induction e using Fin.addCases with
    | left e => simp [code,CopyCycle.layout,h.ne,e.isLt,h.gate]
    | right e => induction e using Fin.addCases with
      | left e => simp [code,CopyCycle.layout,h.ne,e.isLt,h.ng]
      | right e => simp [code,CopyCycle.layout,h.ne,h.ng,next_eq]


set_option maxHeartbeats 1200000 in
theorem endpoints_poly {α : Type} [Enc α] {c : α → Code} {name : α → ℕ → ℕ}
    (hg : PolyT fun x => (c x).ng) (he : PolyT fun x => (c x).ne) (hu : Unary fun x => (c x).ne)
    (hgate : PolyT fun z : α × ℕ => (c z.1).gate z.2) (hs : PolyT fun z : α × ℕ => name z.1 z.2) :
    (PolyT fun z : α × ℕ => (code (c z.1) (name z.1)).gate z.2) ∧
    (PolyT fun z : α × ℕ => (code (c z.1) (name z.1)).bit z.2) := by
  have hg' := PolyT.comp hg (PolyT.fst (PolyT.id' (α := α × ℕ)))
  have he' := PolyT.comp he (PolyT.fst (PolyT.id' (α := α × ℕ)))
  have hu' : Unary fun z : α × ℕ => (c z.1).ne := PolyT.comp (g := Prod.fst) hu (by fun_prop)
  have hs' : PolyT fun z : (α × ℕ) × ℕ => name z.1.1 z.2 := PolyT.comp (g := fun z : (α × ℕ) × ℕ => (z.1.1,z.2)) hs (by fun_prop)
  have hn := next_poly (name := fun z : α × ℕ => name z.1) (i := fun z : α × ℕ => z.2-(c z.1).ne-(c z.1).ne) hu' (by fun_prop) hs'
  constructor <;> unfold code <;> dsimp only <;> fun_prop (disch := assumption)

theorem packetEndpoints {c : Code} {A : w3_FactorLayout} (h : Models c A) (name : ℕ → ℕ) :
    let C := code c name
    let G := w3_factorGraph (CopyCycle.layout A.gate (NamedWires.next fun e : Fin A.ne => name e.val))
    C.ng+C.nb = G.nV ∧ C.ne = G.nE ∧
    (∀ i : Fin G.nE, C.gate i.val = (G.endpoints i).1.val) ∧
     ∀ i : Fin G.nE, C.ng+C.bit i.val = (G.endpoints i).2.val := by
  let H := models h name
  refine ⟨congrArg₂ (·+·) H.ng H.nb,H.ne, fun i => H.gate i,?_⟩
  intro i
  exact congrArg₂ (·+·) H.ng (H.bit i)

end DetDLP.S8H0.CycleCode


