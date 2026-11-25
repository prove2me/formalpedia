-- Prove2me | Definitions.Def_DetDLP_S8H0_AnchoredLayout
-- name    : DetDLP_S8H0_AnchoredLayout
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T06:59:32.698797+00:00
-- url     : https://prove2.me/theorems/b9e4357f-4090-478d-b837-f43077ac7471
-- title:
--   Anchored occurrence wiring for Boolean factor layouts
-- statement:
--   A unary always-true gate anchors each signal. Adding these anchors and closing occurrence fibres under copy cycles yields a graph whose logical assignments are exactly the assignments satisfying the original named tests. The associated numerical endpoints model the extended incidence layout.
-- source:
--   DetDLP elliptic-curve order query, UUID f0e81f0e-6143-4672-a126-0c2b5aa2d552.

import Definitions.Def_DetDLP_S8H0_CycleCode
import Definitions.Def_DetDLP_S8J_CircuitRealizes

set_option autoImplicit false
namespace DetDLP.S8H0.AnchoredLayout
open S8H S8H.PointAddresses S8J S8J.CircuitRealizes
attribute [-simp] Fin.natAdd_eq_addNat

def anchors (k : ℕ) : w3_FactorLayout := ⟨k,k,k,id,id,id,by simp⟩

def block (b : Block) (k : ℕ) : Block :=
  ⟨join (anchors k) b.A,joinTest (fun _ _ => true) b.t⟩

variable (b : Block) {k : ℕ} (name : Fin b.A.ne → Fin k)

def signal : Fin (block b k).A.ne → Fin k := Fin.addCases id name

def wiring : Wiring (block b k).A.ne k where
  next := NamedWires.next (signal b name)
  signal := signal b name
  rep := Fin.castAdd b.A.ne
  section_eq i := Fin.addCases_left ..
  next_eq i := NamedWires.name_next _ i
  connected a h i := NamedWires.constant _ h (Fin.addCases_left ..)

abbrev Good (x : Fin k → Bool) := ∀ g, b.t g (fun e => x (name e.val)) = true

theorem logical_iff (x : Fin k → Bool) :
    (∀ g, (block b k).t g (fun e => x ((wiring b name).signal e.val)) = true) ↔ Good b name x := by
  constructor
  · intro h g
    simpa [block,joinTest,wiring,signal,anchors] using h (Fin.natAdd k g)
  · intro h g
    induction g using Fin.addCases with
    | left i => simp [block,joinTest]
    | right i => simpa [block,joinTest,wiring,signal,anchors] using h i

def assignments : Logical (block b k) (wiring b name) ≃ {x // Good b name x} :=
  Equiv.subtypeEquivRight (logical_iff b name)

def anchorCode (k : ℕ) : Code := ⟨k,k,k,id,id⟩

def withAnchors (k : ℕ) (c : Code) := sum (anchorCode k) c

theorem anchorModels (k : ℕ) : Models (anchorCode k) (anchors k) :=
  ⟨rfl,rfl,rfl,fun _ => rfl,fun _ => rfl⟩

def signalNat (k : ℕ) (f : ℕ → ℕ) (i : ℕ) := if i < k then i else f (i-k)

theorem signal_spec (f : ℕ → ℕ) (hf : ∀ i : Fin b.A.ne, f i.val = (name i).val) (i : Fin (block b k).A.ne) :
    signalNat k f i.val = (signal b name i).val := by
  induction i using Fin.addCases with
  | left i =>
    change Fin k at i
    change (if i.val < k then i.val else f (i.val-k)) = (Fin.addCases (motive := fun _ => Fin k) id name (i.castAdd b.A.ne)).val
    simp [i.isLt]
  | right i => simp [signalNat,signal,anchors,hf]

theorem next_congr {n : ℕ} {K L : Type} [DecidableEq K] [DecidableEq L] (f : Fin n → K) (g : Fin n → L)
    (h : ∀ i j, f i = f j ↔ g i = g j) : NamedWires.next f = NamedWires.next g := by
  apply Equiv.ext; intro i
  change (NamedWires.fiber f (f i)).formPerm i = (NamedWires.fiber g (g i)).formPerm i
  congr 2
  unfold NamedWires.fiber; apply List.filter_congr; intro j _; simp only [h j i]

def code (k : ℕ) (c : Code) (f : ℕ → ℕ) := CycleCode.code (withAnchors k c) (signalNat k f)

theorem code_spec {c : Code} (hc : Models c b.A) (f : ℕ → ℕ) (hf : ∀ i : Fin b.A.ne, f i.val = (name i).val) :
    Models (code k c f) (circuit (block b k) (wiring b name)) := by
  let s := signal b name
  have hs : NamedWires.next (fun e : Fin (block b k).A.ne => signalNat k f e.val) = NamedWires.next s := by
    apply next_congr; intro i j; rw [signal_spec b name f hf,signal_spec b name f hf]; exact Fin.val_inj
  have ha : Models (withAnchors k c) (block b k).A := sum_spec (anchorModels k) hc
  have hh := CycleCode.models ha (signalNat k f)
  rw [hs] at hh
  exact hh

end DetDLP.S8H0.AnchoredLayout


