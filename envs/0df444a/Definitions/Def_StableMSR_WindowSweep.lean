-- Prove2me | Definitions.Def_StableMSR_WindowSweep
-- name    : StableMSR_WindowSweep
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-25T05:21:05.842092+00:00
-- url     : https://prove2.me/theorems/1cade36b-7eaa-4428-916c-857ad0650a1c
-- title:
--   The memory image of a whole window and a candidate word
-- statement:
--   For a fixed vertex and candidate word, four vectors record seed selection, the persistent representatives, the least points and ownership intersections. A matrix records the membership rows. The prefix image specifies exactly which cells have been written after each seed index and which input cells remain available. The completed vertex image adds the feasibility bit and the next scratch allocation cursor.
-- source:
--   Implementation of the root-component and boundary requests in Appendix A.6 of Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, https://arxiv.org/abs/2611.03547.

import Definitions.Def_StableMSR_RegionalMenuImage

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.WindowSweep
open StableMSR.Recovery
open scoped Classical
set_option autoImplicit false

/-- The four seed-indexed vectors and the seed-by-point membership matrix used for one candidate. -/
inductive Cell (n : ℕ) where
  | mask (p : Fin n)
  | representative (p : Fin n)
  | minimum (p : Fin n)
  | touch (p : Fin n)
  | member (p q : Fin n)
  deriving DecidableEq

def Cell.seed {n : ℕ} : Cell n → Fin n
  | .mask p | .representative p | .minimum p | .touch p | .member p _ => p

/-- Base is the first seed index of this candidate in the global metadata arrays.
The local mask begins at its own scratch pointer. -/
structure Layout where
  base : ℕ
  mask : ℕ
  rep : ℕ
  first : ℕ
  touch : ℕ
  matrix : ℕ

def Layout.addr {n : ℕ} (L : Layout) : Cell n → ℕ
  | .mask p => L.mask+p.val
  | .representative p => L.rep+(L.base+p.val)
  | .minimum p => L.first+(L.base+p.val)
  | .touch p => L.touch+(L.base+p.val)
  | .member p q => L.matrix+(L.base+p.val)*n+q.val

/-- Concrete values under the least-seed convention. Unused metadata cells stay zero. -/
noncomputable def value {n : ℕ} (W : Cluster n) (C : ℕ → Cluster n)
    (owner : Fin n → Fin n) (v : ℕ) : Cell n → ℤ
  | .mask p | .representative p => if p.val ∈ BlockRows.representatives W C then 1 else 0
  | .minimum p => if p.val ∈ BlockRows.representatives W C then
      (if ne : (C p.val).Nonempty then (((C p.val).min' ne).val : ℤ) else 0) else 0
  | .touch p => if p.val ∈ BlockRows.representatives W C ∧ ∃ q ∈ C p.val,(owner q).val=v then 1 else 0
  | .member p q => if p∈W ∧ q∈C p.val then 1 else 0

/-- The input arrays may be read throughout the sweep. -/
structure Separated (n h buf win own : ℕ) (L : Layout) : Prop where
  inj : Function.Injective (L.addr (n:=n))
  digits : ∀ z : Cell n, ∀ j < 2*(h+1), L.addr z ≠ buf+j
  window : ∀ z : Cell n, ∀ q : Fin n, L.addr z ≠ win+q.val
  owners : ∀ z : Cell n, ∀ q : Fin n, L.addr z ≠ own+q.val

/-- The exact physical image after processing seed indices below j. -/
structure Image {n : ℕ} (L : Layout) (W : Cluster n) (C : ℕ → Cluster n)
    (owner : Fin n → Fin n) (v j : ℕ) (s t : State) : Prop where
  cells : ∀ z : Cell n, t.heap (L.addr z) = if z.seed.val < j then value W C owner v z else 0
  frame : ∀ a, (∀ z : Cell n, L.addr z ≠ a) → t.heap a=s.heap a
  flag : t.reg 172 = if ∀ i ∈ BlockRows.representatives W C, i < j → (C i).Nonempty then 1 else 0
  output : t.output=s.output
  closed : t.closed=s.closed

/-- Observable effect of one full call, including the feasibility cell of the window menu.
The arena below the old allocation cursor is protected outside the slot and menu cell. -/
structure VertexImage {n : ℕ} (L : Layout) (W : Cluster n) (m : ℤ → ℤ) (h c : ℕ)
    (owner : Fin n → Fin n) (v menuCell cursor : ℕ) (s t : State) : Prop where
  cells : ∀ z : Cell n, t.heap (L.addr z) = value W (BlockRows.rowBlock m W h c) owner v z
  feasible : t.heap menuCell = if Bits.feasible W (Bits.blocks m W h c) then 1 else 0
  frame : ∀ a < cursor, a ≠ menuCell → (∀ z : Cell n, L.addr z ≠ a) → t.heap a=s.heap a
  nextCursor : t.reg 8=((cursor+2*(h+1)+n : ℕ) : ℤ)
  output : t.output=s.output
  closed : t.closed=s.closed

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.WindowSweep


