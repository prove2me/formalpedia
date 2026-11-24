-- Prove2me | Definitions.Def_ULHC_LinkGraph
-- name    : ULHC_LinkGraph
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T03:02:22.132297+00:00
-- url     : https://prove2.me/theorems/f795fc82-d944-4f14-8888-f2767f769c81
-- title:
--   Link Graph
-- statement:
--   Definitions and structural lemmas for Link Graph, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/LinkGraph.lean

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_MinPath
import Theorems.Thm_ULHC_APair_flip
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v


set_option autoImplicit true
namespace ULHC
open Finset
def chainOKB (b c : StripSpec) : Bool :=
  (List.range c.n).all fun j =>
    decide (∀ x ∈ cellE (cellJ c.c c.s j), x ∈ cellE (endCell b) →
      j = 0 ∧ (x = lat1 (endCell b) b.s ∨ x = lat2 (endCell b) b.s))
def sideIdx : Side → ℕ
  | .b => 0
  | .t => 1
  | .l => 2
  | .r => 3
lemma sideIdx_inj : Function.Injective sideIdx := by
  intro a a' h
  cases a <;> cases a' <;> first | rfl | (simp [sideIdx] at h)
structure Node where
  σ : StripSpec
  pos : ℕ
  deriving DecidableEq
def Node.key (x : Node) : Lex (ℤ × Lex (ℤ × Lex (ℕ × Lex (ℕ × ℕ)))) :=
  toLex (x.σ.c.1, toLex (x.σ.c.2, toLex (sideIdx x.σ.s, toLex (x.σ.n, x.pos))))
lemma Node.key_inj : Function.Injective Node.key := by
  rintro ⟨⟨⟨c1, c2⟩, s, n⟩, p⟩ ⟨⟨⟨d1, d2⟩, s', m⟩, q⟩ h
  simp only [Node.key, toLex_inj, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, hs, rfl, rfl⟩ := h
  rw [sideIdx_inj hs]
instance : LinearOrder Node := LinearOrder.lift' Node.key Node.key_inj
section graph
variable (V : Finset Pt) (G : Finset Edge)
def cand : Finset StripSpec :=
  allStrips V G ∪ (V.filter (IsCell V)).biUnion (fun u => allStrips V (flip G u))
def candN : Finset Node :=
  (cand V G).biUnion fun σ => ({1, 2, 3} : Finset ℕ).image fun p => Node.mk σ p
def gsrc (x : Node) : Bool := x.pos == 1 && validB V G x.σ
def gmid (x : Node) : Bool := x.σ.n % 2 == 0
def gtgt (x : Node) : Bool := x.σ.n % 2 == 1
def gedge (x y : Node) : Bool :=
  (y.pos == min (x.pos + 1) 3) && cr2B V G x.σ y.σ && chainOKB x.σ y.σ
def gw (x : Node) : ℕ := x.σ.n
end graph
def posList : ℕ → List StripSpec → List Node
  | _, [] => []
  | k, σ :: L => ⟨σ, k⟩ :: posList (min (k + 1) 3) L
section facts
variable {V : Finset Pt} {G : Finset Edge}
end facts
def decode : List Node → Option (StripSpec × List StripSpec)
  | [] => none
  | x :: p => some (x.σ, p.map Node.σ)
def findPath (V : Finset Pt) (G : Finset Edge) : Option (StripSpec × List StripSpec) :=
  (MP.minPath (candN V G) (gsrc V G) gmid gtgt (gedge V G) gw).bind decode
section search
variable {V : Finset Pt} {G : Finset Edge}
end search
end ULHC


