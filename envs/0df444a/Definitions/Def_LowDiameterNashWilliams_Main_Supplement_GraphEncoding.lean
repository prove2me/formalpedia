-- Prove2me | Definitions.Def_LowDiameterNashWilliams_Main_Supplement_GraphEncoding
-- name    : LowDiameterNashWilliams_Main_Supplement_GraphEncoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T10:32:56.736489+00:00
-- url     : https://prove2.me/theorems/2c83b7ea-1e60-4d8e-87f2-eee36131527a
-- title:
--   Finite encoded graph inputs and rooted depth
-- statement:
--   A graph input records a finite vertex count $n$, a finite edge count $m$, and the two labelled endpoints of every edge. Its unordered endpoint map uses the published graph interface. Host simplicity is the published injectivity and no-loop condition. A root is one of the actual vertex labels. No packing is supplied as part of the input.
--
--   For an edge set $T$ and root $r$, define
--   $$\operatorname{depth}_r(T)=\sup_v\operatorname{dist}_T(r,v).$$
--   Distance and diameter retain the published extended nonnegative convention: disconnected pairs have infinite distance. The complete-graph predicate requires every distinct pair to be an edge. Packing predicates assert the existence of all $k$ edge-disjoint spanning trees with the requested bound on every tree.
--
--   The binary code lists self-delimiting encodings of $n,m$ and every pair of endpoints. A natural number is encoded by its canonical binary bits, preceded by the bit length in unary and a zero separator. A rooted code appends the root label. The finite relation constructor enumerates each unordered distinct pair once and includes it precisely when the given relation holds in either direction. These interfaces add no efficiency, existence, or tree-quality assertion.
-- source:
--   Pin-Hsian Lee, Peng-Ting Lin, Meng-Tsung Tsai, Ting-An Wu, STOC 2027 submission #1510 (October 2026), Section 2, pp. 4–5 (PDF pp. 5–6); Section 7, pp. 25–26 (PDF pp. 26–27)

import Mathlib
import Definitions.Def_LowDiameterNashWilliams_Main_Geometry

set_option autoImplicit false
open scoped ENNReal NNReal
open scoped BigOperators
open Classical
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn
open LowDiameterNashWilliams.Main

namespace LowDiameterNashWilliams.Main.Supplement

/-- Raw finite edge-list input. Validity uses the published Simple predicate, not a packing certificate. -/
structure GraphInput where
  n : ℕ
  m : ℕ
  uv : Fin m → Fin n × Fin n

def GraphInput.ends (G : GraphInput) (e : Fin G.m) : Sym2 (Fin G.n) :=
  s((G.uv e).1, (G.uv e).2)

/-- Binary natural, framed by its bit length in unary and a zero separator. -/
def natCode (n : ℕ) : List Bool :=
  List.replicate (Nat.bits n).length true ++ [false] ++ Nat.bits n

def GraphInput.encode (G : GraphInput) : List Bool :=
  natCode G.n ++ natCode G.m ++
    (List.ofFn fun e : Fin G.m => natCode (G.uv e).1.val ++ natCode (G.uv e).2.val).flatten

/-- One copy of each unordered nonloop pair for which the supplied relation holds in either direction. -/
noncomputable def graphFromRel (n : ℕ) (R : ℕ → ℕ → Prop) : GraphInput :=
  let es := ((List.ofFn fun u : Fin n => List.ofFn fun v : Fin n => (u,v)).flatten).filter
    fun p => decide (p.1.val < p.2.val ∧ (R p.1.val p.2.val ∨ R p.2.val p.1.val))
  ⟨n, es.length, fun e => es.get e⟩

noncomputable def depth {n m : ℕ} (ends : Fin m → Sym2 (Fin n))
    (T : Edges m) (r : Fin n) : ℝ≥0∞ :=
  ⨆ v : Fin n, distance ends T r v

def IsClique (G : GraphInput) : Prop :=
  Simple G.ends ∧ ∀ u v : Fin G.n, u ≠ v → ∃ e, G.ends e = s(u,v)

noncomputable def HasDepthPacking (G : GraphInput) (k : ℕ) (r : Fin G.n) (h : ℝ≥0∞) : Prop :=
  ∃ T : Trees k G.m, Packing G.ends T ∧ ∀ i, depth G.ends (T i) r ≤ h

noncomputable def HasDiameterPacking (G : GraphInput) (k : ℕ) (h : ℝ≥0∞) : Prop :=
  ∃ T : Trees k G.m, Packing G.ends T ∧ ∀ i, diameter G.ends (T i) ≤ h

/-- A specified root is structural input, with no trees supplied. -/
structure RootedInput where
  graph : GraphInput
  root : Fin graph.n

def RootedInput.encode (G : RootedInput) : List Bool :=
  G.graph.encode ++ natCode G.root.val

end LowDiameterNashWilliams.Main.Supplement


