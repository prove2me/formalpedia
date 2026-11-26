-- Prove2me | Definitions.Def_SP4WhiteheadSketch
-- name    : SP4WhiteheadSketch
-- status  : Definition
-- author  : @loader3229
-- created : 2026-11-26T10:41:04.997419+00:00
-- url     : https://prove2.me/theorems/597e224b-2491-5d96-8f60-1f76cf20ffea
-- title:
--   Cellular map between CW complexes
-- statement:
--   A continuous map `f` between CW complexes is **cellular** if it sends the `n`-skeleton of the source into the `n`-skeleton of the target, for every `n`:
--   $$f(X^{n})\subseteq Y^{n}\quad\text{for all }n.$$
--   This is the notion to which the cellular approximation theorem applies.  In the Whitehead argument the map of a CW pair must be cellular so that its mapping cone is again a CW complex and the compression lemma can be run cell by cell over the skeleta.
-- source:
--   同伦论(2) Whitehead定理与胞腔逼近, 知乎专栏 https://zhuanlan.zhihu.com/p/22412267564 (压缩引理、胞腔逼近定理、Whitehead 定理证明); A. Hatcher, Algebraic Topology, Cambridge University Press (2002), §4.1 Proposition 4.8 (cellular approximation) and Theorem 4.5 (Whitehead).

import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.CWComplex.Classical.Basic

set_option autoImplicit false

open scoped ContinuousMap

universe u v

namespace SP4WhiteheadSketch

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [T2Space X] [T2Space Y]
  [Topology.CWComplex (Set.univ : Set X)]
  [Topology.CWComplex (Set.univ : Set Y)]

/-- A continuous map between CW complexes is cellular when it sends the `n`-skeleton of the
source into the `n`-skeleton of the target, for every `n`.  This is the notion used in the
cellular approximation theorem: the reference map of a CW pair is required to be cellular
so that the mapping cone carries a CW structure. -/
def CellularMap (f : C(X, Y)) : Prop :=
  ∀ n : ℕ, Set.MapsTo f (Topology.CWComplex.skeleton (Set.univ : Set X) n : Set X)
    (Topology.CWComplex.skeleton (Set.univ : Set Y) n : Set Y)

end SP4WhiteheadSketch


