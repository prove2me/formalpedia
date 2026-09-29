-- Prove2me | Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering
-- name    : AlgebraicCurve_TotallyDegenerateCovering
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/18acba26-7e47-546f-b221-1abee3d079db
-- title:
--   Two-sided totally degenerate coverings and their weighted dual graphs
-- statement:
--   Throughout, $L$ is a field, $A \subseteq L$ a valuation subring with residue field $k =$ `ResidueField A`, $F$ a field extension of $L$, and $\varpi$ an element of $A$. The structure [`AlgebraicCurve.TotallyDegenerateCovering A F ϖ`](../def/AlgebraicCurve_TotallyDegenerateCovering.html#L15) packages a bipartite totally degenerate semistable covering of the places of $F/L$ by charts and annuli. Its fields require $\varpi$ to lie in the maximal ideal of $A$ and to be non-zero in $L$, and then supply: a finite vertex type $V$ with a two-valued function `side : V → Fin 2`; a finite edge type $E$; for each $v \in V$ a `ComponentChart A F (RatFunc k)`, that is, a valuation subring `integers` of $F$ contracting to $A$ on $L$, a surjective reduction map onto the rational function field $k(t)$ whose kernel is the maximal ideal, a domain of places of $F/L$, a finite set `nodes` of places of $k(t)/k$, and a map on places compatible with evaluation at rational places and with divisors of functions away from the nodes; for each $e \in E$ two annuli `annOut e`, `annIn e` (each a set of places together with a parameter and a modulus in the maximal ideal of $A$, the places of the domain being parametrised bijectively by the admissible values of the parameter, with the unit principle for functions without zeros or poles); endpoint maps `src`, `tgt` with `side (src e) = 0`, `side (tgt e) = 1`; nodes `nodeOut e`, `nodeIn e` at which the outer and inner annuli are attached to the charts of `src e` and `tgt e` in the sense of `Annulus.IsAttached`; the conditions that the two presentations of $e$ have the same domain and modulus and that the product of the two parameters is the image of the modulus; a width `width e` in $\mathbb{N}^{+}$ with $A$-valuation of the modulus equal to the $\mathrm{width}(e)$-th power of that of $\varpi$; the requirement that the nodes of `chart v` are exactly the `nodeOut` of edges leaving $v$ and the `nodeIn` of edges entering $v$, each occurring once; and finally that the chart domains and annulus domains are pairwise disjoint and cover all places of $F/L$.
--
--   The definition `toDegeneracyData` reads off the weighted dual graph as the `DegeneracyData E V` with $a =$ `src`, $b =$ `tgt`, $w =$ `width`, with the three projections computed by simp lemmas; `src_ne_tgt` records that no edge joins a vertex to itself, which follows from the two side conditions.
--
--   **Relation to Mathlib.** Mathlib has no notion of component charts, annuli of places, or semistable coverings; these are the project's own structures, built over Mathlib's `ValuationSubring`, `Place` and `RatFunc`.
--
--   **Where it is used.** Such coverings describe the totally degenerate reduction of a curve whose components are rational, with the annuli recording the nodes and their thicknesses; the associated degeneracy datum feeds the ribbon kernel and the thickness-weighted Gram pairing, hence the component group of the Néron model attached to the special fibre. These are the shapes occurring for the Čerednik–Drinfeld fibre of a Shimura curve and the Deligne–Rapoport fibre of $X_0(Np)$, as used on the level-lowering side of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_TotallyDegenerateCovering.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_CerednikDrinfeld_Ribbon
import Mathlib.FieldTheory.RatFunc.AsPolynomial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

open IsLocalRing CerednikDrinfeld

variable {L : Type} [Field L] (A : ValuationSubring L) (F : Type) [Field F] [Algebra L F]

structure TotallyDegenerateCovering (ϖ : A) : Type 1 where

  ϖ_mem : ϖ ∈ maximalIdeal A
  ϖ_ne_zero : (ϖ : L) ≠ 0

  V : Type
  [instFintypeV : Fintype V]
  [instDecidableEqV : DecidableEq V]

  side : V → Fin 2

  E : Type
  [instFintypeE : Fintype E]
  [instDecidableEqE : DecidableEq E]

  chart : V → ComponentChart A F (RatFunc (ResidueField A))

  annOut : E → Annulus A F

  annIn : E → Annulus A F

  src : E → V

  tgt : E → V
  side_src : ∀ e, side (src e) = 0
  side_tgt : ∀ e, side (tgt e) = 1

  nodeOut : E → Place (ResidueField A) (RatFunc (ResidueField A))
  nodeIn : E → Place (ResidueField A) (RatFunc (ResidueField A))
  attachedOut : ∀ e, (annOut e).IsAttached (chart (src e)) (nodeOut e)
  attachedIn : ∀ e, (annIn e).IsAttached (chart (tgt e)) (nodeIn e)

  dom_eq : ∀ e, (annIn e).dom = (annOut e).dom
  modulus_eq : ∀ e, (annIn e).modulus = (annOut e).modulus
  param_mul_param : ∀ e, (annOut e).param * (annIn e).param = algebraMap L F ((annOut e).modulus : L)

  width : E → ℕ+

  valuation_modulus : ∀ e, A.valuation ((annOut e).modulus : L) = A.valuation (ϖ : L) ^ (width e : ℕ)

  mem_nodes_iff : ∀ (v : V) (x : Place (ResidueField A) (RatFunc (ResidueField A))),
    x ∈ (chart v).nodes ↔ (∃ e, src e = v ∧ nodeOut e = x) ∨ (∃ e, tgt e = v ∧ nodeIn e = x)

  nodeOut_injective : ∀ e e', src e = src e' → nodeOut e = nodeOut e' → e = e'
  nodeIn_injective : ∀ e e', tgt e = tgt e' → nodeIn e = nodeIn e' → e = e'

  cover : ∀ P : Place L F, (∃ v, P ∈ (chart v).dom) ∨ (∃ e, P ∈ (annOut e).dom)

  disjoint_chart : ∀ v v', v ≠ v' → Disjoint (chart v).dom (chart v').dom
  disjoint_chart_ann : ∀ v e, Disjoint (chart v).dom (annOut e).dom
  disjoint_ann : ∀ e e', e ≠ e' → Disjoint (annOut e).dom (annOut e').dom

attribute [instance] TotallyDegenerateCovering.instFintypeV TotallyDegenerateCovering.instDecidableEqV
  TotallyDegenerateCovering.instFintypeE TotallyDegenerateCovering.instDecidableEqE

namespace TotallyDegenerateCovering

variable {A F} {ϖ : A} (𝒞 : TotallyDegenerateCovering A F ϖ)

def toDegeneracyData : DegeneracyData 𝒞.E 𝒞.V where
  a := 𝒞.src
  b := 𝒞.tgt
  w := 𝒞.width

@[simp] theorem toDegeneracyData_a (e : 𝒞.E) : 𝒞.toDegeneracyData.a e = 𝒞.src e := rfl
@[simp] theorem toDegeneracyData_b (e : 𝒞.E) : 𝒞.toDegeneracyData.b e = 𝒞.tgt e := rfl
@[simp] theorem toDegeneracyData_w (e : 𝒞.E) : 𝒞.toDegeneracyData.w e = 𝒞.width e := rfl

protected theorem src_ne_tgt (e : 𝒞.E) : 𝒞.src e ≠ 𝒞.tgt e := fun h => by
  have h0 := 𝒞.side_src e
  rw [h, 𝒞.side_tgt e] at h0
  exact one_ne_zero h0

end TotallyDegenerateCovering

end AlgebraicCurve

end


