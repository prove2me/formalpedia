-- Prove2me | Definitions.Def_ModularCurve_MultCoveringAnnuli
-- name    : ModularCurve_MultCoveringAnnuli
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/a3489e61-92b3-5916-ac1a-db825bc67d3c
-- title:
--   Annulus context for the multiplicative covering of X0​(p)
-- statement:
--   Fix a prime $p$, a valuation subring $A$ of $\overline{\mathbb Q}$ whose residue field $k$ has characteristic $p$, and a chart context $\Gamma$ for the level $1\cdot p$ modular function field: $\Gamma$ provides two component charts over $A$ (the chart `infChart` and its Fricke conjugate `zeroChart`) together with the enumeration $e \mapsto a_e =$ `ssValue` $\Gamma\,e$ of the finite set `ssJSet` $p\,k$ of supersingular $j$-values by $e \in$ `Fin (mAnnuli p)`. The structure `AnnCtx` $\Gamma$ is the datum, for each such $e$, of a pair of annuli $\mathrm{An}\,e$, $\mathrm{An}'\,e$ in $\overline{\mathbb Q}$-level $1\cdot p$ modular function field relative to $A$ (each an `Annulus`: a set of places, a parameter, and a modulus in the maximal ideal of $A$, subject to the one-dimensional-disc axioms), subject to fields that are themselves assertions: the two annuli have the same place set and the same modulus, the modulus is nonzero in $\overline{\mathbb Q}$, and the product of the two parameters equals the image of the modulus under $\overline{\mathbb Q} \to$ the function field — so the pair presents a single two-ended annulus. Further fields prescribe the place set as the set of $W$ with `IsSSCentred` $p\,A\,W\,a_e$, fix the parameter of $\mathrm{An}\,e$ to be `tieG` $p = j(q^p) - j^p$ whenever $a_e \ne 0, 1728$, fix the modulus to be $p^{\,\mathrm{jWidth}(a_e)}$ in $A$, where $\mathrm{jWidth}$ is $3$ at $0$, $2$ at $1728$ and $1$ otherwise, and require $\mathrm{An}\,e$ to be attached (in the sense of `Annulus.IsAttached`: the node lies in the chart's nodes, the parameter has residue of order one there, and a unit/slope condition holds) to the chart `chart` $\Gamma$ (`src` $p\,e$) at the node $\tilde\jmath = a_e^{\,p}$, and $\mathrm{An}'\,e$ to the chart `chart` $\Gamma$ (`tgt` $p\,e$) at the node $\tilde\jmath = a_e$. The abbreviations `annIn`, `annOut` rename $\mathrm{An}$, $\mathrm{An}'$, and `twoEnded`, `attached` restate the corresponding fields as conjunctions in the shape used by the covering statement.
--
--   **Relation to Mathlib.** Mathlib has no notion of component charts, annuli or semistable coverings of curves in this valuation-theoretic form; `Annulus`, `ComponentChart` and `Annulus.IsAttached` are the project's own, and `AnnCtx` merely packages a family of them over a chart context.
--
--   **Where it is used.** The annuli recorded here are the tubular pieces of the semistable covering of $X_0(p)$ at the supersingular points, one two-ended annulus per supersingular $j$-invariant, with width dictated by the extra automorphisms at $j = 0$ and $j = 1728$. Bundling them as a structure over the chart context lets each clause of the multiplicative covering statement for level $1 \cdot p$ be proved with $(\Gamma, \Delta)$ as standing data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_MultCoveringAnnuli.lean

import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_ModularCurve_JWidth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve

namespace ModularCurve.MultCovering

variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]

structure AnnCtx (Γ : ChartCtx p A) where

  An  : Fin (mAnnuli p) → Annulus A ↥(modularFunctionFieldBar (1 * p))

  An' : Fin (mAnnuli p) → Annulus A ↥(modularFunctionFieldBar (1 * p))

  dom_eq : ∀ e, (An' e).dom = (An e).dom
  modulus_eq' : ∀ e, (An' e).modulus = (An e).modulus
  modulus_ne_zero : ∀ e, ((An e).modulus : AlgebraicClosure ℚ) ≠ 0
  param_mul_param : ∀ e, (An' e).param * (An e).param
      = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ((An e).modulus : AlgebraicClosure ℚ)

  mem_dom_iff : ∀ e (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))),
      W ∈ (An e).dom ↔ IsSSCentred p A W (ssValue Γ e)

  param_eq_tieG : ∀ e, ssValue Γ e ≠ 0 → ssValue Γ e ≠ 1728 → (An e).param = tieG p

  modulus_eq : ∀ e, (An e).modulus = ((p : ℕ) : ↥A) ^ jWidth (ssValue Γ e)

  attached_src : ∀ e, (An e).IsAttached (chart Γ (src p e)) (nodeSrc Γ e)

  attached_tgt : ∀ e, (An' e).IsAttached (chart Γ (tgt p e)) (nodeTgt Γ e)

namespace AnnCtx

variable {Γ : ChartCtx p A} (Δ : AnnCtx Γ)

abbrev annIn (e : Fin (mAnnuli p)) : Annulus A ↥(modularFunctionFieldBar (1 * p)) := Δ.An e

abbrev annOut (e : Fin (mAnnuli p)) : Annulus A ↥(modularFunctionFieldBar (1 * p)) := Δ.An' e

theorem twoEnded (e : Fin (mAnnuli p)) :
    (Δ.annOut e).dom = (Δ.annIn e).dom ∧ (Δ.annOut e).modulus = (Δ.annIn e).modulus ∧
      ((Δ.annIn e).modulus : AlgebraicClosure ℚ) ≠ 0 ∧
      (Δ.annOut e).param * (Δ.annIn e).param
        = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ((Δ.annIn e).modulus : AlgebraicClosure ℚ) :=
  ⟨Δ.dom_eq e, Δ.modulus_eq' e, Δ.modulus_ne_zero e, Δ.param_mul_param e⟩

theorem attached (e : Fin (mAnnuli p)) :
    (Δ.annIn e).IsAttached (chart Γ (src p e)) (nodeSrc Γ e) ∧
      (Δ.annOut e).IsAttached (chart Γ (tgt p e)) (nodeTgt Γ e) :=
  ⟨Δ.attached_src e, Δ.attached_tgt e⟩

end AnnCtx

end ModularCurve.MultCovering


