-- Prove2me | Definitions.Def_ModularCurve_SSCarrier3
-- name    : ModularCurve_SSCarrier3
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/4628f728-ff90-5a11-aa1f-08c59240033e
-- title:
--   Carrier and residue map at the zeros of j
-- statement:
--   Fix a field $F$ and a positive level $N'$, and work with the project's function field $\mathrm{modularFunctionFieldC}\,F\,N'$ of the modular curve of level $N'$ over $F$, with distinguished element $\mathrm{jGeomGen}\,F\,N'$ (the $q$-expansion $j(q)$ viewed inside that field). The type [`ModularCurve.ssPlaces3 F N'`](../def/ModularCurve_SSCarrier3.html#L11) is the subtype of those places $x$ of this field over $F$ (in the project's sense: a valuation subring containing $F$, proper, with principal ideals) at which $\operatorname{ord}_x(j) > 0$, i.e. the zeros of $j$; [`ModularCurve.SSCarrier3 F N'`](../def/ModularCurve_SSCarrier3.html#L15) is the dependent product $\prod_x x.\mathrm{ResidueField}$ over these places, so an element is a family of residue-field values, one at each zero of $j$.
--
--   Three auxiliary data are attached. For $m : \mathbb{N}$ and such a place $x$, `aPole m x` is the integer $7m\cdot\operatorname{ord}_x(j)/6 + 1$ (integer division, hence $\lfloor 7me/6\rfloor+1$ with $e=\operatorname{ord}_x(j)>0$); `uniformizer x` is an unspecified element of the function field, selected by `Classical.epsilon`, satisfying $\operatorname{ord}_x(\pi)=1$. Finally, `res m φ x` turns a power series $φ$ over $F$ into a residue-field value: if there is some $G$ in the function field whose image in $F((q))$ satisfies $G\cdot(\mathrm{thetaJ}\,F)^m = φ$, where $\mathrm{thetaJ}\,F = q\,\frac{d}{dq} j(q)$, then, for a chosen such witness $G$, the value is the residue of $G\cdot(\mathrm{uniformizer}\,x)^{(\mathrm{aPole}\,m\,x)^{+}}$ in $x.\mathrm{ResidueField}$ whenever this product lies in the valuation subring of $x$; in the two remaining cases (no such factorisation, or the product having a pole at $x$) the value is $0$.
--
--   **Relation to Mathlib.** Places of a function field over a base field, their `ord`, valuation subrings and residue fields are the project's own [`AlgebraicCurve.Place`](../def/AlgebraicCurve_DivisorClassGroup.html#L22) structure; Mathlib contributes the ambient machinery used here (`PowerSeries`, `LaurentSeries`, `HahnSeries.ofPowerSeries`, `IsLocalRing.residue`). Mathlib has no notion corresponding to this carrier or to its residue map.
--
--   **Where it is used.** In characteristic $3$ the only supersingular $j$-invariant is $0$, so the zeros of $j$ on the modular curve are exactly the supersingular places, and `SSCarrier3` serves as the space of residue-field valued functions on that finite set. The normalisation by $(\mathrm{uniformizer}\,x)^{\lfloor 7m e/6\rfloor+1}$ records the largest pole that the factor $G$ of a weight-$2m+2$ expansion may have there, so that `res` detects divisibility by the weight-two Hasse invariant; this is the device used in the mod-$3$ input to the modularity arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_SSCarrier3.lean

import Definitions.Def_ModularCurve_ModPFormFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve

variable (F : Type) [Field F] (N' : ℕ) [NeZero N']

abbrev ssPlaces3 : Type :=
  {x : AlgebraicCurve.Place F ↥(ModularCurve.modularFunctionFieldC F N') //
    0 < x.ord (ModularCurve.jGeomGen F N')}

abbrev SSCarrier3 : Type := (x : ssPlaces3 F N') → x.1.ResidueField

namespace SSCarrier3

variable {F N'}

def aPole (m : ℕ) (x : ssPlaces3 F N') : ℤ :=
  7 * (m : ℤ) * x.1.ord (ModularCurve.jGeomGen F N') / 6 + 1

def uniformizer (x : ssPlaces3 F N') : ↥(ModularCurve.modularFunctionFieldC F N') :=
  Classical.epsilon fun π : ↥(ModularCurve.modularFunctionFieldC F N') => x.1.ord π = 1

open Classical in

def res (m : ℕ) (φ : PowerSeries F) (x : ssPlaces3 F N') : x.1.ResidueField :=
  if h : ∃ G : ↥(ModularCurve.modularFunctionFieldC F N'),
      (G : LaurentSeries F) * ModularCurve.thetaJ F ^ m = HahnSeries.ofPowerSeries ℤ F φ then
    if hm : Classical.choose h * uniformizer x ^ (aPole m x).toNat ∈ x.1.toValuationSubring then
      IsLocalRing.residue x.1.toValuationSubring ⟨_, hm⟩
    else 0
  else 0

end SSCarrier3

end ModularCurve

end


