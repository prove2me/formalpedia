-- Prove2me | Definitions.Def_ModularCurve_JHNodeDepthInf
-- name    : ModularCurve_JHNodeDepthInf
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/54ca43fb-d08c-52b0-8f33-f516ae0f4b74
-- title:
--   Annulus depth law with flipped parameter, ΓH​ level
-- statement:
--   Context: a prime $p$, a level $M$ divisible by $p$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and a valuation subring $A$ of an algebraic closure of $\mathbb{Q}$ whose residue field $\kappa$ is algebraically closed of characteristic $p$; write $F_M$ for the geometric function field `xHFunctionFieldBar M H`, $F_{M/p}$ for the one at level $M/p$ with the subgroup [`ModularCurve.infSubgroup p M H hpM`](../def/ModularCurve_XHDifferentialsModL.html#L246), and $\bar F$ for the characteristic-$p$ function field `JHNeronObjectAtP.Fbar p M H hpM κ`.
--
--   The single declaration `AnnulusDepthLawInf` is a predicate on the data: a place specialisation $P$ (a structure packaging a map $\mathrm{sp}$ from places of $F_{M/p}$ over $\overline{\mathbb{Q}}$ to places of $\bar F$ over $\kappa$, a map on degree-zero divisor class groups, and compatibility axioms for divisors of $q$-expansions, surjectivity, inertia-invariance, Frobenius and $\mathrm{Pic}^0$); an integral $\overline{\mathbb{Q}}$-algebra map $\alpha : F_{M/p} \to F_M$; a pair $s$ of places of $\bar F$ over $\kappa$; an annulus `An` for $A$ in $F_M$, with parameter $z =$ `An.param` and modulus $\pi =$ `An.modulus`, an element of the maximal ideal of $A$; and a function $\mathrm{depth}$ from places of $F_M$ over $\overline{\mathbb{Q}}$ to $\mathbb{N}$.
--
--   It asserts: for every place $V$ of $F_M$ over $\overline{\mathbb{Q}}$ whose first reading $P.\mathrm{reduceFst}\,\alpha\,h\alpha\,V$ (namely $\mathrm{sp}$ of the restriction of $V$ along $\alpha$) equals $s_1$, and which is fixed by the arithmetic Galois action of every $\sigma$ in the inertia subgroup of $A$ over $\mathbb{Q}$, the $A$-valuation of the value at $V$ of $\pi \cdot z^{-1}$ equals the $A$-valuation of $p$ raised to the power $\mathrm{depth}(V)$. Thus it is the analogue of `AnnulusDepthLaw` with the annulus parameter $z$ replaced by the flipped parameter $\pi/z$, i.e. the depth measured from the opposite end of the annulus.
--
--   **Relation to Mathlib.** Places, annuli, prolongations, place specialisations and the $\Gamma_H$ function fields are project notions; from Mathlib come only the valuation on a `ValuationSubring`, the Galois-theoretic machinery and the ambient field theory (the inertia subgroup used here is the project's [`ValuationSubring.inertiaSubgroupIn`](../def/FLTPrelim_Ramification.html#L21), built from Mathlib's inertia subgroup of a valuation subring).
--
--   **Where it is used.** The depth functions governed by such laws enter the description, in the style of Raynaud, of the component group of the Néron model of the Jacobian of $X_H(M)$ at $p$ via the widths of the annuli of the semistable model; that description is what the level-lowering step at $p$ uses.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_JHNodeDepthInf.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNodeDepth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups

namespace ModularCurve
namespace JHPlaceSpecialization

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
variable {A : ValuationSubring (AlgebraicClosure ℚ)}
variable [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)]

def AnnulusDepthLawInf (P : JHPlaceSpecialization p M H hpM A)
    (α : ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)) (hα : α.IsIntegral)
    (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (An : AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H))
    (depth : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → ℕ) : Prop :=
  ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), P.reduceFst α hα V = s.1 →
    (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • V = V) →
    A.valuation (V.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An.modulus : ↥A) : AlgebraicClosure ℚ)) * An.param⁻¹)) =
      A.valuation ((p : ℕ) : AlgebraicClosure ℚ) ^ depth V

end JHPlaceSpecialization
end ModularCurve

end


