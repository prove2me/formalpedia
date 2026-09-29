-- Prove2me | Definitions.Def_FreyPackage_LoweringAt
-- name    : FreyPackage_LoweringAt
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/301ccaff-1084-515d-983e-95c5fcf50dc1
-- title:
--   Level-lowering predicates targeting the fixed integral Frey model
-- statement:
--   Three predicates on a Frey package $P$ (a triple $a,b,c$ of nonzero integers with $a^p+b^p=c^p$ for a prime $p\ge 5$, $\gcd(a,b)=1$, $a\equiv 3 \pmod 4$, $b$ even) are defined; each is an implication asserting that a congruence between the mod $p$ representation of the Frey curve and a newform of level divisible by an auxiliary prime can be descended to one of smaller level. They differ from the earlier variants of the same shape only in the conclusion: instead of `ModularRepOfLevel`, which asserts the existence of a level-$N$ normalised weight-two eigenform on $\Gamma_0(N)$, of some integral model $W$ of `P.freyCurve` and of a maximal ideal $\mathfrak m$ of the integral closure of $\mathbb Z$ in $\mathbb C$ containing $p$, with $a_\ell(f)\equiv a_\ell(W) \bmod \mathfrak m$ for all primes $\ell\nmid N$, $\ell\ne p$ of good reduction, the conclusion here is `ModularRepOfLevelAt N`, where the model is pinned down to be the fixed integral Weierstrass model `freyCurveInt P`.
--
--   The hypotheses are unchanged. `MazurPrincipleNewLoweringAt P q` assumes $N>0$, $q$ prime, $q\ne 2$, $q\ne p$, $q\nmid N$, that $p\nmid q^2-1$ (the negation of `ExchangeCongruence`), that the $p$-torsion of the Frey curve over an algebraic closure of $\mathbb Q$ is nontrivial with no proper nonzero Galois-stable $\mathbb Z/p$-submodule, that `freyGaloisRep` kills the inertia subgroups of all valuation subrings lying over $q$, and `ModularRepOfLevelNewAt (N*q) q` (a congruent eigenform $g$ of level $Nq$ with $a_q(g)^2=1$). `ExchangeCaseLoweringAt P q` is the same with $p\mid q^2-1$ assumed instead. `AtPNewLoweringAt P` assumes $N_0>0$, $p\nmid N_0$, the same irreducibility, that $p$ divides the $p$-adic valuation of the discriminant of `P.freyCurve`, and `ModularRepOfLevelNewAt (N₀ * P.p) P.p`, concluding `ModularRepOfLevelAt N₀`. A local decidable-equality instance on $\overline{\mathbb Q}$ is also provided.
--
--   **Relation to Mathlib.** Mathlib supplies cusp forms for $\Gamma_0(N)$, $q$-expansions, Weierstrass curves and valuation-theoretic inertia; the notions of residual modularity, newness at a prime, and level lowering used here are the project's own.
--
--   **Where it is used.** These predicates package the level-lowering steps of the Frey–Serre–Ribet argument in the form in which they are consumed by the descent on the level of the Frey curve's mod $p$ representation: removal of an auxiliary prime $q$ from the level (split into Mazur's principle and the exchange case according to whether $p \mid q^2-1$), and removal of $p$ itself. The `At` versions are the variants whose conclusion refers to the fixed integral model `freyCurveInt P`, so that successive descents can be chained without rechoosing a model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_FreyPackage_LoweringAt.lean

import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FreyPackage_ExchangeCase
import Definitions.Def_GaloisRep_GlobalUnramifiedAt
import Definitions.Def_FreyPackage_GaloisRep
import Definitions.Def_FreyPackage_LevelRaising
import Definitions.Def_RibetLevelLowering_CharacterGroupApparatusV2
import Definitions.Def_WeierstrassCurve_PeuRamifiee
import Definitions.Def_FreyPackage_AtPNewLowering

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine.Point

set_option autoImplicit false

noncomputable section

namespace FreyPackage

noncomputable local instance instDecEqQbarDescentRepoint :
    DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _

def MazurPrincipleNewLoweringAt (P : FreyPackage) (q : ℕ) : Prop :=
  ∀ N : ℕ, 0 < N → q.Prime → q ≠ 2 → q ≠ P.p → ¬ q ∣ N →
    ¬ P.ExchangeCongruence q →
    GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p →
    GlobalGaloisRep.IsUnramifiedAt P.freyGaloisRep q →
    P.ModularRepOfLevelNewAt (N * q) q →
    P.ModularRepOfLevelAt N

def ExchangeCaseLoweringAt (P : FreyPackage) (q : ℕ) : Prop :=
  ∀ N : ℕ, 0 < N → q.Prime → q ≠ 2 → q ≠ P.p → ¬ q ∣ N →
    P.ExchangeCongruence q →
    GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p →
    GlobalGaloisRep.IsUnramifiedAt P.freyGaloisRep q →
    P.ModularRepOfLevelNewAt (N * q) q →
    P.ModularRepOfLevelAt N

def AtPNewLoweringAt (P : FreyPackage) : Prop :=
  ∀ N₀ : ℕ, 0 < N₀ → ¬ P.p ∣ N₀ →
    GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p →
    P.freyCurve.IsPeuRamifieeAt P.p P.p →
    P.ModularRepOfLevelNewAt (N₀ * P.p) P.p →
    P.ModularRepOfLevelAt N₀

end FreyPackage

end


