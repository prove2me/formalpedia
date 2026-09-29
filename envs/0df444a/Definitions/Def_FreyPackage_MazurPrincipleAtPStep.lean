-- Prove2me | Definitions.Def_FreyPackage_MazurPrincipleAtPStep
-- name    : FreyPackage_MazurPrincipleAtPStep
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/e6d07dfd-7db4-5608-b48c-d5e41ec8e4e0
-- title:
--   One-step level lowering at p for Frey packages
-- statement:
--   For a Frey package $P$ — integers $a,b,c$, all non-zero and with $\gcd(a,b)=1$, $a\equiv 3 \pmod 4$, $b\equiv 0 \pmod 2$, and a prime $p\ge 5$ with $a^p+b^p=c^p$ — the abbreviation `MazurPrincipleAtPStep P` is the proposition that the level of the residual representation can be divided by $p$ once. Explicitly, it asserts: for every natural number $M$, if the $p$-torsion Galois module of the Frey curve is irreducible in the sense of `GaloisRepIsIrreducible`, i.e. the $\mathbb{Z}$-torsion submodule killed by $p$ of the points of `P.freyCurve` over $\overline{\mathbb{Q}}$ is non-trivial and its only $\mathbb{Z}/p$-submodules stable under all $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}}$ are $\bot$ and $\top$, and if $M>0$ and $p\nmid M$, then `P.ModularRepOfLevelAt (M * P.p)` implies `P.ModularRepOfLevelAt M`.
--
--   Here `ModularRepOfLevelAt P N` is the project's congruence form of residual modularity, pinned to the canonical integral Weierstrass model `freyCurveInt P`: there exist a weight-$2$ cusp form $f$ on $\Gamma_0(N)$ which is a normalised eigenform (the structure [`CuspForm.IsNormalizedEigenform`](../def/FLTPrelim_Modularity.html#L28), whose fields are $a_1(f)=1$, multiplicativity of the $q$-coefficients at coprime indices, and the two Hecke recursions at prime powers according as the prime divides $N$ or not) and a maximal ideal $\mathfrak{m}$ of the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ containing $p$, such that for every prime $\ell$ with $\ell\nmid\Delta(\mathtt{freyCurveInt } P)$, $\ell\nmid N$ and $\ell\ne p$, the coefficient $a_\ell(f)$ is an algebraic integer congruent to the trace of Frobenius $a_\ell$ of the integral model modulo $\mathfrak{m}$. Thus the conclusion is a congruence of Hecke eigenvalue systems at good primes away from the level, not an isomorphism of representations.
--
--   The statement is shaped differently from Mazur's principle proper: no $p$-newness of the level-$Mp$ witness, and no semistability or peu-ramifiée condition at $p$, is assumed.
--
--   **Relation to Mathlib.** Mathlib supplies the cusp forms on $\Gamma_0(N)$ and the $q$-expansion coefficients used here; the eigenform axioms, the congruence-modularity predicate `ModularRepOfLevelAt` and the irreducibility predicate for the $p$-torsion Galois module are the project's own.
--
--   **Where it is used.** This is one of the level-lowering inputs used to strip the prime $p$ from the level of the residual representation attached to the Frey curve; it yields the $p$-new, peu-ramifiée form of lowering at $p$ (`AtPNewLoweringAtUniform`) by forgetting the newness clause, and feeds the descent of the level towards $2$, where no suitable eigenform exists.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_FreyPackage_MazurPrincipleAtPStep.lean

import Mathlib
import Definitions.Def_FreyPackage_LoweringAtUniform

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine.Point

namespace FreyPackage

abbrev MazurPrincipleAtPStep (P : FreyPackage) : Prop :=
  ∀ M : ℕ,
    GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p →
    0 < M → ¬ P.p ∣ M → P.ModularRepOfLevelAt (M * P.p) →
    P.ModularRepOfLevelAt M

end FreyPackage


