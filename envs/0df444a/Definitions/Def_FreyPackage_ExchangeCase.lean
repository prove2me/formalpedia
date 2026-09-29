-- Prove2me | Definitions.Def_FreyPackage_ExchangeCase
-- name    : FreyPackage_ExchangeCase
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/3c2b23e1-5f47-58e0-93bb-ff81215d5b8e
-- title:
--   Exchange-case and Mazur-principle level-lowering predicates at q
-- statement:
--   Fix a Frey package $P$ (integers $a,b,c$ with $a^p+b^p=c^p$, $\gcd(a,b)=1$, $a\equiv 3 \bmod 4$, $b$ even, $p\ge 5$ prime) and a natural number $q$. The predicate [`FreyPackage.ExchangeCongruence P q`](../def/FreyPackage_ExchangeCase.html#L21) is the integer divisibility $p \mid q^2-1$; it is decidable, divisibility of integers being decidable.
--
--   The other two declarations are the two halves of a case split, each a statement about $P$ and $q$ that is to be assumed or proved as a whole. Both `ExchangeCaseLowering P q` and `MazurPrincipleNewLowering P q` assert: for every $N>0$ with $q$ prime, $q\neq 2$, $q\neq p$ and $q\nmid N$, assuming respectively that $p \mid q^2-1$ (exchange case) or that $p \nmid q^2-1$ (Mazur case), that the $p$-torsion of the Frey curve over an algebraic closure of $\mathbb{Q}$ is nontrivial and has no Galois-stable $\mathbb{Z}/p$-submodules besides $\bot$ and $\top$, and that the representation `P.freyGaloisRep` (the Galois action on that $p$-torsion) is unramified at $q$ in the sense that for every valuation subring $A$ of the algebraic closure in which $q$ is a non-unit the inertia subgroup of $A$ over $\mathbb{Q}$ lies in the kernel, one has: if `P.ModularRepOfLevelNewAt (N*q) q` holds then `P.ModularRepOfLevel N` holds.
--
--   Here `ModularRepOfLevel N` means that there exist a weight-$2$ cusp form $f$ on $\Gamma_0(N)$ which is a normalized eigenform (normalisation and Hecke recursions imposed on its $q$-expansion coefficients), an integral Weierstrass model $W$ of the Frey curve, and a maximal ideal $\mathfrak{m}$ of the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ containing $p$, such that for all primes $\ell$ of good reduction for $W$ with $\ell \nmid N$, $\ell \neq p$, the coefficient $a_\ell(f)$ is integral and congruent to $a_\ell(W)$ modulo $\mathfrak{m}$. The variant `ModularRepOfLevelNewAt M q` requires the same congruence data at level $M$ together with the newness condition $a_q(g)^2=1$. Thus the conclusion is a congruence between a form of level $N$ and the Frey curve, not an isomorphism of representations.
--
--   **Relation to Mathlib.** Mathlib supplies the weight-$2$ cusp forms on $\Gamma_0(N)$, $q$-expansions, Weierstrass curves and valuation-theoretic inertia subgroups used here; the notions of normalized eigenform, of a mod-$p$ congruence between a form and an integral model, of newness at $q$ and of these level-lowering statements are the project's own.
--
--   **Where it is used.** The two predicates supply the complementary branches of the case split used to strip an odd prime $q\nmid N$ from the level $N\cdot q$ after newform descent, in the Frey–Serre–Ribet part of the argument: the branch with $p \mid q^2-1$ is the exchange case, the branch with $p \nmid q^2-1$ is the one handled by Mazur's principle. Together they cover all odd $q\neq p$, so a level-lowering statement at $q$ follows from the two of them.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_FreyPackage_ExchangeCase.lean

import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FreyPackage_GaloisRep
import Definitions.Def_FreyPackage_LevelRaising
import Definitions.Def_GaloisRep_GlobalUnramifiedAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine.Point

open scoped CongruenceSubgroup

namespace FreyPackage

noncomputable local instance instDecEqQbarExchangeCase :
    DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _

def ExchangeCongruence (P : FreyPackage) (q : ℕ) : Prop :=
  (P.p : ℤ) ∣ (q : ℤ) ^ 2 - 1

instance (P : FreyPackage) (q : ℕ) : Decidable (P.ExchangeCongruence q) :=
  Int.decidableDvd _ _

def ExchangeCaseLowering (P : FreyPackage) (q : ℕ) : Prop :=
  ∀ N : ℕ, 0 < N → q.Prime → q ≠ 2 → q ≠ P.p → ¬ q ∣ N →
    P.ExchangeCongruence q →
    GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p →
    GlobalGaloisRep.IsUnramifiedAt P.freyGaloisRep q →
    P.ModularRepOfLevelNewAt (N * q) q →
    P.ModularRepOfLevel N

def MazurPrincipleNewLowering (P : FreyPackage) (q : ℕ) : Prop :=
  ∀ N : ℕ, 0 < N → q.Prime → q ≠ 2 → q ≠ P.p → ¬ q ∣ N →
    ¬ P.ExchangeCongruence q →
    GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p →
    GlobalGaloisRep.IsUnramifiedAt P.freyGaloisRep q →
    P.ModularRepOfLevelNewAt (N * q) q →
    P.ModularRepOfLevel N

end FreyPackage


