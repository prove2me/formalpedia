-- Prove2me | Definitions.Def_FreyPackage_LevelRaising
-- name    : FreyPackage_LevelRaising
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/2975dbfe-9a23-5163-8a8a-dd6d59d62fa0
-- title:
--   Level raising for Frey packages: witnesses new at a prime
-- statement:
--   Four items are defined. First, for a weight-$2$ cusp form $g$ on $\Gamma_0(M)$ and a natural number $q$, [`CuspForm.IsNewAt`](../def/FreyPackage_LevelRaising.html#L14) asserts the single equation $a_q(g)^2 = 1$ on the $q$-expansion coefficient $a_q(g)$ (the $q$-th coefficient of the expansion of $g$ with respect to the parameter of width $1$); this is a numerical condition on one coefficient, not the span-theoretic definition of newness, and no relation between $q$ and $M$ is required.
--
--   Second, [`FreyPackage.IsCongruentWitness P N f W 𝔪`](../def/FreyPackage_LevelRaising.html#L24) packages the data used throughout to say that the mod-$p$ representation attached to the Frey curve of a Frey package $P=(a,b,c,p)$ comes from level $N$: $f$ is a normalized Hecke eigenform of weight $2$ on $\Gamma_0(N)$ in the project's coefficient-wise sense ($a_1=1$, multiplicativity at coprime indices, and the two prime-power recursions according as $p \mid N$ or not); $W$ is an integral Weierstrass model of `P.freyCurve`, i.e. some variable change over $\mathbb{Q}$ carries the Frey curve to the base change of $W$; $\mathfrak{m}$ is a maximal ideal of the ring of algebraic integers in $\mathbb{C}$ containing $p$; and for every prime $\ell$ with $\ell \nmid \Delta_W$, $\ell \nmid N$, $\ell \neq p$, the coefficient $a_\ell(f)$ is an algebraic integer congruent modulo $\mathfrak{m}$ to $\#\mathbb{F}_\ell + 1 - \#W_{/\mathbb{F}_\ell}$. This is literally the existential body of `ModularRepOfLevel`, now named. Third, `ModularRepOfLevelNewAt P M q` asserts the existence of such a witness at level $M$ whose form is new at $q$ in the above sense.
--
--   Finally, [`FreyPackage.LevelRaising P N q'`](../def/FreyPackage_LevelRaising.html#L37) is the implication: for all $f$, $W$, $\mathfrak{m}$, if $N>0$, $q'$ is prime with $q' \nmid N$ and $q' \neq p$, the $p$-torsion of the Frey curve over $\overline{\mathbb{Q}}$ is irreducible as a Galois module in the project's sense (nontrivial, with no Galois-stable $\mathbb{Z}/p$-submodules other than $\bot$ and $\top$), $(f,W,\mathfrak{m})$ is a congruent witness at level $N$, and $a_{q'}(f)^2 \equiv (q'+1)^2 \pmod{\mathfrak{m}}$, then `ModularRepOfLevelNewAt P (N*q') q'` holds.
--
--   **Relation to Mathlib.** Mathlib supplies `CuspForm`, the groups $\Gamma_0(N)$ and the $q$-expansion machinery, together with Weierstrass curves and the integral closure of $\mathbb{Z}$ in $\mathbb{C}$; newness, congruent witnesses and the level-raising property are the project's own notions, as are the normalized-eigenform and integral-model predicates they use. A local `DecidableEq (AlgebraicClosure ℚ)` instance is obtained from classical choice, as required by the project's Galois-module irreducibility predicate.
--
--   **Where it is used.** `LevelRaising` is the hypothesis form of Ribet's level-raising theorem as it is needed for the Frey curve: it allows a prime $q'$ satisfying the congruence $a_{q'}^2 \equiv (q'+1)^2$ to be inserted into the level, producing a witness new at $q'$. It is used alongside `ModularRepOfLevel` in the level-lowering step which contradicts the existence of a Frey package.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_FreyPackage_LevelRaising.lean

import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Definitions.Def_FLTPrelim_ModularRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine.Point

open scoped CongruenceSubgroup

namespace CuspForm

def IsNewAt {M : ℕ} (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (q : ℕ) : Prop :=
  ModularFormClass.qCoeff g q ^ 2 = 1

end CuspForm

namespace FreyPackage

noncomputable local instance instDecEqQbarLevelRaising :
    DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _

def IsCongruentWitness (P : FreyPackage) (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (W : WeierstrassCurve ℤ)
    (𝔪 : Ideal (integralClosure ℤ ℂ)) : Prop :=
  f.IsNormalizedEigenform ∧ W.IsIntegralModelOf P.freyCurve ∧
    𝔪.IsMaximal ∧ (P.p : integralClosure ℤ ℂ) ∈ 𝔪 ∧
    ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ N → ℓ ≠ P.p →
      ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ ∧
        a - ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪

def ModularRepOfLevelNewAt (P : FreyPackage) (M q : ℕ) : Prop :=
  ∃ (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (W : WeierstrassCurve ℤ)
    (𝔪 : Ideal (integralClosure ℤ ℂ)), P.IsCongruentWitness M g W 𝔪 ∧ g.IsNewAt q

def LevelRaising (P : FreyPackage) (N q' : ℕ) : Prop :=
  ∀ (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (W : WeierstrassCurve ℤ)
    (𝔪 : Ideal (integralClosure ℤ ℂ)),
    0 < N → q'.Prime → ¬ q' ∣ N → q' ≠ P.p →
    GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p →
    P.IsCongruentWitness N f W 𝔪 →
    (∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f q' ∧
      a ^ 2 - ((q' : integralClosure ℤ ℂ) + 1) ^ 2 ∈ 𝔪) →
    P.ModularRepOfLevelNewAt (N * q') q'

end FreyPackage


