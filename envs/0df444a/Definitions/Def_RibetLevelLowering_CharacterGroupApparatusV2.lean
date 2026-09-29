-- Prove2me | Definitions.Def_RibetLevelLowering_CharacterGroupApparatusV2
-- name    : RibetLevelLowering_CharacterGroupApparatusV2
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/501ffa81-717d-56ac-bb84-d4955be96e72
-- title:
--   Character-group apparatus hypotheses for Ribet level lowering
-- statement:
--   Three predicates on a Frey package $P$ (with prime exponent $p\ge 5$), plus a variant of the residual modularity predicate pinned to a fixed integral model.
--
--   `ModularRepOfLevelAt P N` asserts the existence of a weight-$2$ cusp form $f$ for $\Gamma_0(N)$ and a maximal ideal $\mathfrak m$ of the integral closure of $\mathbb Z$ in $\mathbb C$ such that $f$ is a normalised eigenform (normalised first $q$-coefficient, multiplicativity on coprime indices, and the two Hecke recursions at prime powers according as the prime divides $N$ or not), $p\in\mathfrak m$, and for every prime $\ell$ with $\ell\nmid\Delta(\mathtt{freyCurveInt}\,P)$, $\ell\nmid N$, $\ell\ne p$, there is an algebraic integer $a$ with $a=a_\ell(f)$ in $\mathbb C$ and $a\equiv \#\mathbb F_\ell+1-\#(\mathtt{freyCurveInt}\,P\bmod\ell)\pmod{\mathfrak m}$. This differs from `ModularRepOfLevel` in that the integral Weierstrass model is the explicit Frey model `freyCurveInt P` rather than an existentially quantified integral model of `P.freyCurve`.
--
--   `CharacterGroupApparatus P q` asserts: for all $N>0$ and all primes $q,q'$ with $q'\ne q$ and $q,q'\nmid N$, if $P$ is residually modular of level $Nqq'$ by a form that is new at $q'$ in the sense $a_{q'}^2=1$, then there are a field $k$ and an exchange datum $d$ over $k$ — finite-dimensional $k$-spaces $X_p,Y_q,L_p,Y_p,L_q$, maps $f:Y_q\to L_p$, $g:L_p\to X_p$ with $g$ surjective and $\ker g\subseteq\operatorname{im}f$, and integers $\lambda>0,\mu$ with $\dim Y_p=2\mu$, $\dim L_p=2\lambda$, $\dim Y_q,\dim X_p\le\mu$, $\dim L_q\le\lambda$ — such that failure of residual modularity at level $Nq'$ implies $\dim Y_p=\dim L_q$. The existential quantifier precedes this implication. `CharacterGroupApparatusAt` is the same with `ModularRepOfLevelAt` as the trigger, and `CharacterGroupApparatusAtFamily P` asserts it for every $q$. Primality of $q$ sits inside the binders, so the predicates hold vacuously at non-prime $q$.
--
--   **Relation to Mathlib.** Mathlib supplies the ambient notions used (cusp forms for $\Gamma_0(N)$, $q$-expansion coefficients, `integralClosure`, finite-dimensional modules and `Module.finrank`); the residual-modularity predicates, the exchange datum and the character-group apparatus hypotheses are the project's own.
--
--   **Where it is used.** These hypotheses package the conclusion of Ribet's character-group analysis on Shimura curves in a form consumable by the exchange case of level lowering: combined with a datum for which the rank equality fails, the apparatus forces the non-modularity trigger to fail, i.e. the residual representation of the Frey curve is modular of the smaller level $Nq'$, so the prime $q$ has been removed from the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_RibetLevelLowering_CharacterGroupApparatusV2.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_FreyPackage_LevelRaising
import Definitions.Def_RibetLevelLowering_ExchangeData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve CuspForm
open scoped CongruenceSubgroup

namespace FreyPackage

def ModularRepOfLevelAt (P : FreyPackage) (N : ℕ) : Prop :=
  ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (𝔪 : Ideal (integralClosure ℤ ℂ)),
    f.IsNormalizedEigenform ∧
    𝔪.IsMaximal ∧ (P.p : integralClosure ℤ ℂ) ∈ 𝔪 ∧
    ∀ ℓ : ℕ, ℓ.Prime → (freyCurveInt P).IsGoodPrimeFor ℓ → ¬ ℓ ∣ N → ℓ ≠ P.p →
      ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ ∧
        a - (((freyCurveInt P).apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪

def CharacterGroupApparatus (P : FreyPackage) (q : ℕ) : Prop :=
  ∀ N q' : ℕ, 0 < N → q.Prime → q'.Prime → q' ≠ q → ¬ q' ∣ N → ¬ q ∣ N →
    P.ModularRepOfLevelNewAt (N * q * q') q' →
    ∃ (k : Type) (hk : Field k) (d : @RibetEndgame.ExchangeData k hk),
      ¬ P.ModularRepOfLevel (N * q') → @RibetEndgame.ExchangeData.SeqIso k hk d

def CharacterGroupApparatusAt (P : FreyPackage) (q : ℕ) : Prop :=
  ∀ N q' : ℕ, 0 < N → q.Prime → q'.Prime → q' ≠ q → ¬ q' ∣ N → ¬ q ∣ N →
    P.ModularRepOfLevelNewAt (N * q * q') q' →
    ∃ (k : Type) (hk : Field k) (d : @RibetEndgame.ExchangeData k hk),
      ¬ P.ModularRepOfLevelAt (N * q') → @RibetEndgame.ExchangeData.SeqIso k hk d

def CharacterGroupApparatusAtFamily (P : FreyPackage) : Prop :=
  ∀ q : ℕ, P.CharacterGroupApparatusAt q

end FreyPackage


