-- Prove2me | Definitions.Def_FreyPackage_RouteAReversePinSeam
-- name    : FreyPackage_RouteAReversePinSeam
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/1157d5a9-8f8f-5bde-a132-b964631d9f50
-- title:
--   Two residual predicates pinning aℓ​ to the canonical Frey model
-- statement:
--   Two `Prop`-valued predicates on a Frey package $P=(a,b,c,p)$ are introduced; both concern transporting trace-of-Frobenius data from an arbitrary integral Weierstrass model of the Frey curve to the canonical one, `freyCurveInt P`.
--
--   `FreyCurveApOfModelThreeAgreement P` says: for every $W$ over $\mathbb{Z}$ that is an integral model of `P.freyCurve` (i.e. some variable change over $\mathbb{Q}$ carries the Frey curve to $W$ base-changed to $\mathbb{Q}$) and satisfies the project's good-prime condition at $3$, namely $3 \nmid \Delta_W$, one has `W.apOfModel 3 = 0`. Here `apOfModel W q` is $\#\mathbb{Z}/q + 1$ minus the number of points of the affine Weierstrass curve obtained by reducing the coefficients of $W$ modulo $q$ (the point at infinity included). So this is a model-independence statement for $a_3$, pinned to the value $0$.
--
--   `RouteAReversePinBadOnlySeam P` says: whenever $N\in\mathbb{N}$, $f$ is a cusp form of weight $2$ for $\Gamma_0(N)$, $W$ is an integral Weierstrass model over $\mathbb{Z}$ and $\mathfrak{m}$ is an ideal of $\overline{\mathbb{Z}} =$ `integralClosure ℤ ℂ` such that `P.IsCongruentWitness N f W 𝔪` holds — $f$ a normalized eigenform in the project's sense (recursions on its $q$-expansion coefficients), $W$ an integral model of the Frey curve, $\mathfrak{m}$ maximal containing $p$, and $a_\ell(f)$ congruent modulo $\mathfrak{m}$ to `W.apOfModel ℓ` for all primes $\ell \nmid N$, $\ell \neq p$ good for $W$ — then the same congruence holds with $W$ replaced by `freyCurveInt P` at every prime $\ell \nmid N$, $\ell \neq p$ that is good for `freyCurveInt P` but bad for $W$ (i.e. $\ell \mid \Delta_W$). Precisely: there is $a \in \overline{\mathbb{Z}}$ with $a = a_\ell(f)$ in $\mathbb{C}$ and $a - a_\ell(\mathrm{freyCurveInt}\,P) \in \mathfrak{m}$. The predicate is vacuous when $W$ itself is the canonical model.
--
--   **Relation to Mathlib.** Weierstrass curves, their discriminant, variable changes, `CuspForm`, `Gamma0` and the $q$-expansion are Mathlib's; the notions used here to package reduction data — good primes ($p \nmid \Delta$), `apOfModel`, integral models, normalized eigenforms via coefficient recursions, and congruence witnesses in $\overline{\mathbb{Z}}$ — are the project's own, Mathlib having no such notions.
--
--   **Where it is used.** These two predicates isolate the part of the mod-$p$ congruence bookkeeping that is not covered by intrinsic model-independence of $a_\ell$ at good primes: the prime $3$, and the primes that are bad for an auxiliary integral model but good for the canonical Frey model. Downstream modules use them as hypotheses to move an eigenform congruence witness onto `freyCurveInt P`, the form in which the congruence is fed into the level-lowering step for the Frey curve attached to a putative solution of the Fermat equation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_FreyPackage_RouteAReversePinSeam.lean

import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_FreyPackage_LevelRaising
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

set_option maxHeartbeats 600000

open WeierstrassCurve WeierstrassCurve.Affine.Point CuspForm

open scoped CongruenceSubgroup

namespace FreyPackage

def FreyCurveApOfModelThreeAgreement (P : FreyPackage) : Prop :=
  ∀ W : WeierstrassCurve ℤ, W.IsIntegralModelOf P.freyCurve →
    W.IsGoodPrimeFor 3 → W.apOfModel 3 = 0

def RouteAReversePinBadOnlySeam (P : FreyPackage) : Prop :=
  ∀ (N : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (W : WeierstrassCurve ℤ)
    (𝔪 : Ideal (integralClosure ℤ ℂ)), P.IsCongruentWitness N f W 𝔪 →
    ∀ ℓ : ℕ, ℓ.Prime → (freyCurveInt P).IsGoodPrimeFor ℓ → ¬ ℓ ∣ N → ℓ ≠ P.p →
      ¬ W.IsGoodPrimeFor ℓ →
      ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ ∧
        a - (((freyCurveInt P).apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪

end FreyPackage


