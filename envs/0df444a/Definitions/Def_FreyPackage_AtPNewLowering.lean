-- Prove2me | Definitions.Def_FreyPackage_AtPNewLowering
-- name    : FreyPackage_AtPNewLowering
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/a87632d9-1905-5be3-8279-94db32ea98e2
-- title:
--   At-p level lowering for p-new witnesses: the predicate
-- statement:
--   The module defines a single proposition attached to a Frey package $P$ (integers $a,b,c$, all nonzero, coprime with $a\equiv 3 \pmod 4$, $b\equiv 0\pmod 2$, and a prime $p\ge 5$ with $a^p+b^p=c^p$). [`FreyPackage.AtPNewLowering P`](../def/FreyPackage_AtPNewLowering.html#L18) says: for every $N_0>0$ with $p\nmid N_0$, if
--
--   (i) `GaloisRepIsIrreducible` holds for the Frey curve at $p$ over $\overline{\mathbb{Q}}$ — that is, the $p$-torsion submodule $\mathrm{torsionBy}\,\mathbb{Z}\,E_P(\overline{\mathbb{Q}})\,p$ is nontrivial and every $\mathbb{Z}/p$-submodule stable under the action of $\overline{\mathbb{Q}}\simeq_{\mathbb{Q}}\overline{\mathbb{Q}}$ is $\bot$ or $\top$;
--
--   (ii) `IsPeuRamifieeAt P.p P.p` holds for `P.freyCurve`, which by definition means $p \mid v_p(\Delta)$, the $p$-adic valuation of the discriminant of that particular Weierstrass presentation (a condition on the chosen model, not on a minimal model);
--
--   (iii) `P.ModularRepOfLevelNewAt (N₀ * P.p) P.p` holds: there exist a normalised eigenform $g$ of weight $2$ on $\Gamma_0(N_0p)$, an integral Weierstrass model $W$ of `P.freyCurve` (obtained by a rational variable change), and a maximal ideal $\mathfrak{m}$ of the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ containing $p$, such that for every prime $\ell$ with $\ell\nmid\Delta_W$, $\ell\nmid N_0p$, $\ell\ne p$ the $q$-coefficient $a_\ell(g)$ is an algebraic integer congruent to $a_\ell(W)$ modulo $\mathfrak{m}$, and moreover $a_p(g)^2=1$ (the project's `IsNewAt` condition, an exact equality of complex $q$-coefficients, rather than genuine $p$-newness);
--
--   then `P.ModularRepOfLevel N₀` holds: the same congruence data exist at level $N_0$, for some normalised eigenform of weight $2$ on $\Gamma_0(N_0)$, some integral model of the Frey curve and some maximal ideal above $p$.
--
--   A classical `DecidableEq` instance on $\overline{\mathbb{Q}}$ is provided locally, as the torsion-module constructions require it.
--
--   **Relation to Mathlib.** Mathlib has no notion of level lowering or of residual modularity; these are the project's own predicates, built on Mathlib's `WeierstrassCurve`, the group of affine points and `Submodule.torsionBy`, on `CuspForm` for `CongruenceSubgroup.Gamma0` with its `qExpansion` coefficients, and on `padicValRat` for the peu-ramifiée condition.
--
--   **Where it is used.** This proposition is the form in which level lowering at the prime $p$ itself enters the Frey–Serre–Ribet argument, complementing the lowering statements that remove auxiliary primes $\ell\ne p$: from a $p$-new witness of level $N_0p$ congruent to the Frey curve it produces a witness of level $N_0$, which is what eventually forces a weight-$2$ eigenform of level too small to exist.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_FreyPackage_AtPNewLowering.lean

import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_FreyPackage_LevelRaising
import Definitions.Def_WeierstrassCurve_PeuRamifiee

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open WeierstrassCurve.Affine.Point

namespace FreyPackage

noncomputable local instance instDecEqQbarLedgerStageFour :
    DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _

def AtPNewLowering (P : FreyPackage) : Prop :=
  ∀ N₀ : ℕ, 0 < N₀ → ¬ P.p ∣ N₀ →
    GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p →
    P.freyCurve.IsPeuRamifieeAt P.p P.p →
    P.ModularRepOfLevelNewAt (N₀ * P.p) P.p →
    P.ModularRepOfLevel N₀

end FreyPackage

end


