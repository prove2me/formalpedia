-- Prove2me | Definitions.Def_FreyPackage_LoweringAtUniform
-- name    : FreyPackage_LoweringAtUniform
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/8cc016f6-793f-579c-a33b-76071591f12c
-- title:
--   Uniformly pinned level-lowering predicates for Frey packages
-- statement:
--   Fix a Frey package $P=(a,b,c,p)$, so $a^p+b^p=c^p$ with $abc\neq0$, $\gcd(a,b)=1$, $a\equiv3\pmod 4$, $b\equiv0\pmod 2$ and $p\ge 5$ prime, and let `freyCurveInt P` be the explicit integral Weierstrass model with $a_1=1$, $a_2=(b^p-1-a^p)/4$, $a_3=a_6=0$, $a_4=-a^pb^p/16$.
--
--   The first definition, `ModularRepOfLevelNewAtPinned P M q`, asserts the existence of a cusp form $g$ of weight $2$ on $\Gamma_0(M)$ and a maximal ideal $\mathfrak m$ of the ring $\overline{\mathbb Z}$ of algebraic integers in $\mathbb C$ such that: $g$ is a normalised eigenform in the project's sense (first $q$-coefficient $1$, multiplicativity at coprime indices, and the two Hecke recursions at prime powers according as the prime divides $M$ or not); $\mathfrak m$ contains $p$; for every prime $\ell$ with $\ell\nmid \Delta(\mathtt{freyCurveInt }P)$, $\ell\nmid M$ and $\ell\neq p$ there is an algebraic integer $a$ whose complex value is the $\ell$-th $q$-expansion coefficient of $g$ and with $a-a_\ell\in\mathfrak m$, where $a_\ell=\ell+1-\#(\mathtt{freyCurveInt }P\bmod \ell)(\mathbb F_\ell)$; and $g$ satisfies the project's newness condition at $q$, namely that its $q$-th coefficient squares to $1$. So the congruence is pinned to the one fixed integral model, with no existential quantification over integral models of the Frey curve.
--
--   The remaining three definitions are statement bundles of level-lowering form, each a $\Pi$-type whose conclusion is the pinned condition `ModularRepOfLevelAt N` (the same congruence data at level $N$, without the newness clause). `MazurPrincipleNewLoweringAtUniform P q` says: for all $N>0$ with $q$ prime, $q\neq2$, $q\neq p$, $q\nmid N$, with $p\nmid q^2-1$ (the negation of `ExchangeCongruence`), with the mod-$p$ representation on the $p$-torsion of the Frey curve over $\overline{\mathbb Q}$ irreducible (no Galois-stable $\mathbb Z/p$-submodule other than $0$ and everything, the torsion being nontrivial), and with `freyGaloisRep` unramified at $q$ (inertia at every valuation subring lying over $q$ is in the kernel), a pinned witness at level $Nq$ new at $q$ gives the pinned condition at level $N$. `ExchangeCaseLoweringAtUniform P q` is the same implication with $p\mid q^2-1$ assumed instead. `AtPNewLoweringAtUniform P` treats removal of $p$ itself: for $N_0>0$ with $p\nmid N_0$, irreducibility, and $p\mid v_p(\Delta)$ of the Frey curve over $\mathbb Q$ (the `IsPeuRamifieeAt` condition), a pinned witness at level $N_0p$ new at $p$ gives the pinned condition at level $N_0$. A local classical decidable-equality instance on $\overline{\mathbb Q}$ accompanies the definitions.
--
--   **Relation to Mathlib.** Mathlib supplies the cusp forms, the groups $\Gamma_0(N)$ and $q$-expansions used here, and the integral closure $\overline{\mathbb Z}\subset\mathbb C$; the notions of residual modularity by congruence of Fourier coefficients, of newness (here the condition $a_q^2=1$, not Mathlib's or the classical notion of a newform), and the level-lowering implications are the project's own.
--
--   **Where it is used.** These predicates package the level-lowering inputs of the Frey–Serre–Ribet step: starting from a residual congruence between the Frey curve and an eigenform of level $Nq$ (or $N_0p$) new at the prime to be removed, they conclude the same congruence at the smaller level, the three branches corresponding to Mazur's principle, to the exchange case where $p\mid q^2-1$, and to lowering at $p$ for a curve peu ramifiée at $p$. Iterating them drives the level of the congruence down towards the conductor $2$, which carries no weight-$2$ eigenform.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_FreyPackage_LoweringAtUniform.lean

import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FreyPackage_LevelRaising
import Definitions.Def_RibetLevelLowering_CharacterGroupApparatusV2
import Definitions.Def_GaloisRep_GlobalUnramifiedAt
import Definitions.Def_FreyPackage_GaloisRep
import Definitions.Def_FreyPackage_ExchangeCase
import Definitions.Def_FreyPackage_LoweringAt
import Definitions.Def_FreyPackage_AtPNewLowering
import Definitions.Def_WeierstrassCurve_PeuRamifiee
import Definitions.Def_WeierstrassCurve_Semistability

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine.Point FreyCurve

open scoped CongruenceSubgroup

namespace FreyPackage

noncomputable local instance instDecEqQbarUniformPin :
    DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _

def ModularRepOfLevelNewAtPinned (P : FreyPackage) (M q : ℕ) : Prop :=
  ∃ (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (𝔪 : Ideal (integralClosure ℤ ℂ)),
    g.IsNormalizedEigenform ∧
    𝔪.IsMaximal ∧ (P.p : integralClosure ℤ ℂ) ∈ 𝔪 ∧
    (∀ ℓ : ℕ, ℓ.Prime → (freyCurveInt P).IsGoodPrimeFor ℓ → ¬ ℓ ∣ M → ℓ ≠ P.p →
      ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff g ℓ ∧
        a - (((freyCurveInt P).apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪) ∧
    g.IsNewAt q

def MazurPrincipleNewLoweringAtUniform (P : FreyPackage) (q : ℕ) : Prop :=
  ∀ N : ℕ, 0 < N → q.Prime → q ≠ 2 → q ≠ P.p → ¬ q ∣ N →
    ¬ P.ExchangeCongruence q →
    GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p →
    GlobalGaloisRep.IsUnramifiedAt P.freyGaloisRep q →
    P.ModularRepOfLevelNewAtPinned (N * q) q →
    P.ModularRepOfLevelAt N

def ExchangeCaseLoweringAtUniform (P : FreyPackage) (q : ℕ) : Prop :=
  ∀ N : ℕ, 0 < N → q.Prime → q ≠ 2 → q ≠ P.p → ¬ q ∣ N →
    P.ExchangeCongruence q →
    GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p →
    GlobalGaloisRep.IsUnramifiedAt P.freyGaloisRep q →
    P.ModularRepOfLevelNewAtPinned (N * q) q →
    P.ModularRepOfLevelAt N

def AtPNewLoweringAtUniform (P : FreyPackage) : Prop :=
  ∀ N₀ : ℕ, 0 < N₀ → ¬ P.p ∣ N₀ →
    GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p →
    P.freyCurve.IsPeuRamifieeAt P.p P.p →
    P.ModularRepOfLevelNewAtPinned (N₀ * P.p) P.p →
    P.ModularRepOfLevelAt N₀

end FreyPackage

end


