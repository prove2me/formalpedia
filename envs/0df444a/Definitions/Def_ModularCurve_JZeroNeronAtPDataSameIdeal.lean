-- Prove2me | Definitions.Def_ModularCurve_JZeroNeronAtPDataSameIdeal
-- name    : ModularCurve_JZeroNeronAtPDataSameIdeal
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/580037d8-1e1e-5883-84db-47df9d12f291
-- title:
--   Néron datum at q with same-ideal level detection
-- statement:
--   Fix $N\ge 1$ and a prime $q$ with $q\nmid N$, and a valuation subring $A$ of $\overline{\mathbb Q}$ lying over $q$ (i.e. $q$ is a non-unit of $A$). The structure [`ModularCurve.JZeroNeronAtPDataSameIdeal`](../def/ModularCurve_JZeroNeronAtPDataSameIdeal.html#L10) extends [`ModularCurve.JZeroNeronAtPData`](../def/ModularCurve_JZeroNeronAtPData.html#L19) — hence carries, verbatim, all the data and axioms of an at-$q$ Néron datum for $J_0(Nq)$: the filtration $\mathrm{toric}\le\mathrm{fin}\le\mathrm{finPart}$ inside the $m$-torsion of `JZero (N*q)` with its compatibilities in $m$, its stability under the Hecke algebra and under the decomposition group at $A$, the inertia clauses, the homomorphism to $J_0(N)\times J_0(N)$ with prescribed kernel and image, the finite Hecke-module $\Phi$ with its specialisation maps and Eisenstein property, the Frobenius and monodromy clauses, the Raynaud clause, the rank pins $\#\mathrm{toric}(m)=m^{\text{toricRank}}$ and $\#\mathrm{fin}(m)=m^{\text{toricRank}+2\,\text{abelianRank}}$, and the detection clause producing `HasLowerLevelTorsion (primesOf (N*q)) 𝔪 (JZero N)` — and adds exactly one further field.
--
--   That field, `fin_heckeTorsion_detects_lowerLevel_sameIdeal`, asserts: assuming the Hecke inputs and the commutation of the Hecke operators at both levels $Nq$ and $N$, for every maximal ideal $\mathfrak m$ of the polynomial Hecke algebra $\mathbb Z[X_\ell:\ell\text{ prime}]$ with $q\in\mathfrak m$ and $X_q\notin\mathfrak m$, if some $x\in\mathrm{fin}(q)$ is $\mathfrak m$-torsion in `JZero (N*q)` (for the Hecke action `heckeModuleBar (N*q)`) and $x\notin\mathrm{toric}(q)$, then the $\mathfrak m$-torsion submodule of `JZero N` (for `heckeModuleBar N`) is non-zero. Compared with the inherited clause this is stronger in its conclusion — non-vanishing of $\mathfrak m$-torsion for the same ideal $\mathfrak m$, rather than existence of an element annihilated by the integers in $\mathfrak m$ and by the good $X_\ell-b$ lying in $\mathfrak m$ — at the price of the extra hypothesis $X_q\notin\mathfrak m$.
--
--   The predicate `HasJZeroNeronAtPDataSameIdeal N q hqN` states that such a structure is inhabited for every valuation subring $A$ of $\overline{\mathbb Q}$ over $q$.
--
--   **Relation to Mathlib.** Mathlib has no Jacobians or Néron models of modular curves; the special-fibre geometry at $q$ is axiomatised here by structure fields, and the Hecke algebra is realised as the polynomial ring $\mathbb Z[X_\ell]$ over the primes. Mathlib supplies the ambient notions used (valuation subrings with their decomposition and inertia subgroups, torsion submodules, Hopf algebras).
--
--   **Where it is used.** This is the form of Mazur's principle datum used for level lowering at the prime $q$ exactly dividing the level: from a non-toric $\mathfrak m$-torsion point in the finite part of $J_0(Nq)[q]$, with $X_q\notin\mathfrak m$, one concludes that the same maximal ideal $\mathfrak m$ supports torsion in $J_0(N)$, i.e. that the residual representation attached to $\mathfrak m$ already arises at level $N$. In the Fermat argument this removes the primes of multiplicative reduction from the level of the representation attached to the Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_JZeroNeronAtPDataSameIdeal.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronAtPData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve

structure JZeroNeronAtPDataSameIdeal (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    extends JZeroNeronAtPData N q hqN A hA where

  fin_heckeTorsion_detects_lowerLevel_sameIdeal :
    HeckeInputsAll (N * q) → HeckeOperatorsCommuteBar (N * q) →
    HeckeInputsAll N → HeckeOperatorsCommuteBar N →
      ∀ 𝔪 : Ideal HeckeAlg, 𝔪.IsMaximal → ((q : ℕ) : HeckeAlg) ∈ 𝔪 → heckeGen ⟨q, Fact.out⟩ ∉ 𝔪 →
        ∀ x ∈ fin q, (letI := heckeModuleBar (N * q); x ∈ heckeTorsion (JZero (N * q)) 𝔪) →
          x ∉ toric q →
            (letI := heckeModuleBar N; heckeTorsion (JZero N) 𝔪 ≠ ⊥)

def HasJZeroNeronAtPDataSameIdeal (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) : Prop :=
  ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q), Nonempty (JZeroNeronAtPDataSameIdeal N q hqN A hA)

end ModularCurve

end


