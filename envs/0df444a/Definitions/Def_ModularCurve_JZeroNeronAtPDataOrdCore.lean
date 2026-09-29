-- Prove2me | Definitions.Def_ModularCurve_JZeroNeronAtPDataOrdCore
-- name    : ModularCurve_JZeroNeronAtPDataOrdCore
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/eba7b28c-e739-5011-9706-ebeb92c094cf
-- title:
--   At-q Néron datum with monodromy inclusion at all levels
-- statement:
--   Fix $N\ge 1$, a prime $q$ with $q\nmid N$, and a valuation subring $A$ of $\overline{\mathbb Q}$ lying over $q$ (i.e. $q$ is a non-unit of $A$); let $I_\lambda =$ `A.inertiaSubgroupIn ℚ` be the associated inertia subgroup of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ and write $J =$ `JZero (N * q)` for the group of points of the modular Jacobian at level $Nq$. The structure `JZeroNeronAtPDataOrdCore` extends `JZeroNeronAtPDataSameIdeal`, hence carries all the data of an at-$q$ Néron datum: three subgroup filtrations $m \mapsto$ `toric m` $\le$ `fin m` $\le$ `finPart m` of the $m$-torsion $J[m]$, each compatible with divisibility by intersection with $J[m]$, stable under the Hecke algebra `HeckeAlg` = $\mathbb Z[T_\ell : \ell]$ and under the decomposition subgroup, with `finPart` containing (and, for $m$ coprime to $q$, equal to) the inertia-invariant $m$-torsion, the cyclotomic action of inertia on `toric m`, the inclusion $\sigma x - x \in$ `toric m` for $m$ coprime to $q$, the homomorphisms `abq` onto the $m$-torsion of $J_0(N)^2$ with kernel `toric m`, the finite Hecke-module $\Phi$ of components with its specialisation maps, Eisenstein-type and Frobenius identities, a Raynaud prolongation clause, the rank formulae $\#$`toric m`$= m^{r}$ and $\#$`fin m`$=m^{r+2a}$, and the two clauses detecting torsion at level $N$ from $\mathfrak m$-torsion in `fin q` outside the toric part.
--
--   The single new field `inertia_sub_mem_fin` asserts Grothendieck's monodromy inclusion at every nonzero level: for all $m \neq 0$, all $\sigma \in I_\lambda$ and all $x \in J[m]$ one has $\sigma\cdot x - x \in$ `fin m`. This is weaker than the inherited clause for $m$ coprime to $q$, where the difference lands in `toric m`, but it holds for $m$ divisible by $q$ as well. The predicate `HasJZeroNeronAtPDataOrdCore N q hqN` asserts that such a datum exists for every valuation subring of $\overline{\mathbb Q}$ lying over $q$.
--
--   **Relation to Mathlib.** Mathlib has no Néron model, component group or toric part of a modular Jacobian; the structure is the project's own axiomatisation of the properties of $J_0(Nq)$ at $q$. The $m$-torsion used is Mathlib's `Submodule.torsionBy ℤ` viewed as an additive subgroup, and the inertia subgroup is built from Mathlib's ramification groups of a valuation subring.
--
--   **Where it is used.** The datum packages the local structure of $J_0(Nq)$ at $q$ that is needed for the level-lowering step removing the prime $q$ from the level, in the form where only the monodromy inclusion into the finite part (at all levels of torsion, $q$-power levels included) is required of consumers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_JZeroNeronAtPDataOrdCore.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronAtPDataSameIdeal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve

structure JZeroNeronAtPDataOrdCore (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    extends JZeroNeronAtPDataSameIdeal N q hqN A hA where

  inertia_sub_mem_fin : ∀ (m : ℕ), m ≠ 0 → ∀ σ ∈ A.inertiaSubgroupIn ℚ,
    ∀ x ∈ jZeroTorsion (N * q) m, σ • x - x ∈ fin m

def HasJZeroNeronAtPDataOrdCore (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) : Prop :=
  ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q), Nonempty (JZeroNeronAtPDataOrdCore N q hqN A hA)

end ModularCurve

end


