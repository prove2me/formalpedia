-- Prove2me | Definitions.Def_ModularCurve_JZeroToricTorsion
-- name    : ModularCurve_JZeroToricTorsion
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/e49d47df-33a1-59d0-ba40-c8df4edd3b9c
-- title:
--   Intrinsic toric torsion in `JZero p` at a place
-- statement:
--   Fix a prime $p$, a valuation subring $A$ of $\overline{\mathbb Q}$ (no hypothesis relates $A$ to $p$ here), and a natural number $m$. The definition [`ModularCurve.jZeroToricTorsion p A m`](../def/ModularCurve_JZeroToricTorsion.html#L11) is the additive subgroup of `JZero p` obtained as the intersection of two subgroups. The first is `jZeroTorsion p m`, the $m$-torsion $\{x : m\cdot x = 0\}$ of `JZero p`, i.e. the $\mathbb Z$-torsion submodule `Submodule.torsionBy ℤ (JZero p) (m : ℤ)` read as an additive subgroup. The second is the image of `inertiaInvariantPoints p A` under multiplication by $n :=$ `eisensteinNumerator p` $= (p-1)/\gcd(p-1,12)$, the numerator of $(p-1)/12$; here `inertiaInvariantPoints p A` is the subgroup of those $x \in$ `JZero p` with $\sigma\cdot x = x$ for every $\sigma$ in `A.inertiaSubgroupIn ℚ`, the image in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $A$. Thus, writing $V =$ `JZero p` with its Galois action,
--   $$\mathrm{jZeroToricTorsion}\,p\,A\,m \;=\; V[m] \cap n\,V^{I_A}.$$
--   The accompanying lemma `mem_jZeroToricTorsion` records the membership criterion in exactly this unfolded form: $x$ lies in the subgroup if and only if $m\cdot x = 0$ and there exists an inertia-invariant $y$ with $n\cdot y = x$. No relation between $m$ and $p$, and no coprimality or Néron-model input, is imposed in the definition; the intended reading as the $m$-torsion of the identity component of the Néron model of $J_0(p)$ is a matter of the theorems proved about it elsewhere.
--
--   **Relation to Mathlib.** Mathlib has no notion of the Néron model of $J_0(p)$ or of its toric part; this subgroup is the project's own, assembled from Mathlib's `Submodule.torsionBy`, `AddSubgroup.map` and `nsmulAddMonoidHom` applied to the project's group `JZero p` and to the project's notions `inertiaInvariantPoints` and `eisensteinNumerator`.
--
--   **Where it is used.** The subgroup is a presentation of the toric $m$-torsion of $J_0(p)$ that is defined directly from the Galois action on `JZero p` and the integer $(p-1)/\gcd(p-1,12)$, rather than as the field `toric` of a `JZeroNeronDataPrime` structure; it is therefore available in arguments about $p$-torsion of $J_0(p)$ that do not presuppose the existence of a Néron datum at $p$. Such arguments feed the level-lowering step of the Frey–Serre–Ribet route to Fermat's Last Theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_JZeroToricTorsion.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronDataPrime
import Definitions.Def_ModularCurve_ModularUnit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve

def jZeroToricTorsion (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (m : ℕ) :
    AddSubgroup (JZero p) :=
  jZeroTorsion p m ⊓ (inertiaInvariantPoints p A).map (nsmulAddMonoidHom (eisensteinNumerator p))

theorem mem_jZeroToricTorsion {p : ℕ} [Fact p.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {m : ℕ} {x : JZero p} :
    x ∈ jZeroToricTorsion p A m ↔
      x ∈ jZeroTorsion p m ∧
      ∃ y ∈ inertiaInvariantPoints p A, eisensteinNumerator p • y = x := by
  simp only [jZeroToricTorsion, AddSubgroup.mem_inf, AddSubgroup.mem_map,
    nsmulAddMonoidHom_apply]

end ModularCurve

end


