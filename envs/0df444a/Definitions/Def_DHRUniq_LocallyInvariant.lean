-- Prove2me | Definitions.Def_DHRUniq_LocallyInvariant
-- name    : DHRUniq_LocallyInvariant
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:33:35.339124+00:00
-- url     : https://prove2.me/theorems/8d29d6e6-d9a4-476e-848b-cb8a902011e7
-- title:
--   Invariance under isomorphisms of the local spaces
-- statement:
--   A functional $E$ is **invariant under relabeling the local spaces** if for all bijections $e:a\to a'$ and $f:b\to b'$ and every density operator $\varrho$ on $\mathbb C^a\otimes\mathbb C^b$, the value of $E$ on the image of $\varrho$ under the induced unitary identification $\mathbb C^a\otimes\mathbb C^b\cong\mathbb C^{a'}\otimes\mathbb C^{b'}$ equals $E(\varrho)$.
--
--   The paper identifies isomorphic local spaces: in the proof of Lemma 10, $(\varrho^{\otimes m})^{\otimes n}=\varrho^{\otimes mn}$ is an equality "of equivalent density matrices on products of isomorphic local spaces".
--
--   **Formalization Note** In Lean the two sides are matrices over different index types, so the identification must be stated. Lemma 10 alone assumes it.
-- source:
--   Donald, Horodecki, Rudolph, The uniqueness theorem for entanglement measures, arXiv:quant-ph/0105017v2, proof of Lemma 10, p. 10; (E2′′), p. 8

import Mathlib
import Definitions.Def_DHRUniq_BipartiteFunctional
import Definitions.Def_WildeQIT_IsDensityOperator

open WildeQIT (IsDensityOperator)

namespace DHRUniq

/-- **Invariance under relabeling the local spaces.** Donald, Horodecki, Rudolph, *The uniqueness theorem for entanglement measures*, arXiv:quant-ph/0105017v2, proof of Lemma 10, p. 10: "by
definition, `(ϱ^{⊗m})^{⊗n} = ϱ^{⊗mn}` where the equality relates equivalent density matrices on
products of isomorphic local spaces". §5.1, p. 8, also states the standing assumption (E2′′) that a
measure is invariant under strictly local unitaries.

**Formalization Note** The paper identifies isomorphic local spaces, so `E` takes the same value
on a density operator and on its image under bijections of the local bases. In Lean these are
matrices over different index types, so the identification is an explicit predicate. Only Lemma 10
assumes it; for a functional with (P2) it holds on pure states, because a relabeling is LQCC. -/
def LocallyInvariant (E : BipartiteFunctional) : Prop :=
  ∀ ⦃a b a' b' : Type⦄ [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype a'] [DecidableEq a'] [Fintype b'] [DecidableEq b'] (e : a ≃ a') (f : b ≃ b')
    (ρ : Matrix (a × b) (a × b) ℂ), IsDensityOperator ρ →
    E (ρ.submatrix (Prod.map e.symm f.symm) (Prod.map e.symm f.symm)) = E ρ

end DHRUniq


