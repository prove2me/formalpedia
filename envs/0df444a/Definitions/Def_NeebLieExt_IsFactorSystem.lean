-- Prove2me | Definitions.Def_NeebLieExt_IsFactorSystem
-- name    : NeebLieExt_IsFactorSystem
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:18:05.177703+00:00
-- url     : https://prove2.me/theorems/f72a8d58-f881-4a69-b234-9046568974a5
-- title:
--   Continuous outer actions, continuous factor systems $Z^2(\mathfrak g,\mathfrak n)$, and $Z^2(\mathfrak g,\mathfrak n)_S$
-- statement:
--   1. A **continuous outer action** of $\mathfrak g$ on $\mathfrak n$ is a linear map $S\colon\mathfrak g\to\operatorname{der}\mathfrak n$ with $(x,m)\mapsto S(x).m$ continuous on $\mathfrak g\times\mathfrak n$, for which there exists $\omega\in C^2(\mathfrak g,\mathfrak n)$ with $R_S=\operatorname{ad}\circ\omega$.
--   2. A pair $(S,\omega)$ is a **continuous factor system** for $(\mathfrak g,\mathfrak n)$ if $(x,m)\mapsto S(x).m$ is continuous, $\omega\in C^2(\mathfrak g,\mathfrak n)$, $R_S=\operatorname{ad}\circ\omega$ and $d_S\omega=0$. The set of continuous factor systems is $Z^2(\mathfrak g,\mathfrak n)$.
--   3. For a continuous outer action $S$,
--   $$
--   Z^2(\mathfrak g,\mathfrak n)_S:=\{\omega\in C^2(\mathfrak g,\mathfrak n):\ R_S=\operatorname{ad}\circ\omega,\ d_S\omega=0\}.
--   $$
--
--   Continuous factor systems are the data from which every topologically split extension of $\mathfrak g$ by $\mathfrak n$ is rebuilt as a twisted product $\mathfrak n\times_{(S,\omega)}\mathfrak g$.
-- source:
--   Neeb, Non-abelian extensions of topological Lie algebras, arXiv:math/0411256v1, Definition II.2, p. 11

import Mathlib
import Definitions.Def_NeebLieExt_IsCochain2
import Definitions.Def_NeebLieExt_IsContDerAction
import Definitions.Def_NeebLieExt_curv
import Definitions.Def_NeebLieExt_dS1

namespace NeebLieExt

/-- **Continuous factor systems** `Z²(g, n)`. Neeb, arXiv:math/0411256v1, Definition II.2, p. 11:
"A continuous outer action of g on n is a linear map S: g → der n for which the bilinear map
g × n → n, (x, n) ↦ S(x).n is continuous, i.e., S ∈ C¹_c(g, der n), and there exists a continuous
alternating map ω with R_S = ad ∘ ω. If, in addition, d_S ω = 0 (cf. Lemma I.4), then we call the
pair (S, ω) a continuous factor system for (g, n)."

`IsFactorSystem S ω` says: `(x, m) ↦ S(x).m` is jointly continuous, `ω ∈ C²(g, n)` (continuous,
bilinear, alternating), `R_S = ad ∘ ω`, and `d_S ω = 0`. -/
def IsFactorSystem {K g n : Type*} [CommRing K] [LieRing g] [LieAlgebra K g] [LieRing n]
    [LieAlgebra K n] [TopologicalSpace g] [TopologicalSpace n]
    (S : g →ₗ[K] LieDerivation K n n) (ω : g → g → n) : Prop :=
  IsContDerAction S ∧ IsCochain2 K ω ∧ CurvEqAd S ω ∧ ∀ x y z, dS2 S ω x y z = 0

/-- **Continuous outer actions**. Neeb, arXiv:math/0411256v1, Definition II.2, p. 11 (first
sentence): `S ∈ C¹_c(g, der n)` and there is `ω ∈ C²(g, n)` with `R_S = ad ∘ ω`.

**Formalization Note** Companion of `IsFactorSystem`. -/
def IsContOuterAction {K g n : Type*} [CommRing K] [LieRing g] [LieAlgebra K g] [LieRing n]
    [LieAlgebra K n] [TopologicalSpace g] [TopologicalSpace n]
    (S : g →ₗ[K] LieDerivation K n n) : Prop :=
  IsContDerAction S ∧ ∃ ω : g → g → n, IsCochain2 K ω ∧ CurvEqAd S ω

/-- **The fibre `Z²(g, n)_S`**. Neeb, arXiv:math/0411256v1, Definition II.2, p. 11:
"Z²(g, n)_S := {ω ∈ C²(g, n): R_S = ad ∘ ω, d_S ω = 0}."

**Formalization Note** Companion of `IsFactorSystem`. -/
def InZ2S {K g n : Type*} [CommRing K] [LieRing g] [LieAlgebra K g] [LieRing n]
    [LieAlgebra K n] [TopologicalSpace g] [TopologicalSpace n]
    (S : g →ₗ[K] LieDerivation K n n) (ω : g → g → n) : Prop :=
  IsCochain2 K ω ∧ CurvEqAd S ω ∧ ∀ x y z, dS2 S ω x y z = 0

end NeebLieExt


