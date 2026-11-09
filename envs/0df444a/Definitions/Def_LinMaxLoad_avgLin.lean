-- Prove2me | Definitions.Def_LinMaxLoad_avgLin
-- name    : LinMaxLoad_avgLin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:34:05.33365+00:00
-- url     : https://prove2.me/theorems/0422ff01-b7d9-4a81-b2e6-4c2567e17148
-- title:
--   Expectation over a uniformly random linear map $h : E \to K^r$
-- statement:
--   Let $K$ be a finite field, $E$ a finite-dimensional (hence finite) vector space over $K$, and $r \ge 0$. A **uniformly random linear map** $h : E \to K^r$ is a $K$-linear map drawn uniformly from the finite set $\mathrm{Hom}_K(E, K^r)$ of **all** linear maps, surjective or not; for $E = K^u$ these are exactly the $r \times u$ matrices. For a real-valued function $X$ of linear maps, its expectation is the uniform average
--
--   $$
--   \mathbb E_h[X(h)] = \frac{1}{|\mathrm{Hom}_K(E, K^r)|} \sum_{h \in \mathrm{Hom}_K(E, K^r)} X(h).
--   $$
--
--   Every probability and expectation in the mission (Definition 2, Lemma 1, Theorem 7, Lemma 7, Theorem 17) is taken with respect to this distribution.
--
--   **Formalization Note** The module also records two instances: the set of linear maps $E \to K^r$ is finite, and the quotient $E/V$ of a finite module by a submodule is finite (so the same average makes sense for maps $E/V \to K^{r}$). The denominator is at least $1$ because the zero map exists.
-- source:
--   Kumar–Zuckerman, Linear Max Load and Additive Structure, STOC 2027 submission (manuscript sha256 9dfdbfff…163b056d), Definition 2, p.3; Lemma 1 and Theorem 7, p.8; Lemma 7, p.21 ("uniformly random linear map")

import Mathlib

namespace LinMaxLoad

/-- The space of linear maps from a finite module to `K^r` over a finite field is finite. -/
instance finite_linearMap_finTarget (K E : Type*) [Field K] [Finite K] [AddCommGroup E]
    [Module K E] [Finite E] (r : ℕ) : Finite (E →ₗ[K] (Fin r → K)) :=
  Finite.of_injective (fun f : E →ₗ[K] (Fin r → K) => (f : E → Fin r → K))
    DFunLike.coe_injective

/-- The quotient of a finite module by a submodule is finite. -/
instance finite_submoduleQuotient {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    [Finite E] (V : Submodule K E) : Finite (E ⧸ V) :=
  Finite.of_surjective _ V.mkQ_surjective

/-- **Expectation over a uniformly random linear map** `h : E → K^r` (the "uniformly random
linear map" of Definition 2, p.3, Lemma 1 and Theorem 7, p.8, and Lemma 7, p.21, of
Kumar–Zuckerman, *Linear Max Load and Additive Structure*, STOC 2027 submission manuscript
(sha256 9dfdbfffae232e07951f18360ca77987748ff477822893e9f447422f163b056d)).
For a finite field `K`, a finite `K`-module `E` and `X` a real function of linear maps,
`avgLin K E r X = (1 / #{linear maps E → K^r}) · ∑_h X h`, the uniform average over **all**
`K`-linear maps `E →ₗ[K] (Fin r → K)` (surjective or not; for `E = K^u` these are the
`r × u` matrices).

**Formalization Note** The set of linear maps is finite (instance above), and the average
divides by its cardinality, which is at least 1 (the zero map). -/
noncomputable def avgLin (K E : Type*) [Field K] [Fintype K] [AddCommGroup E] [Module K E]
    [Finite E] (r : ℕ) (X : (E →ₗ[K] (Fin r → K)) → ℝ) : ℝ :=
  haveI : Fintype (E →ₗ[K] (Fin r → K)) := Fintype.ofFinite _
  (∑ h, X h) / (Fintype.card (E →ₗ[K] (Fin r → K)) : ℝ)

end LinMaxLoad


