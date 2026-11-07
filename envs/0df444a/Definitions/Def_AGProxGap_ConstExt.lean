-- Prove2me | Definitions.Def_AGProxGap_ConstExt
-- name    : AGProxGap_ConstExt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:36:42.622293+00:00
-- url     : https://prove2.me/theorems/5eb8afe2-c6bb-4a7b-ae6d-980d1ce92c1d
-- title:
--   A finite constant field extension $K/\mathbb F_q$ with the points $P_i,P_\infty$ on $X_K$
-- statement:
--   Let $F=\mathbb F_q(X)$ and let $P_1,\dots,P_n,P_\infty$ be places of $F$. A **finite constant field extension with the points carried along** consists of:
--   1. a finite field extension $K/\mathbb F_q$;
--   2. a field $K(X)$ with compatible embeddings $\mathbb F_q\to K\to K(X)$ and $\mathbb F_q\to F\to K(X)$;
--   3. $K(X)/K$ is again a function field of one variable with full constant field $K$;
--   4. $K(X)$ is generated over $K$ by $F$, i.e. $K(X)=K\cdot F$;
--   5. places $P_i'$, $P_\infty'$ of $K(X)$ lying over $P_i$, $P_\infty$, each the only place of $K(X)$ over its base place.
--
--   This is the base-changed curve $X_K=X\times_{\mathbb F_q}K$ of §2.3 with "the corresponding points" $P_1,\dots,P_n,P_\infty$ on it. Lemma 3.3 constructs an auxiliary divisor on such an $X_K$.
--
--   **Formalization Note** Over the perfect field $\mathbb F_q$ with full constant field, $F\otimes_{\mathbb F_q}K$ is a field, so clauses 2–4 make $K(X)$ the function field of $X_K$; clause 4 excludes larger function fields over $K$. A rational place has exactly one place above it in a constant field extension, which clause 5 records. Every finite extension $K/\mathbb F_q$ admits such a datum. Lying over is expressed by pulling back valuation rings (`ValuationSubring.comap`).
-- source:
--   Li, Xing, Yuan, Zhu, On Proximity Gaps for One-Point Algebraic Geometric Codes, arXiv:2610.39256 (held version, sha256 d2017986…3b3f), §2.3, p.15; §3, p.17; Lemma 3.3, p.18

import Mathlib
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

universe u v

namespace AGProxGap

/-- **A finite constant field extension with the points carried along** (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), §2.3, p.15: "For
any field extension K/F_q, let X_K = X ×_{F_q} K be the curve obtained by extending the constant
field. Its function field is denoted by K(X) … We retain the notation P_∞, P_1, . . . , P_n for the
corresponding points on X_K"; §3, p.17; Lemma 3.3, p.18: "a finite extension K/F_q").

For a function field `F/F_q` and places `P_1, …, P_n, P_∞`, the datum consists of:
1. a field `K` that is a finite extension of `F_q` (`FiniteDimensional F_q K`);
2. a field `FK` (the function field `K(X)` of `X_K`) with compatible algebra maps
   `F_q → K → FK` and `F_q → F → FK`;
3. `FK/K` is again a function field of one variable with full constant field `K`
   (`IsCurveOver K FK`, `Algebra.EssFiniteType K FK`, `ConstantsAreBase K FK`);
4. `FK` is generated over `K` by the image of `F` (`adjoin_eq_top`), i.e. `FK = K · F`;
5. places `lift i` and `liftInf` of `FK/K` lying over `P_i` and `P_∞` (their valuation rings
   pull back to those of `P_i`, `P_∞`), each the only place of `FK` over its base place.

**Formalization Note** The paper's `K(X)` is the compositum `K · F_q(X)`; clause 4 rules out a
larger function field over `K`, and clause 1 the infinite extensions. Over the perfect field
`F_q` with full constant field, `F ⊗_{F_q} K` is a field and equals `FK`, so `FK` is the
paper's `K(X)`; a rational place of `F` has exactly one place of `FK` over it, which is the
paper's "corresponding point" on `X_K` (clause 5). Every finite extension `K/F_q` admits such a
datum. -/
structure ConstExt {Fq : Type u} {F : Type v} [Field Fq] [Field F] [Algebra Fq F] {n : ℕ}
    (P : Fin n → Place Fq F) (Pinf : Place Fq F) where
  /-- The finite extension `K` of `F_q`. -/
  K : Type u
  /-- The function field `K(X)` of the base-changed curve `X_K`. -/
  FK : Type v
  [instFieldK : Field K]
  [instFieldFK : Field FK]
  [instAlgFqK : Algebra Fq K]
  [instAlgKFK : Algebra K FK]
  [instAlgFFK : Algebra F FK]
  [instAlgFqFK : Algebra Fq FK]
  [instTowerK : IsScalarTower Fq K FK]
  [instTowerF : IsScalarTower Fq F FK]
  [instFinite : FiniteDimensional Fq K]
  [instCurve : IsCurveOver K FK]
  [instEFT : Algebra.EssFiniteType K FK]
  /-- `K` is the full constant field of `K(X)`. -/
  constantsAreBase : ConstantsAreBase K FK
  /-- `K(X)` is generated over `K` by `F_q(X)`. -/
  adjoin_eq_top : IntermediateField.adjoin K (Set.range (algebraMap F FK)) = ⊤
  /-- The point `P_i` on `X_K`. -/
  lift : Fin n → Place K FK
  /-- The point `P_∞` on `X_K`. -/
  liftInf : Place K FK
  lift_comap : ∀ i, (lift i).toValuationSubring.comap (algebraMap F FK) = (P i).toValuationSubring
  liftInf_comap : liftInf.toValuationSubring.comap (algebraMap F FK) = Pinf.toValuationSubring
  lift_unique : ∀ i (Q : Place K FK),
    Q.toValuationSubring.comap (algebraMap F FK) = (P i).toValuationSubring → Q = lift i
  liftInf_unique : ∀ Q : Place K FK,
    Q.toValuationSubring.comap (algebraMap F FK) = Pinf.toValuationSubring → Q = liftInf

attribute [instance] ConstExt.instFieldK ConstExt.instFieldFK ConstExt.instAlgFqK
  ConstExt.instAlgKFK ConstExt.instAlgFFK ConstExt.instAlgFqFK ConstExt.instTowerK
  ConstExt.instTowerF ConstExt.instFinite ConstExt.instCurve ConstExt.instEFT

end AGProxGap


