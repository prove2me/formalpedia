-- Prove2me | Definitions.Def_AGProxGap_Supplement_ClosureExt
-- name    : AGProxGap_Supplement_ClosureExt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:16:54.043139+00:00
-- url     : https://prove2.me/theorems/e2226109-3cbc-4e7c-b2e8-72a506f3639c
-- title:
--   Base change to the algebraic closure $\overline{\mathbb F}_q$
-- statement:
--   For a function field $F=\mathbb F_q(X)$ and rational places $P_1,\dots,P_n,P_\infty$, the datum consists of an algebraic closure $K=\overline{\mathbb F}_q$ of $\mathbb F_q$, the function field $\overline{\mathbb F}_q(X)=K\cdot F$ of the base-changed curve $X_{\overline{\mathbb F}_q}$ (a function field over $K$ with full constant field $K$), compatible embeddings $\mathbb F_q\to K\to \overline{\mathbb F}_q(X)$ and $F\to\overline{\mathbb F}_q(X)$, and the points $P_1,\dots,P_n,P_\infty$ on $X_{\overline{\mathbb F}_q}$: for each, the unique place of $\overline{\mathbb F}_q(X)$ lying over it.
--
--   Section 4.2 factors the interpolation polynomial over $\overline{\mathbb F}_q(X)$ and expands functions at a point of $X(\overline{\mathbb F}_q)$; this datum is the setting of those steps.
--
--   **Formalization Note** The fields are those of the published finite-extension datum `AGProxGap.ConstExt`, with "$K/\mathbb F_q$ finite" replaced by "$K$ algebraically closed and algebraic over $\mathbb F_q$".
-- source:
--   Li, Xing, Yuan, Zhu, On Proximity Gaps for One-Point Algebraic Geometric Codes, arXiv:2610.39256 (held version, sha256 d2017986…3b3f), §2.1, p.13; §2.3, p.15; §4.2, p.25

import Mathlib
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

universe u v

namespace AGProxGap.Supplement

/-- **The base change to an algebraic closure, with the points carried along** (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), §2.1, p.13:
"let F̄_q be an algebraic closure of F_q"; §2.3, p.15: "For any field extension K/F_q, let
X_K = X ×_{F_q} K be the curve obtained by extending the constant field. Its function field is
denoted by K(X) … We retain the notation P_∞, P_1, . . . , P_n for the corresponding points on
X_K"; §4.2, p.25: "We factor Q over F̄_q(X) and take local expansions on the curve X_{F̄_q}").

For a function field `F/F_q` and places `P_1, …, P_n, P_∞`, the datum consists of:
1. a field `K` that is an algebraic closure of `F_q` (`IsAlgClosed K`, `K/F_q` algebraic);
2. a field `FK` (the function field `F̄_q(X)` of `X_{F̄_q}`) with compatible algebra maps
   `F_q → K → FK` and `F_q → F → FK`;
3. `FK/K` is again a function field of one variable with full constant field `K`
   (`IsCurveOver K FK`, `Algebra.EssFiniteType K FK`, `ConstantsAreBase K FK`);
4. `FK` is generated over `K` by the image of `F` (`adjoin_eq_top`), i.e. `FK = K · F`;
5. places `lift i` and `liftInf` of `FK/K` lying over `P_i` and `P_∞` (their valuation rings
   pull back to those of `P_i`, `P_∞`), each the only place of `FK` over its base place.

**Formalization Note** This is the published `AGProxGap.ConstExt` with its finiteness field
`FiniteDimensional F_q K` replaced by "`K` is an algebraic closure of `F_q`"; `ConstExt` cannot be
used because `F̄_q/F_q` is infinite. Over the perfect field `F_q` with full constant field,
`F ⊗_{F_q} K` is a field and equals `FK`, so `FK` is the paper's `F̄_q(X)`, and a rational
place of `F` has exactly one place of `FK` over it, the paper's "corresponding point"
(clause 5). Such a datum exists for every function field `F/F_q` of the kind considered. -/
structure ClosureExt {Fq : Type u} {F : Type v} [Field Fq] [Field F] [Algebra Fq F] {n : ℕ}
    (P : Fin n → Place Fq F) (Pinf : Place Fq F) where
  /-- The algebraic closure `F̄_q`. -/
  K : Type u
  /-- The function field `F̄_q(X)` of the base-changed curve. -/
  FK : Type v
  [instFieldK : Field K]
  [instFieldFK : Field FK]
  [instAlgFqK : Algebra Fq K]
  [instAlgKFK : Algebra K FK]
  [instAlgFFK : Algebra F FK]
  [instAlgFqFK : Algebra Fq FK]
  [instTowerK : IsScalarTower Fq K FK]
  [instTowerF : IsScalarTower Fq F FK]
  [instAlgClosed : IsAlgClosed K]
  [instAlgebraic : Algebra.IsAlgebraic Fq K]
  [instCurve : IsCurveOver K FK]
  [instEFT : Algebra.EssFiniteType K FK]
  /-- `K` is the full constant field of `FK`. -/
  constantsAreBase : ConstantsAreBase K FK
  /-- `FK` is generated over `K` by `F`. -/
  adjoin_eq_top : IntermediateField.adjoin K (Set.range (algebraMap F FK)) = ⊤
  /-- The point `P_i` on `X_{F̄_q}`. -/
  lift : Fin n → Place K FK
  /-- The point `P_∞` on `X_{F̄_q}`. -/
  liftInf : Place K FK
  lift_comap : ∀ i, (lift i).toValuationSubring.comap (algebraMap F FK) = (P i).toValuationSubring
  liftInf_comap : liftInf.toValuationSubring.comap (algebraMap F FK) = Pinf.toValuationSubring
  lift_unique : ∀ i (Q : Place K FK),
    Q.toValuationSubring.comap (algebraMap F FK) = (P i).toValuationSubring → Q = lift i
  liftInf_unique : ∀ Q : Place K FK,
    Q.toValuationSubring.comap (algebraMap F FK) = Pinf.toValuationSubring → Q = liftInf

attribute [instance] ClosureExt.instFieldK ClosureExt.instFieldFK ClosureExt.instAlgFqK
  ClosureExt.instAlgKFK ClosureExt.instAlgFFK ClosureExt.instAlgFqFK ClosureExt.instTowerK
  ClosureExt.instTowerF ClosureExt.instAlgClosed ClosureExt.instAlgebraic ClosureExt.instCurve
  ClosureExt.instEFT

end AGProxGap.Supplement


