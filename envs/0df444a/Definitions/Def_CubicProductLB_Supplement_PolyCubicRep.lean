-- Prove2me | Definitions.Def_CubicProductLB_Supplement_PolyCubicRep
-- name    : CubicProductLB_Supplement_PolyCubicRep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:36:35.795191+00:00
-- url     : https://prove2.me/theorems/bf397083-6401-45a4-a9e9-32e76eb7ace4
-- title:
--   Cubic product representation of $F_{q,n}$ over $\mathbb F_p$ (Definition 31)
-- statement:
--   A **cubic product representation** of $F_{q,n}$ over $\mathbb F_p$ is a list of polynomials $P_1,\dots,P_m \in \mathbb F_p[x_1,\dots,x_n]$ with $\deg P_j \le 3$ such that
--   $$F_{q,n}(x) = \prod_{j=1}^m P_j(x) \qquad \text{for all } x \in \{-1,1\}^n.$$
--   The equality is functional equality on the sign cube; no formal polynomial identity is assumed. The number of factors is $m$; factors may be constant and may repeat.
--
--   The definition also provides the number of factors that are **nonconstant on the sign cube**, i.e. take two different values on $\{-1,1\}^n$; Theorem 32's second sentence is stated for this count.
--
--   **Formalization Note** $\deg$ is the formal total degree, as printed in Definition 31.
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Definition 31, Eq. (398), p.51; Theorem 32, p.51

import Mathlib
import Definitions.Def_CubicProductLB_Supplement_signCubeP
import Definitions.Def_CubicProductLB_Supplement_signedModP

namespace CubicProductLB.Supplement

/-- A cubic product representation of `F_{q,n}` over `F_p` (Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Definition 31, Eq. (398), p.51):
polynomials `P_1, …, P_m ∈ F_p[x_1, …, x_n]` with `deg P_j ≤ 3` whose product equals `F_{q,n}` at every
point of `{-1, 1}^n`.

**Formalization Note** `deg` is the formal total degree, as printed. Equality is functional on the
sign cube only; no formal polynomial identity is required. `m` is `factors.length`; a factor may be
constant and factors may repeat. -/
structure PolyCubicRep (p q n : ℕ) where
  /-- the factors `P_1, …, P_m` -/
  factors : List (MvPolynomial (Fin n) (ZMod p))
  /-- `deg P_j ≤ 3` -/
  deg_le : ∀ P ∈ factors, P.totalDegree ≤ 3
  /-- the product equals `F_{q,n}` on `{-1, 1}^n` -/
  rep : ∀ x ∈ signCubeP p n, (factors.map fun P => MvPolynomial.eval x P).prod = signedModP p q n x

/-- The number of factors of a representation that are nonconstant as functions on the sign cube,
i.e. take two different values on `{-1, 1}^n` (Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Theorem 32, second sentence, p.51). -/
noncomputable def PolyCubicRep.nonconstCount {p q n : ℕ} (r : PolyCubicRep p q n) : ℕ := by
  classical
  exact r.factors.countP fun P => decide (∃ x ∈ signCubeP p n, ∃ y ∈ signCubeP p n,
    MvPolynomial.eval x P ≠ MvPolynomial.eval y P)

end CubicProductLB.Supplement


