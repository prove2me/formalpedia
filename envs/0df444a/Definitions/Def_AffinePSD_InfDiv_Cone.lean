-- Prove2me | Definitions.Def_AffinePSD_InfDiv_Cone
-- name    : AffinePSD_InfDiv_Cone
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:48:50.327762+00:00
-- url     : https://prove2.me/theorems/a01bfec5-3e10-40e0-8240-ba4b507811ad
-- title:
--   The space $M_d$, the trace pairing $\langle x,y\rangle=\mathrm{Tr}(xy)$, its norm, and the cone $S_d^+$ (§1.2)
-- statement:
--   Let $M_d$ be the space of real $d\times d$ matrices and $S_d\subset M_d$ the symmetric ones. The paper's scalar product is the **trace pairing**
--   $$\langle x,y\rangle=\mathrm{Tr}(xy)=\sum_{i,j}x_{ij}y_{ji},$$
--   with induced norm $\|x\|=\sqrt{\langle x,x\rangle}$ (the Frobenius norm on $S_d$). The **state space** is the cone $S_d^+$ of symmetric positive semidefinite matrices. It is a convex cone: for $x^{(1)},\dots,x^{(k)}\in S_d^+$ the sum $x^{(1)}+\dots+x^{(k)}$ lies again in $S_d^+$. The file also records the matrix product and the symmetry predicate.
--
--   These are the basic objects of every statement of the mission.
--
--   **Formalization Note** $M_d$ is the function type `Fin d → Fin d → ℝ`, so it carries Mathlib's normed, measurable and Borel structures. Positive semidefiniteness is Mathlib's `Matrix.PosSemidef`, which over $\mathbb R$ includes symmetry. $S_d^+$ is a subtype of $M_d$ with the subspace topology and the subspace Borel σ-algebra. The paper never names its norm, and its only scalar product is $\mathrm{Tr}(xy)$, so `fnorm` is the norm of that pairing.
-- source:
--   Cuchiero, Filipović, Mayerhofer, Teichmann, Affine processes on positive semidefinite matrices, arXiv:0910.0137v3 (2011), §1.2, p. 6

import Mathlib
import Definitions.Def_AffinePSD_Necessity_Cone

namespace AffinePSD.InfDiv

/-- The sum of two points of the convex cone `S_d^+`. -/
def coneAdd {d : ℕ} (x y : AffinePSD.Necessity.Cone d) : AffinePSD.Necessity.Cone d :=
  ⟨x.1 + y.1, by
    have h : (Matrix.of x.1 + Matrix.of y.1).PosSemidef := Matrix.PosSemidef.add x.2 y.2
    exact h⟩

/-- The sum `x^{(1)} + ⋯ + x^{(k)}` of finitely many points of `S_d^+`. -/
def coneSum {d k : ℕ} (xs : Fin k → AffinePSD.Necessity.Cone d) : AffinePSD.Necessity.Cone d :=
  ⟨∑ i, (xs i).1, by
    have h : (∑ i, Matrix.of (xs i).1).PosSemidef :=
      Matrix.posSemidef_sum Finset.univ (fun i _ => (xs i).2)
    exact h⟩

end AffinePSD.InfDiv


