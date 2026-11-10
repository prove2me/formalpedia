-- Prove2me | Definitions.Def_AlgebraicFPT_HittingSet_Model
-- name    : AlgebraicFPT_HittingSet_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T12:56:45.343808+00:00
-- url     : https://prove2.me/theorems/56fbb5d3-28d5-4c71-8621-335ec708589e
-- title:
--   Hypergraph edge ideal and complex coordinate subspaces
-- statement:
--   Let $E$ be a finite hyperedge family on $V=\{0,\ldots,n-1\}$. In the genuine polynomial ring $\mathbb C[z_v:v\in V]$, define
--   $$m_e=\prod_{v\in e}z_v,\qquad I_E=\langle m_e:e\in E\rangle,\qquad \mathcal V(I_E)=\{z\in\mathbb C^n:\forall f\in I_E,\ f(z)=0\}.$$
--   For $C\subseteq V$, put
--   $$L_C=\{z\in\mathbb C^n:\forall v\in C,\ z_v=0\}.$$
--
--   These are the paper's edge ideal and actual complex zero locus. In particular, the empty product is $1$, an empty edge forces an empty zero locus, and an empty family yields the zero ideal and the whole affine space. No Boolean equations or cardinality constraint are appended. Component correspondence, coordinate-subspace dimension and degree, and the count bound remain mathematical conclusions to establish.
-- source:
--   Liming Cai, Sixiang Zhang, STOC 2027 submission #1035 (October 2026), p.3, §2.1; p.4, §3

import Definitions.Def_AlgebraicFPT_HittingSet_HittingSets
import Definitions.Def_AlgebraicFPT_HittingSet_Geometry

set_option autoImplicit false

namespace AlgebraicFPT.HittingSet

/-- The squarefree monomial of a hyperedge (§3, p.4); the empty product is 1. -/
noncomputable def edgeMonomial {n : ℕ} (e : Finset (Fin n)) : MvPolynomial (Fin n) ℂ :=
  ∏ v ∈ e, MvPolynomial.X v

/-- The actual edge ideal, with all its polynomial multiples and finite sums. -/
noncomputable def edgeIdeal {n : ℕ} (E : Finset (Finset (Fin n))) : Ideal (MvPolynomial (Fin n) ℂ) :=
  Ideal.span (edgeMonomial '' (E : Set (Finset (Fin n))))

/-- All complex zeros of the ideal, without Boolean equations or a size constraint. -/
def edgeVariety {n : ℕ} (E : Finset (Finset (Fin n))) : Set (Fin n → ℂ) :=
  RSCapacity.zeroSet (edgeIdeal E : Set (MvPolynomial (Fin n) ℂ))

/-- The coordinate subspace L_C of §3, p.4, not an assumed component. -/
def coordinateSubspace {n : ℕ} (C : Finset (Fin n)) : Set (Fin n → ℂ) :=
  {z | ∀ v ∈ C, z v = 0}

end AlgebraicFPT.HittingSet


