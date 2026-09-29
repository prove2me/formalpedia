-- Prove2me | Definitions.Def_WeierstrassCurve_KernelPolynomial
-- name    : WeierstrassCurve_KernelPolynomial
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:30.087021+00:00
-- url     : https://prove2.me/theorems/ede22ca4-aec7-521e-8a82-779bac65c737
-- title:
--   Kernel polynomial of a finite set of coordinate pairs
-- statement:
--   Over a commutative ring $R$, for a finite set $S$ of pairs $(x,y) \in R \times R$ — in the intended application the affine coordinates of finitely many points of a Weierstrass curve, e.g. one representative of each $\pm$-pair among the nonzero points of a finite subgroup of odd order — [`WeierstrassCurve.kernelPolynomial S`](../def/WeierstrassCurve_KernelPolynomial.html#L11) is the polynomial
--   $$\prod_{P \in S} \bigl(X - C\,P_1\bigr) \in R[X],$$
--   the product over the elements of $S$ of $X$ minus (the constant polynomial on) the first coordinate. Nothing further is built into the definition: the pairs are not required to lie on any curve, to form a subgroup, or to have distinct first coordinates, and the second coordinates are discarded.
--
--   The accompanying lemmas are the elementary formal properties. The empty set gives $1$; a singleton $\{P\}$ gives $X - C\,P_1$; adjoining a point $P \notin S$ (in the `Finset.cons` and the `insert` forms) multiplies the polynomial by $X - C\,P_1$; and the product may be rewritten as the product of the multiset obtained by mapping $x \mapsto X - C\,x$ over the first coordinates of the underlying multiset of $S$. The polynomial is monic, and over a nontrivial ring its `natDegree` is the cardinality of $S$. Its value at $x \in R$ is $\prod_{P \in S}(x - P_1)$; consequently it vanishes at $P_1$ for every $P \in S$, and over a domain its value at $x$ vanishes if and only if some $P \in S$ has $P_1 = x$, while its multiset of roots is exactly the multiset of first coordinates of $S$, with multiplicity. For a ring homomorphism $f : R \to S'$ the image polynomial is $\prod_{P \in S}(X - C\,f(P_1))$, and when $\mathrm{Prod.map}\ f\ f$ is injective on $S$ this equals the kernel polynomial of the image finite set $f(S) \subseteq S' \times S'$.
--
--   **Relation to Mathlib.** Mathlib has no kernel-polynomial construction; this is the project's own definition, placed in the `WeierstrassCurve` namespace but formulated for an arbitrary finite set of pairs in $R \times R$ rather than for points of a curve.
--
--   **Where it is used.** The polynomial serves as the kernel polynomial, in the sense of Kohel, of a separable isogeny with prescribed kernel of odd order: its coefficients are what the Vélu-type quotient curve is expressed through over an arbitrary commutative ring, and it is the object lifted when a curve is deformed over a complete local ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_WeierstrassCurve_KernelPolynomial.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

noncomputable def kernelPolynomial (S : Finset (R × R)) : R[X] :=
  ∏ P ∈ S, (X - C P.1)

@[simp] theorem kernelPolynomial_empty : kernelPolynomial (∅ : Finset (R × R)) = 1 := by
  simp [kernelPolynomial]

theorem kernelPolynomial_cons {P : R × R} {S : Finset (R × R)} (hP : P ∉ S) :
    kernelPolynomial (Finset.cons P S hP) = (X - C P.1) * kernelPolynomial S := by
  simp [kernelPolynomial, Finset.prod_cons]

theorem kernelPolynomial_insert [DecidableEq R] {P : R × R} {S : Finset (R × R)} (hP : P ∉ S) :
    kernelPolynomial (insert P S) = (X - C P.1) * kernelPolynomial S := by
  simp [kernelPolynomial, Finset.prod_insert hP]

@[simp] theorem kernelPolynomial_singleton (P : R × R) :
    kernelPolynomial ({P} : Finset (R × R)) = X - C P.1 := by
  simp [kernelPolynomial]

theorem kernelPolynomial_eq_multiset_prod (S : Finset (R × R)) :
    kernelPolynomial S = ((S.val.map Prod.fst).map fun x => X - C x).prod := by
  rw [kernelPolynomial, Finset.prod_eq_multiset_prod, Multiset.map_map]
  rfl

theorem monic_kernelPolynomial (S : Finset (R × R)) : (kernelPolynomial S).Monic :=
  monic_prod_of_monic _ _ fun P _ => monic_X_sub_C P.1

theorem natDegree_kernelPolynomial [Nontrivial R] (S : Finset (R × R)) :
    (kernelPolynomial S).natDegree = S.card := by
  rw [kernelPolynomial, natDegree_prod_of_monic _ _ fun P _ => monic_X_sub_C P.1]
  simp

theorem eval_kernelPolynomial (S : Finset (R × R)) (x : R) :
    (kernelPolynomial S).eval x = ∏ P ∈ S, (x - P.1) := by
  simp [kernelPolynomial, eval_prod]

theorem eval_kernelPolynomial_eq_zero {S : Finset (R × R)} {P : R × R} (hP : P ∈ S) :
    (kernelPolynomial S).eval P.1 = 0 := by
  rw [eval_kernelPolynomial]
  exact Finset.prod_eq_zero hP (sub_self _)

theorem map_kernelPolynomial {S' : Type*} [CommRing S'] (f : R →+* S') (S : Finset (R × R)) :
    (kernelPolynomial S).map f = ∏ P ∈ S, (X - C (f P.1)) := by
  simp [kernelPolynomial, Polynomial.map_prod]

theorem map_kernelPolynomial_of_injOn {S' : Type*} [CommRing S'] [DecidableEq S'] (f : R →+* S')
    (S : Finset (R × R)) (hf : Set.InjOn (Prod.map f f) S) :
    (kernelPolynomial S).map f = kernelPolynomial (S.image (Prod.map f f)) := by
  rw [map_kernelPolynomial, kernelPolynomial, Finset.prod_image hf]
  simp

theorem roots_kernelPolynomial [IsDomain R] (S : Finset (R × R)) :
    (kernelPolynomial S).roots = S.val.map Prod.fst := by
  rw [kernelPolynomial_eq_multiset_prod, roots_multiset_prod_X_sub_C]

theorem eval_kernelPolynomial_eq_zero_iff [IsDomain R] {S : Finset (R × R)} {x : R} :
    (kernelPolynomial S).eval x = 0 ↔ ∃ P ∈ S, P.1 = x := by
  rw [eval_kernelPolynomial, Finset.prod_eq_zero_iff]
  simp [sub_eq_zero, eq_comm]

end WeierstrassCurve


