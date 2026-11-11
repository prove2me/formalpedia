-- Prove2me | Definitions.Def_ChowFormsCH_ProjSpace
-- name    : ChowFormsCH_ProjSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:57:15.693044+00:00
-- url     : https://prove2.me/theorems/407b5379-0633-4397-9050-0f133ae96dd6
-- title:
--   Projective space $\mathbb P^n$, projective zero sets $V(F_1,\dots,F_m)$, projective varieties and linear images
-- statement:
--   **Projective space** $\mathbb P^n$ over $K$ is modelled by the punctured affine cone $K^{n+1}\setminus\{0\}$ with the Zariski topology of $K^{n+1}$ restricted to it: a point of $\mathbb P^n$ is represented by all of its nonzero representatives $(x_0,\dots,x_n)$. For a set $T$ of forms in $x_0,\dots,x_n$,
--   $$
--   V(T)=\{x\in K^{n+1}\setminus\{0\} : F(x)=0 \text{ for all } F\in T\}\subseteq \mathbb P^n
--   $$
--   is its projective zero set, and a **projective variety** is the zero set of some set of forms. For a matrix $M\in K^{(n+1)\times(n+1)}$ and $V\subseteq\mathbb P^n$, the **linear image** is $\phi(V)=\{M\alpha:\alpha\in V\}$.
--
--   These objects carry the varieties $V(F_1,\dots,F_m)$ of Theorem 4.9, the Chow forms of Section 3.1 and the changes of coordinates of Lemmas 3.1 and 4.8.
--
--   **Formalization Note** Irreducible closed subsets of the punctured cone correspond to those of $\mathbb P^n$; the topological Krull dimension of the punctured cone over a projective variety of dimension $r$ is $r+1$. Points $\alpha$ with $M\alpha=0$ contribute nothing to $\phi(V)$; for invertible $M$ there are none.
-- source:
--   Andrews, Garg, Oliveira, Schost, Some algebraic and geometric computations in CH via Chow forms, arXiv:2611.05289 (held version, sha256 75e796c6…), §2.1, p.8; Lemma 3.1, p.22; Lemma 4.8, p.33

import Mathlib
import Definitions.Def_ChowFormsCH_AffSp

set_option autoImplicit false

namespace ChowFormsCH

/-- Projective space `P^n` over `K`, modelled by the punctured affine cone `K^{n+1} \ {0}` with the
subspace topology of the Zariski topology of `K^{n+1}` (Andrews–Garg–Oliveira–Schost, *Some
algebraic and geometric computations in CH via Chow forms*, arXiv:2611.05289, held version,
sha256 75e796c6…, §2.1, p.8: "V(F1, . . . , Fm) is taken to be their common zeroes in the
projective space P^n").

**Formalization Note** A point of `P^n` is represented by all of its nonzero representatives:
subsets of `ProjSpace n K` that come from forms are unions of punctured lines through the origin.
The irreducible closed subsets of the punctured cone correspond to those of `P^n`, and the
topological Krull dimension of the punctured cone over a projective variety of dimension `r` is
`r + 1`. Coordinates are `x₀, …, xₙ`, indexed by `Fin (n+1)`. -/
def ProjSpace (n : ℕ) (K : Type*) [Field K] : Type _ := {x : Fin (n + 1) → K // x ≠ 0}

/-- The topology of `P^n`: the subspace topology of the punctured cone in `K^{n+1}`. -/
noncomputable instance ProjSpace.instTopologicalSpace {n : ℕ} {K : Type*} [Field K] :
    TopologicalSpace (ProjSpace n K) :=
  TopologicalSpace.induced (fun p : ProjSpace n K => (show AffSp (Fin (n + 1)) K from p.1))
    inferInstance

/-- The projective zero set `V(T) ⊆ P^n` of a set `T` of polynomials in `x₀, …, xₙ` (§2.1, p.8);
it is meaningful when `T` consists of forms. -/
def projZero {n : ℕ} {K : Type*} [Field K] (T : Set (MvPolynomial (Fin (n + 1)) K)) :
    Set (ProjSpace n K) :=
  {x | ∀ f ∈ T, MvPolynomial.eval x.1 f = 0}

/-- A projective variety: the common zero set in `P^n` of a set of forms (§2.1, p.8). -/
def IsProjVariety {n : ℕ} {K : Type*} [Field K] (V : Set (ProjSpace n K)) : Prop :=
  ∃ T : Set (MvPolynomial (Fin (n + 1)) K), (∀ f ∈ T, ∃ e : ℕ, f.IsHomogeneous e) ∧ V = projZero T

/-- The image `ϕ(V) = {Mα : α ∈ V}` of `V ⊆ P^n` under the linear map of a matrix `M`
(Lemma 3.1, p.22; Lemma 4.8, p.33). Points `α` with `Mα = 0` contribute nothing; for invertible
`M` there are none. -/
def linImage {n : ℕ} {K : Type*} [Field K] (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (V : Set (ProjSpace n K)) : Set (ProjSpace n K) :=
  {y | ∃ x ∈ V, y.1 = M.mulVec x.1}

end ChowFormsCH


