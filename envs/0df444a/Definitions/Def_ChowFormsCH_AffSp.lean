-- Prove2me | Definitions.Def_ChowFormsCH_AffSp
-- name    : ChowFormsCH_AffSp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:56:28.739514+00:00
-- url     : https://prove2.me/theorems/32a749e4-a01b-49eb-9c7f-102e192a24c4
-- title:
--   Affine space $K^\sigma$ with the Zariski topology; zero sets $V(T)$ and affine varieties
-- statement:
--   For a field $K$ and an index set $\sigma$, **affine space** $K^\sigma$ is the set of points $x=(x_s)_{s\in\sigma}$ with coordinates in $K$, equipped with the **Zariski topology**, whose closed sets are the common zero sets of families of polynomials. For a set $T\subseteq K[x_s : s\in\sigma]$ of polynomials,
--   $$
--   V(T)=\{x\in K^\sigma : f(x)=0 \text{ for all } f\in T\},
--   $$
--   and an **affine variety** is any set of the form $V(T)$. Following the paper, varieties may be reducible.
--
--   These are the ambient spaces of Section 3.2 (affine varieties $V\subset K^{m+n}$ with coordinates $x_1,\dots,x_m,y_1,\dots,y_n$) and the base of the projective model.
--
--   **Formalization Note** The type `AffSp σ K` is a synonym of `σ → K` that carries the Zariski topology, induced from the prime spectrum of $K[\sigma]$ by $x\mapsto \ker(\mathrm{ev}_x)$; its closed sets are exactly the sets $V(T)$.
-- source:
--   Andrews, Garg, Oliveira, Schost, Some algebraic and geometric computations in CH via Chow forms, arXiv:2611.05289 (held version, sha256 75e796c6…), §2.1, p.8; §3.2, p.22

import Mathlib

set_option autoImplicit false

namespace ChowFormsCH

/-- Affine space `K^σ` with its Zariski topology (Andrews–Garg–Oliveira–Schost, *Some algebraic
and geometric computations in CH via Chow forms*, arXiv:2611.05289, held version, sha256 75e796c6…,
§2.1, p.8: "V(f1, . . . , fm) … their common zeroes in A^n"; §3.2, p.22).

A point is a function `σ → K`. The type is a synonym so that it carries the Zariski topology and
not a product topology of `K`.

**Formalization Note** The Zariski topology is induced by the map sending a point `x` to the prime
ideal `ker (eval x)` of `K[σ]`, from the Zariski topology of the prime spectrum: its closed sets
are exactly the common zero sets of families of polynomials. -/
def AffSp (σ K : Type*) : Type _ := σ → K

/-- The point `x ∈ K^σ` as the prime ideal of polynomials vanishing at `x`. -/
noncomputable def AffSp.toPrimeSpectrum {σ K : Type*} [Field K] (x : AffSp σ K) :
    PrimeSpectrum (MvPolynomial σ K) :=
  ⟨RingHom.ker (MvPolynomial.eval (show σ → K from x)), RingHom.ker_isPrime _⟩

/-- The Zariski topology on `K^σ`: closed sets are common zero sets of polynomials. -/
noncomputable instance AffSp.instTopologicalSpace {σ K : Type*} [Field K] :
    TopologicalSpace (AffSp σ K) :=
  TopologicalSpace.induced AffSp.toPrimeSpectrum inferInstance

/-- The common zero set `V(T) ⊆ K^σ` of a set `T` of polynomials (§2.1, p.8). -/
def zeroSet {σ K : Type*} [Field K] (T : Set (MvPolynomial σ K)) : Set (AffSp σ K) :=
  {x | ∀ f ∈ T, MvPolynomial.eval (show σ → K from x) f = 0}

/-- An affine variety: the common zero set of some set of polynomials (§2.1, p.8: "a variety is
any set of solutions to a system of polynomial equations over an algebraically closed field; in
particular, varieties may be reducible"). -/
def IsAffVariety {σ K : Type*} [Field K] (V : Set (AffSp σ K)) : Prop :=
  ∃ T : Set (MvPolynomial σ K), V = zeroSet T

end ChowFormsCH


