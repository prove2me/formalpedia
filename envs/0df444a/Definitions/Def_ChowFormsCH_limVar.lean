-- Prove2me | Definitions.Def_ChowFormsCH_limVar
-- name    : ChowFormsCH_limVar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:59:39.739773+00:00
-- url     : https://prove2.me/theorems/fc735b62-1363-4460-b689-6fd6652a6ed8
-- title:
--   The deformation $V^p(G_1,\dots,G_k)\subseteq\mathbb P^n\times\mathbb A^1$, its part $V'$, and the limit varieties $\lim_{t\to\tau}V^p$
-- statement:
--   Let $G_1,\dots,G_k\in K[x_0,\dots,x_n]$ be forms of degrees $d_1,\dots,d_k$, $k\le n$. Then
--   $$
--   V^p(G_1,\dots,G_k)=V\big((1-t)G_1+tx_1^{d_1},\dots,(1-t)G_k+tx_k^{d_k}\big)\subseteq \mathbb P^n\times\mathbb A^1 .
--   $$
--   Let $W_1,\dots,W_a$ be those irreducible components of $V^p(G_1,\dots,G_k)$ whose projection to $\mathbb A^1$ is surjective, and $V'(G_1,\dots,G_k)=W_1\cup\dots\cup W_a$. For $\tau\in K$, $\lim_{t\to\tau}V^p(G_1,\dots,G_k)\subseteq\mathbb P^n$ is the set of $x$ with $(x,\tau)\in V'(G_1,\dots,G_k)$.
--
--   This deformation, generalizing Ierardi's construction, produces the equidimensional subvarieties whose Chow forms Lemmas 4.6 and 4.7 compute.
--
--   **Formalization Note** $\mathbb P^n\times\mathbb A^1$ is modelled by the points $(x,t)\in K^{n+1}\times K$ with $x\neq 0$, with the Zariski topology of $K^{n+2}$ restricted (not a product topology); a subvariety of codimension $k$ has topological dimension $n+2-k$. Indices are 0-based: `G i` is paired with $x_{i+1}$, never with $x_0$.
-- source:
--   Andrews, Garg, Oliveira, Schost, Some algebraic and geometric computations in CH via Chow forms, arXiv:2611.05289 (held version, sha256 75e796c6…), §4.1, pp.28–29

import Mathlib
import Definitions.Def_ChowFormsCH_comps

set_option autoImplicit false

namespace ChowFormsCH

/-- The space `P^n × A¹`, modelled as the set of points `(x, t) ∈ K^{n+1} × K` with `x ≠ 0`, with
the subspace topology of the Zariski topology of `K^{n+2}` (Andrews–Garg–Oliveira–Schost, *Some
algebraic and geometric computations in CH via Chow forms*, arXiv:2611.05289, held version,
sha256 75e796c6…, §4.1, p.28).

**Formalization Note** The coordinate `t` is `p none` and `x_j` is `p (some j)`. As for
`ProjSpace`, a point of `P^n` is represented by all its nonzero representatives; the topological
Krull dimension of the model of a subvariety of `P^n × A¹` of dimension `e` is `e + 1`, so a
subvariety of codimension `k` has topological dimension `n + 2 − k`. The topology is the Zariski
topology of `K^{n+2}` restricted, not a product topology. -/
def ProjAff (n : ℕ) (K : Type*) [Field K] : Type _ :=
  {p : Option (Fin (n + 1)) → K // (fun j => p (some j)) ≠ 0}

/-- The topology of `P^n × A¹`, induced from the Zariski topology of `K^{n+2}`. -/
noncomputable instance ProjAff.instTopologicalSpace {n : ℕ} {K : Type*} [Field K] :
    TopologicalSpace (ProjAff n K) :=
  TopologicalSpace.induced (fun p : ProjAff n K => (show AffSp (Option (Fin (n + 1))) K from p.1))
    inferInstance

/-- The `P^n`-coordinates `x = (x₀, …, xₙ)` of a point of `P^n × A¹`. -/
def ProjAff.x {n : ℕ} {K : Type*} [Field K] (p : ProjAff n K) : Fin (n + 1) → K :=
  fun j => p.1 (some j)

/-- The `A¹`-coordinate `t` of a point of `P^n × A¹`. -/
def ProjAff.t {n : ℕ} {K : Type*} [Field K] (p : ProjAff n K) : K := p.1 none

/-- The variety `V^p(G₁, …, G_k) ⊆ P^n × A¹` defined by
`(1 − t)G₁ + t x₁^{d₁}, …, (1 − t)G_k + t x_k^{d_k}` (§4.1, p.28), for forms `G_i` of degree `d_i`
and `k ≤ n`.

**Formalization Note** Indices are 0-based: `G i`, `i : Fin k`, is the paper's `G_{i+1}`, and it is
paired with the coordinate `x_{i+1}` (`(Fin.castLE hk i).succ`), never with `x₀`. -/
def Vp {n k : ℕ} {K : Type*} [Field K] (hk : k ≤ n) (G : Fin k → MvPolynomial (Fin (n + 1)) K)
    (d : Fin k → ℕ) : Set (ProjAff n K) :=
  {p | ∀ i : Fin k, (1 - p.t) * MvPolynomial.eval p.x (G i)
      + p.t * p.x (Fin.castLE hk i).succ ^ d i = 0}

/-- `V′(G₁, …, G_k)`: the union of the irreducible components of `V^p(G₁, …, G_k)` whose
projection to `A¹` is surjective (§4.1, p.29: "Let W1, . . . , Wa be those irreducible components of
V^p(G1, . . . , Gk) whose projection to A^1 is surjective. We use V′(G1, . . . , Gk) to denote
⋃_{i=1}^a Wi."). -/
def Vprime {n k : ℕ} {K : Type*} [Field K] (hk : k ≤ n) (G : Fin k → MvPolynomial (Fin (n + 1)) K)
    (d : Fin k → ℕ) : Set (ProjAff n K) :=
  ⋃₀ {Z | Z ∈ comps (Vp hk G d) ∧ ∀ τ : K, ∃ p ∈ Z, p.t = τ}

/-- `lim_{t→τ} V^p(G₁, …, G_k) ⊆ P^n`: the subvariety of `P^n` corresponding to the intersection of
`V′(G₁, …, G_k)` with the hyperplane `t = τ` (§4.1, p.29). -/
def limVar {n k : ℕ} {K : Type*} [Field K] (hk : k ≤ n) (G : Fin k → MvPolynomial (Fin (n + 1)) K)
    (d : Fin k → ℕ) (τ : K) : Set (ProjSpace n K) :=
  {x | ∃ p ∈ Vprime hk G d, p.t = τ ∧ p.x = x.1}

end ChowFormsCH


