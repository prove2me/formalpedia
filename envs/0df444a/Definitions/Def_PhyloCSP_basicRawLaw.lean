-- Prove2me | Definitions.Def_PhyloCSP_basicRawLaw
-- name    : PhyloCSP_basicRawLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:23:50.808228+00:00
-- url     : https://prove2.me/theorems/4b142786-da23-464a-9f57-92e966f48265
-- title:
--   The output law of a basic transformation
-- statement:
--   A **basic transformation** (Definition 3.3) is given by a template $B$, a probability distribution $p$ on $\mathrm{Loc}(B)$ and a **centrally symmetric** probability distribution $\nu$ on sign vectors $r\in\{\pm1\}^{E(B)}$, meaning $\nu(r)=\nu(-r)$, with coordinates not necessarily independent. On an input tree $T$ it assigns each leaf $x$ independently to a location $\xi(x)\sim p$, samples an independent copy $r(v)\sim\nu$ at every internal node $v$ of $T$, and outputs the tree described by `rawOut`. As in eq. (15) of the paper, the probability that the output relation equals $R$ is
--   $$
--   \sum_{\xi}\ \sum_{r}\ \Bigl(\prod_{x}p(\xi(x))\Bigr)\Bigl(\prod_{v}\nu(r(v))\Bigr)\,\mathbf 1\{\text{output}(\xi,r)=R\}.
--   $$
--
--   **Formalization Note** The law is on raw ternary relations; that the output is a tree is a property of the construction, not of the type. The law sums to $1$ over all relations (checked).
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Definition 3.3, p.8 (PDF p.10); eq. (15), p.48 (PDF p.50)

import Mathlib
import Definitions.Def_PhyloCSP_rawOut

set_option autoImplicit false

open scoped ENNReal

namespace PhyloCSP

open Template

/-- **Central symmetry of an orientation law** (Definition 3.3, p.8 = PDF p.10): "a centrally
symmetric probability distribution ν (that is, ν(r) = ν(−r))", where `−r` flips every coordinate.
Signs `±1` are `true`/`false`. -/
def IsCentrallySymmetric {E : Type} (ν : PMF (E → Bool)) : Prop :=
  ∀ r : E → Bool, ν (fun e => !r e) = ν r

/-- **The output law of a basic transformation (Definition 3.3; eq. (15)).**

Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027 submission
(manuscript sha256 3444b6c0…682dac), Definition 3.3, p.8 (PDF p.10), steps 1–4, and eq. (15),
p.48 (PDF p.50): "Pr(G[P] ∈ Sat(φ)) = Σ_ξ (Π_i p_ξ(i)) Σ_ω Pr(ω | ξ) 1{G(P; ξ, ω) ∈ Sat(φ)}".
Each input leaf `x` is assigned independently to a location `ξ(x)` with law `p` (step 1); each
internal node `v` of the input independently receives a copy `r(v)` of the sign vector with law
`ν` (step 3); the output is the deterministic relation `rawOut B C ξ r`.

`basicRawLaw B p ν C R` is the probability that the output relation equals `R`.

**Formalization Note.** The law is on *raw* relations `X → X → X → Bool`; that the output is a
tree relation is a property of the construction, not built into the type. A pinned mixture
(`IsMixtureOfBasic`) can exist only if the construction puts no mass on non-tree relations. -/
noncomputable def basicRawLaw (B : Template) (p : PMF B.Loc) (ν : PMF (B.Edge → Bool))
    {X : Type} [Fintype X] [LinearOrder X] (C : X → X → X → Bool) (R : X → X → X → Bool) :
    ℝ≥0∞ :=
  ∑ ξ : X → B.Loc, ∑ r : IntNode C → B.Edge → Bool,
    (∏ x, p (ξ x)) * (∏ v, ν (r v)) *
      (if ∀ a b c, (R a b c = true ↔ rawOut B C ξ r a b c) then 1 else 0)

end PhyloCSP


