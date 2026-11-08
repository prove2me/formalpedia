-- Prove2me | Definitions.Def_AFIsingKS_Matching
-- name    : AFIsingKS_Matching
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T10:14:24.861459+00:00
-- url     : https://prove2.me/theorems/f3a184cc-406e-4cb0-820c-06aeba182658
-- title:
--   The configuration model $\mathbb G(n,d)$: matchings, $\mathcal H_M$, $\mathbb E$ and $\Pr$
-- statement:
--   Form $n$ clouds of $d$ sockets each, $(v,1),\dots,(v,d)$. The **configuration model** samples a uniformly random perfect matching $M$ of the $dn$ sockets; contracting the clouds gives a $d$-regular multigraph. For $\sigma\in\{\pm1\}^n$,
--   $$\mathcal H_M(\sigma)=\sum_{\{(u,i),(v,j)\}\in M}\frac{1-\sigma_u\sigma_v}{2}$$
--   is the number of matched pairs whose clouds carry different spins, so a pair inside one cloud contributes $0$ and parallel pairs count separately. $\mathbb E$ and $\Pr$ denote the average over the finitely many matchings.
--
--   **Formalization Note** A perfect matching is a `Pairing` of the sockets, the published type of fixed-point-free involutions, a socket's image being its partner, and socket labels run over $\{0,\dots,d-1\}$. No such involution exists when $nd$ is odd, in which case averages are $0/0=0$; every statement assumes $nd$ even. The Hamiltonian counts sockets whose partner's cloud has the other spin and halves the count; the division is exact.
-- source:
--   Bencs, Huang, Lee, Liu, Regts, On Zeros and Algorithms for Disordered Systems II, arXiv:2610.40598 (held version, sha256 2a07c158…), Section 2.2, p.9

import Mathlib
import Definitions.Def_AFIsingKS_overlap
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings

open scoped Classical

namespace AFIsingKS

/-- A perfect matching of the `dn` sockets `V × [d]`: the outcomes of the configuration model
`G(n, d)` (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), Section 2.2, p.9).

**Formalization Note.** A perfect matching of the sockets is a `Pairing` of `Fin n × Fin d`, the published
type of fixed-point-free involutions (a socket's image is its partner); socket labels run over `Fin d`
rather than `1, …, d`. The type is empty when `n * d` is odd. -/
abbrev Matching (n d : ℕ) : Type :=
  OAI.MatchingSmoothing.Pairing (Fin n × Fin d)

/-- The Hamiltonian `H_F(σ) = ∑_{{(u,i),(v,j)} ∈ F} (1 − σ_u σ_v)/2` for `F = M`
(Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), Section 2.2, p.9): the number of matched socket pairs whose clouds have different spins.

**Formalization Note.** The set counts sockets `x` whose partner's cloud has a different spin, and
each such pair `{x, M x}` contains exactly two such sockets, so the division by `2` is exact. A pair
inside one cloud contributes `0` and parallel pairs count separately. -/
noncomputable def cmCut {n d : ℕ} (M : Matching n d) (σ : Spin n) : ℕ :=
  (Finset.univ.filter (fun x : Fin n × Fin d => σ x.1 ≠ σ (M.1 x).1)).card / 2

/-- The expectation `𝔼_{G ∼ G(n,d)}[X]`: the average of `X` over the uniform perfect matching
(Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), Section 2.2, p.9). It is used with values in `ℝ` and in `ℂ`.

**Formalization Note.** When `n * d` is odd this is `0 / 0 = 0`; every statement assumes
`Even (n * d)`. -/
noncomputable def cmE {n d : ℕ} {K : Type*} [Semifield K] (X : Matching n d → K) : K :=
  (∑ M, X M) / (Fintype.card (Matching n d) : K)

/-- The probability of a property of the uniform perfect matching. -/
noncomputable def cmProb {n d : ℕ} (P : Matching n d → Prop) : ℝ :=
  (Finset.univ.filter P).card / (Fintype.card (Matching n d) : ℝ)

end AFIsingKS


