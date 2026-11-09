-- Prove2me | Definitions.Def_DerandLDT_localAgr
-- name    : DerandLDT_localAgr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T23:06:51.390016+00:00
-- url     : https://prove2.me/theorems/2be77d10-23d5-4cc9-98c4-441b479eb60f
-- title:
--   Local agreement of a line table along the directions $U$
-- statement:
--   Let $\mathbb F$ be a finite field, $f : \mathbb F^2 \to \mathbb F$ a point table, and $U$ a finite set of directions. A **line table** of degree $k$ assigns to every affine line $L$ a parameterization $t \mapsto a_L + t u_L$ and a univariate polynomial $p_L \in \mathbb F[t]$ of degree at most $k$. An incidence $(x, L)$ with $x \in L$ is **accepted** when $p_L(t) = f(x)$ at the parameter $t$ of $x$.
--
--   The **local agreement** of the table along $U$ is the fraction of accepted incidences among all incidences on the lines along $U$:
--   $$
--   \mathrm{localAgr}(f, P, U) = \frac{\#\{(x, L) : L \in \mathcal L(U),\ x \in L,\ p_L(x) = f(x)\}}{\#\{(x, L) : L \in \mathcal L(U),\ x \in L\}} .
--   $$
--   Since every line has exactly $q$ points, this is $\mathbb E_{L \in \mathcal L(U)}[\mathrm{agree}(f|_L, p_L)]$. Maximizing over tables gives the quantity $\mathbb E_{\ell \in \mathcal L}[\mathrm{agree}(f|_\ell, \mathcal P_{k,1})]$ of the paper: the maximum agreement on each line is attained by some polynomial of degree at most $k$, and the agreement does not depend on how the line is parameterized. In Section 6 the paper uses the same quantity as $|E|/|E^*|$ for the points-vs-lines incidence graph.
--
--   **Formalization Note** The table is the published `LineVsPoint.LineTable F 2 k` and acceptance is `LineVsPoint.Accepted`. If there is no line along $U$, the value is $0/0 = 0$.
-- source:
--   Harsha–Kopparty–Kumar–Saptharishi–Sudan, On derandomizing the line-point low-degree test, STOC 2027 submission (manuscript sha256 d57e7d6f…80df), Theorem 1.2, p.5 (E_{ℓ∈𝓛}[agree(f|ℓ, P_{k,1})], footnote 1, p.3) and Section 6, pp.24–25 ("E_{ℓ∈𝓛}[agree(f|ℓ, P_{k,1})] ≥ ε iff |E| ≥ ε|E*|")

import Definitions.Def_DerandLDT_linesAlong
import Definitions.Def_LineVsPoint_LineTable

set_option autoImplicit false

namespace DerandLDT

open Classical in
/-- **Local agreement of a line table along a set of directions**: the fraction of incidences
`(x, L)` with `L` a line along `U` and `x ∈ L` that are accepted, i.e. at which the line
polynomial `p_L` of the table agrees with the point table `f`. Harsha, Kopparty, Kumar,
Saptharishi, Sudan, *On derandomizing the line-point low-degree test*, STOC 2027 submission
manuscript (sha256 d57e7d6f…80df), Theorem 1.2, p.5, and Section 6, pp.24–25: the edge set
`E = {(a, ℓ) | a ∈ ℓ, P_ℓ(a) = f(a)}` of the points-vs-lines incidence graph, with
"`E_{ℓ∈𝓛}[agree(f|ℓ, P_{k,1})] ≥ ε` iff `|E| ≥ ε|E*|`" (p.25).

**Formalization Note.** The value is `|E| / |E*|`, where `E*` is the set of incidences on the
lines of `linesAlong U` and `E ⊆ E*` the accepted ones (`LineVsPoint.Accepted`). Every line has
exactly `q` points, so this is the average over the lines along `U` of the agreement of `f|_ℓ`
with the table's polynomial `p_ℓ`; maximizing over tables gives the paper's average of
per-line maxima `E_ℓ[agree(f|ℓ, P_{k,1})]`. When there is no line along `U` the value is
`0 / 0 = 0`. -/
noncomputable def localAgr {F : Type*} [Field F] [Fintype F] {k : ℕ} (f : (Fin 2 → F) → F)
    (P : LineVsPoint.LineTable F 2 k) (U : Finset (Submodule F (Fin 2 → F))) : ℝ :=
  ((Finset.univ.filter fun xL : (Fin 2 → F) × LineVsPoint.Line F 2 =>
      xL.2 ∈ linesAlong U ∧ LineVsPoint.Accepted f P xL.1 xL.2).card : ℝ) /
    ((Finset.univ.filter fun xL : (Fin 2 → F) × LineVsPoint.Line F 2 =>
      xL.2 ∈ linesAlong U ∧ xL.1 ∈ xL.2.carrier).card : ℝ)

end DerandLDT


