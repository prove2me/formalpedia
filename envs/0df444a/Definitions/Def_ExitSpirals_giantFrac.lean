-- Prove2me | Definitions.Def_ExitSpirals_giantFrac
-- name    : ExitSpirals_giantFrac
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:00:59.74628+00:00
-- url     : https://prove2.me/theorems/2d9e4481-a5b7-4b3a-812f-c16a1a6e1c90
-- title:
--   Corrected giant-component fraction $g(s)=1-G(1-s+sf(s))$ of a thinned network
-- statement:
--   Let $p$ be a joint degree distribution with mean $\lambda$. The **in-degree of the origin of a random link** has law
--   $$p^-_j=\sum_k\frac{k}{\lambda}\,p_{jk}$$
--   (a node is the origin of a link in proportion to its out-degree), with generating function $H(z)=\sum_jp^-_jz^j$; the in-degree marginal $\sum_kp_{jk}$ has generating function $G(z)=\sum_{j,k}p_{jk}z^j$. With $f(s)$ the smallest root of $f=H(1-s+sf)$, define
--   $$g(s)=1-G\big(1-s+s\,f(s)\big),\qquad s\in[0,1].$$
--   $g(s)$ is the asymptotic fraction of agents that receive support from the giant out-component when every node is kept independently with probability $s$: an agent is not supported when none of its in-links, thinned by $s$, leads back into the giant component.
--
--   By binomial thinning (8), $\sum_{jk}\hat p_{jk}(s)f^j=G(1-s+sf)$, so this is the function $g$ of the system (9) after the in/out correction.
--
--   **Formalization Note** The paper's (9) and Lemma 5 explore out-links, using $p^+_k=\sum_j(j/\lambda)p_{jk}$ and exponent $k$; that measures who can reach the giant component, whereas stability requires support from it. With in-degree 2 for all agents and out-degree 0 or 4 with probability $\tfrac12$, the printed formula gives $g<\tfrac12$ at $s=1$ although all agents are active. The definition uses the paper's own $p^-_j$ of p.46 and exponent $j$.
-- source:
--   Aymanns, Georg, Golub, Exit Spirals in Coupled Networked Markets, SSRN 2881814 (preprint, sha256 12000f11…6c84d2), Appendix A.2.2, p.46 (p⁻_j); Lemma 5, p.50; (8) and (9), p.51 (corrected: in-degree convention)

import Mathlib
import Definitions.Def_ExitSpirals_IsDegreeDist
import Definitions.Def_ExitSpirals_pgf

namespace ExitSpirals

/-- **In-degree law of the origin of a random link**, `p⁻_j = Σ_k (k/λ) p_{jk}`.
Aymanns, Georg, Golub, *Exit Spirals in Coupled Networked Markets*, SSRN 2881814, Appendix A.2.2,
p.46: "p⁻_{j,µ} := Σ_k (k/λ) p_{jk,µ} … This is the probability that the initial node of a randomly
chosen link in layer µ … has in-degree j." -/
noncomputable def edgeOriginIn (p : ℕ → ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑' k : ℕ, (k : ℝ) * p j k / meanDeg p

/-- In-degree marginal `Σ_k p_{jk}` of a joint degree distribution. -/
noncomputable def inLaw (p : ℕ → ℕ → ℝ) (j : ℕ) : ℝ := ∑' k : ℕ, p j k

/-- `f(s)`: the smallest solution of `f = H(1 − s + s f)` with `H(z) = Σ_j p⁻_j z^j`, the
probability that the backward exploration from a random link dies out when each node is kept
with probability `s` (Lemmas 4, 8 and (9), pp.50–53, with the in/out convention corrected). -/
noncomputable def extinctionProb (p : ℕ → ℕ → ℝ) (s : ℝ) : ℝ :=
  smallestRoot (edgeOriginIn p) s

/-- **`g(s)`, the giant-component fraction of the thinned network** (Lemma 5, p.50; (9), p.51,
corrected): `g(s) = 1 − G(1 − s + s f(s))` with `G(z) = Σ_{j,k} p_{jk} z^j = Σ_j (Σ_k p_{jk}) z^j`.
Aymanns, Georg, Golub, *Exit Spirals in Coupled Networked Markets*, SSRN 2881814.

By binomial thinning (8), `Σ_{jk} p̂_{jk}(s) f^j = G(1 − s + s f)`, so this is the `g` of (9) with
exponent `j`.

**Formalization Note.** The paper's (9) and Lemma 5 use exponent `k` (out-degree) and
`H` built from `p⁺_k = Σ_j (j/λ) p_{jk}`; that measures who can *reach* the giant component,
while stability needs support *from* it, i.e. in-links. With in-degree 2 for all agents and
out-degree 0 or 4 with probability ½, the printed formula gives `g < ½` at `s = 1` although every
agent is active (Lemma 2). The corrected version uses `p⁻_j` of p.46 and exponent `j`. -/
noncomputable def giantFrac (p : ℕ → ℕ → ℝ) (s : ℝ) : ℝ :=
  1 - pgf (inLaw p) (1 - s + s * extinctionProb p s)

end ExitSpirals


