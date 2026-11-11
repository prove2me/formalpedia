-- Prove2me | Definitions.Def_MIBF_Balanced_BellmanDifference
-- name    : MIBF_Balanced_BellmanDifference
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:57:26.016064+00:00
-- url     : https://prove2.me/theorems/ab05c638-15b6-4231-962a-be81f33db8b0
-- title:
--   The Bellman difference $R_\phi(M)$ of the balanced candidate $\phi$
-- statement:
--   Let $\phi$ be the balanced candidate of the published `GeneralCK_bellman` (bits): with $\iota$ the lower inverse of the binary entropy $H$ on $[0,\tfrac12]$, $J(t)=\log_2\frac{1-t}{t}$, $\eta(e)=(1-2\iota(e))\,J(\iota(e))$ (with $\eta(1)=0$), and $F(s,e)=s\,J(v)$ where $v\in(0,\tfrac12)$ solves $s\,H(v)=e\,(1-2v)$ (and $F(0,e)=0$),
--   $$\phi(m,e)=\eta(e)-F(|1-2m|,e),\qquad 0<m<1,\ 0<e\le H(m).$$
--   It vanishes at the entropy cap $e=H(m)$ and equals $\eta(e)$ at $m=\tfrac12$.
--
--   For a four-moment tuple $M=(\mu_u,\mu_w,e_u,e_w)$ the **Bellman difference** of $\phi$ is
--   $$R_\phi(M)=\phi\Bigl(\frac{\mu_u+\mu_w}{2},\frac{e_u+e_w}{2}\Bigr)-\tfrac12\,\phi(\mu_u,e_u)-\tfrac12\,\phi(\mu_w,e_w).$$
--   On tuples with $0<\mu_u,\mu_w<1$ and $e_u,e_w>0$ all three arguments lie in the domain of $\phi$: concavity of $H$ gives $\frac{e_u+e_w}{2}\le H\bigl(\frac{\mu_u+\mu_w}{2}\bigr)$. $R_\phi(M)$ is the amount by which $\phi$ fails to be midpoint-concave along the edge; the balanced Bellman inequality asserts that the edge value pays for it.
--
--   **Formalization Note** `GeneralCK.phi` is a total real function; off the domain above (e.g. at $e=0$, where the paper sets $\phi(m,0)=+\infty$) its value is a junk value. Every statement of this mission evaluates $R_\phi$ only at interior means and positive entropies, where it is the paper's $\phi$. Units are bits; in nats every term scales by $\ln 2$.
-- source:
--   Chen, Gohari, Javanmard, Lin, Mirrokni, Nair, Woodruff, A Proof of the Most Informative Boolean Function Conjecture, arXiv:2609.24931 (held version, sha256 35793b82…1f9f), p. 7, eqs. (6)–(8), p. 8, eq. (13); [Full] = arXiv:2609.24931v2 reproduced in the held PDF, [Full] pp. 10–11 (PDF 32–33), eqs. (11), (12), (14)

import Mathlib
import Definitions.Def_GeneralCK_bellman

namespace MIBF.Balanced

/-- The Bellman difference of the balanced candidate `ϕ = GeneralCK.phi` (bits) at the
tuple `(mu, mw, eu, ew)`:
`R_ϕ = ϕ((mu + mw)/2, (eu + ew)/2) - ϕ(mu, eu)/2 - ϕ(mw, ew)/2`. -/
noncomputable def Rphi (mu mw eu ew : ℝ) : ℝ :=
  GeneralCK.phi ((mu + mw) / 2) ((eu + ew) / 2)
    - GeneralCK.phi mu eu / 2 - GeneralCK.phi mw ew / 2

end MIBF.Balanced


