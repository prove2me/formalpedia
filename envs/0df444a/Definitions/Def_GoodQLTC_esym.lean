-- Prove2me | Definitions.Def_GoodQLTC_esym
-- name    : GoodQLTC_esym
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:41:40.8772+00:00
-- url     : https://prove2.me/theorems/9bc65355-1f5d-4606-bb1c-069e23bde565
-- title:
--   Elementary symmetric polynomial $\mathrm{sym}_j$
-- statement:
--   $$\mathrm{sym}_j(z_1,\dots,z_n)=\sum_{J\subseteq[n],\,|J|=j}\ \prod_{i\in J}z_i,$$ which is $0$ for $j\notin\{0,\dots,n\}$.
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), §3.1, p.13 (PDF p.16)

import Mathlib

namespace GoodQLTC

/-- The **elementary symmetric polynomial** `sym_j(z_1, …, z_n) := ∑_{J⊆[n], |J|=j} ∏_{i∈J} z_i`,
Gay–Jeronimo, arXiv:2609.20780 (held version), §3.1, p.13; it is `0` for `j ∉ {0, …, n}`. -/
def esym {n : ℕ} (z : Fin n → ℝ) (j : ℕ) : ℝ :=
  ∑ J ∈ Finset.univ.powersetCard j, ∏ i ∈ J, z i

end GoodQLTC


