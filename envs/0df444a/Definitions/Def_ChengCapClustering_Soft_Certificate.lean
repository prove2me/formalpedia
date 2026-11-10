-- Prove2me | Definitions.Def_ChengCapClustering_Soft_Certificate
-- name    : ChengCapClustering_Soft_Certificate
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T01:51:08.410927+00:00
-- url     : https://prove2.me/theorems/7a0117f0-5e25-40b1-a791-161f9ad72159
-- title:
--   $z$-certificates and the Euclidean constant $\beta^*_z$
-- statement:
--   §5.3.1, eq. (13) (printed p. 26): $(u,g,v)\in\mathbb R^3$ is a **$z$-certificate** if $|1+t|^z\le u+gt+v|t|^z$ for all $t\in\mathbb R$. **$\beta^*_z$** is the smallest value of $u+2^zv$ over all $z$-certificates; it is defined as the infimum of this set, which for $z\ge1$ is nonempty (the triangle certificate $(3^{z-1},0,(3/2)^{z-1})$) and bounded below, and is attained (Appendix A).
-- source:
--   Cheng, Mo, Ding 2026, Constant-Factor Approximation for Capacitated Clustering in Low Dimension with (1+ε)k Centers, arXiv:2610.40625 (held manuscript SHA-256 9d298191e7086ee0bbea53e5a3e4e9b0fe88c438ed58257f01f3c524a8ac4edb; arXiv version suffix unresolved, citation hold), §5.3.1, eq. (13), printed p. 26 / PDF p. 28; Appendix A, printed p. 45 / PDF p. 47

import Mathlib

namespace ChengCapClustering.Soft

/-!
# z-certificates and the Euclidean constant β*_z

Cheng, Mo, Ding, arXiv:2610.40625 (held manuscript SHA-256 9d298191…), §5.3.1, eq. (13)
(printed p. 26 / PDF p. 28): "(u, g, v) ∈ ℝ³ [is] a z-certificate if |1 + t|^z ≤ u + gt + v|t|^z for
all t ∈ ℝ"; "Let β*_z be the smallest value of u + 2^z v over all z-certificates".

**Formalization Note.** `betaStar z` is the real infimum of `u + 2^z v` over all `z`-certificates.
For `z ≥ 1` the set is nonempty (`(3^{z−1}, 0, (3/2)^{z−1})` is a certificate by convexity) and
bounded below by `1` (the inequality at `t = 0` gives `u ≥ 1`, and `v ≥ 0` follows by letting
`t → ∞`), so the infimum is the true one; Appendix A (printed p. 45) shows that it is attained,
which is the source's "smallest value". -/

/-- Eq. (13): `(u, g, v)` is a `z`-certificate. -/
def IsCertificate (z u g v : ℝ) : Prop :=
  ∀ t : ℝ, |1 + t| ^ z ≤ u + g * t + v * |t| ^ z

/-- `β*_z`: the infimum (attained, Appendix A) of `u + 2^z v` over all `z`-certificates. -/
noncomputable def betaStar (z : ℝ) : ℝ :=
  sInf {β : ℝ | ∃ u g v : ℝ, IsCertificate z u g v ∧ β = u + (2 : ℝ) ^ z * v}

end ChengCapClustering.Soft


