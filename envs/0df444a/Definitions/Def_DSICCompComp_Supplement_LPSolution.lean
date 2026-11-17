-- Prove2me | Definitions.Def_DSICCompComp_Supplement_LPSolution
-- name    : DSICCompComp_Supplement_LPSolution
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:24:08.046586+00:00
-- url     : https://prove2.me/theorems/c61e75f4-0b38-479e-8d6a-0f689d62e7df
-- title:
--   Variables $x_{ij}(v)$, $p_i(v)$ of the DSIC revenue LP
-- statement:
--   The revenue-maximization LP of Appendix C has a variable $x_{ij}(v)$, the ex-post probability that bidder $i$ receives item $j$ when the reported profile is $v$, and a variable $p_i(v)$, the ex-post price paid by bidder $i$. As in [CDW16], a bidder may also report a special type $\varnothing$ representing non-participation, so the variables are indexed by report profiles in which entries come from $\mathrm{supp}(D_i) \cup \{\varnothing\}$.
--
--   **Formalization Note** A report profile is a dependent function assigning to each bidder $i$ an element of $S_i \cup \{\varnothing\}$ (`Option`, with `none` $= \varnothing$). The page uses variables only at profiles in $\mathrm{supp}(D)$ and at $(\varnothing, v_{-i})$; the variables at profiles with two or more $\varnothing$ entries also exist here but appear in no constraint, objective or Lagrangian.
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), Appendix C, p.35 (pdf p.36)

import Mathlib
import Definitions.Def_DSICCompComp_Supplement_FiniteSetting

namespace DSICCompComp

namespace Supplement

/-- An assignment of the variables of the DSIC revenue LP of Appendix C
(Ryu–Weinberg–Xue, *The DSIC Competition Complexity of Additive Buyers over Independent Items*, STOC 2027
submission, manuscript of Nov. 3, 2026, sha256 bf61bfdb…,
Appendix C, p.35 (pdf p.36)): `x_ij(v)`, the ex-post probability that bidder `i` receives item `j`,
and `p_i(v)`, the ex-post price paid by bidder `i`, at report profiles `v` in which a bidder may also
report the special non-participation type `∅`.

**Formalization Note** A report profile is `(i : Fin n) → Option (S i)`, with `none` = `∅`. The page
has variables only at profiles in `supp(D)` and at `(∅, v_{-i})`; variables at profiles with two or
more `∅` entries also exist here but occur in no constraint, objective or Lagrangian. -/
structure LPSolution {n m : ℕ} (E : FiniteSetting n m) where
  /-- `x_ij(v)` -/
  x : ((i : Fin n) → Option (E.S i)) → Fin n → Fin m → ℝ
  /-- `p_i(v)` -/
  p : ((i : Fin n) → Option (E.S i)) → Fin n → ℝ

end Supplement

end DSICCompComp


