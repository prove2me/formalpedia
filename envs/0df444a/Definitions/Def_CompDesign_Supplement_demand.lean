-- Prove2me | Definitions.Def_CompDesign_Supplement_demand
-- name    : CompDesign_Supplement_demand
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T20:51:21.947301+00:00
-- url     : https://prove2.me/theorems/48d6cf94-f70b-4997-818f-8eda731ea45a
-- title:
--   $p_k$ and the demand $D_p(t)$ (§7.1.3)
-- statement:
--   For a rule $p:2^A\to[0,1]$ on $A=\{1,\dots,m\}$ let $p_k=\max\{p(S):|S|=k\}$, $k=0,\dots,m$ ($p_0=p(\emptyset)$). Under the uniform cost $c_e=t$ and the value $v(S)=|S|$, the agent's **demand** is
--   $$D_p(t)\in\arg\max_{k\in\{0,\dots,m\}}\{p_k-tk\},$$
--   with ties broken in favor of the largest $k$ (the platform-favoring choice). $D_p(t)$ is the value $|S|$ of the agent's platform-favoring best response; it is the quantity of Theorem 7.4.
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), §7.1.3, p.56 (PDF 59)

import Mathlib

namespace CompDesign.Supplement

open Classical in
/-- `p_k = max {p(S) : |S| = k}` of §7.1.3, p.56 (PDF 59), of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…), for a rule
`p : 2^A → [0, 1]` on `A = Fin m` and `k = 0, …, m` (with `p_0 = p(∅)`).

**Formalization Note.** For `k ≤ m` the set of `k`-subsets is nonempty; the value `0` for `k > m`
is never used. -/
noncomputable def maxPayCard {m : ℕ} (p : Finset (Fin m) → ℝ) (k : ℕ) : ℝ :=
  if h : (Finset.powersetCard k (Finset.univ : Finset (Fin m))).Nonempty then
    (Finset.powersetCard k (Finset.univ : Finset (Fin m))).sup' h p
  else 0

open Classical in
/-- The demand `D_p(t)` of §7.1.3, p.56 (PDF 59), of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…): under the uniform cost `c_e = t` and the
value `v(S) = |S|`, the agent chooses a cardinality in `argmax_{k∈{0,…,m}} {p_k − t k}`, ties broken
in favor of the largest `k` (the platform-favoring choice). It is the value `|S|` of the agent's
platform-favoring best response. -/
noncomputable def demand {m : ℕ} (p : Finset (Fin m) → ℝ) (t : ℝ) : ℕ :=
  ((Finset.range (m + 1)).filter fun k =>
    ∀ j ∈ Finset.range (m + 1), maxPayCard p j - t * j ≤ maxPayCard p k - t * k).sup id

end CompDesign.Supplement


