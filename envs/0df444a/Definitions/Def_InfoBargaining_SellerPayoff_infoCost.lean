-- Prove2me | Definitions.Def_InfoBargaining_SellerPayoff_infoCost
-- name    : InfoBargaining_SellerPayoff_infoCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:13:31.536987+00:00
-- url     : https://prove2.me/theorems/bb67d0e6-00b0-42be-b7ba-bebd8ce8fc5e
-- title:
--   Linear information cost $k(\alpha)=\bar k(\alpha-\underline\alpha)/(\bar\alpha-\underline\alpha)$
-- statement:
--   The buyer's cost of acquiring a signal of informativeness $\alpha$ is linear,
--
--   $$
--   k(\alpha)=\bar k\,\frac{\alpha-\underline\alpha}{\bar\alpha-\underline\alpha},
--   $$
--
--   so that $k(\underline\alpha)=0$ and $k(\bar\alpha)=\bar k>0$, as required on p. 8.
--
--   **Formalization Note** The formula divides by $\bar\alpha-\underline\alpha$; every statement assumes $\underline\alpha<\bar\alpha$.
-- source:
--   Guo, Gathering Information before Negotiation, SSRN 3930651 (manuscript of 15 Feb 2022), §3.2, unnumbered, p. 13 ("linear information-acquisition cost k(α) = k̄(α − α̲)/(ᾱ − α̲)"); §2, p. 8

import Mathlib

namespace InfoBargaining.SellerPayoff

/-- **The linear information-acquisition cost `k(α)`.**
Guo, *Gathering Information before Negotiation*, SSRN 3930651 (manuscript of 15 Feb 2022),
§3.2, unnumbered, p. 13: "we consider linear information-acquisition cost
k(α) = k̄(α − α̲)/(ᾱ − α̲)"; with "k̲ ≡ k(α̲) = 0 and k̄ ≡ k(ᾱ) > 0" (§2, p. 8).

`infoCost α̲ ᾱ k̄ α = k̄ (α − α̲)/(ᾱ − α̲)`.

**Formalization Note.** Divides by `ᾱ − α̲`; every statement assumes `α̲ < ᾱ` (p. 8). -/
noncomputable def infoCost (αl αh kbar α : ℝ) : ℝ := kbar * (α - αl) / (αh - αl)

end InfoBargaining.SellerPayoff


