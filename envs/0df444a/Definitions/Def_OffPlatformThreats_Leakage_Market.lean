-- Prove2me | Definitions.Def_OffPlatformThreats_Leakage_Market
-- name    : OffPlatformThreats_Leakage_Market
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:28:42.770674+00:00
-- url     : https://prove2.me/theorems/111e9e6d-d5d5-444a-bd5d-e216bad86a58
-- title:
--   Parameters of the on-demand service model (one provider type)
-- statement:
--   The model of He, Savin, Goh and Teo has a platform, customers, and service providers of quality type $j \in \{h, l\}$. For one provider type $j$, the record collects:
--
--   1. $c$, a customer's cost of waiting per unit time;
--   2. $\phi$, the heavy-traffic constant $\phi = (1 + c_s^2)/2$ of the waiting-time formula, where $c_s^2$ is the squared coefficient of variation of service durations;
--   3. $\mu$, the service rate of every provider;
--   4. $R_o$, the counterparty risk: the extra cost a customer incurs when transacting off the platform;
--   5. $v = v^j$, the customers' value of service by a $j$-type provider;
--   6. $K = K^j$, the opportunity cost per unit time of a $j$-type provider's outside option;
--   7. $N = N^j \in \mathbb{N}$, the number of $j$-type providers.
--
--   The parameters $c, \phi, \mu, R_o$ are shared by both types; every object the paper defines for type $j$ depends only on these and on $(v^j, K^j, N^j)$.
--
--   **Formalization Note** No sign conditions are bundled: each theorem states the ones it uses.
-- source:
--   He, Savin, Goh, Teo, Off-Platform Threats in On-Demand Services, SSRN 3550646 (2021-03-25 version), §3.1–3.2, pp. 9–12

import Mathlib

namespace OffPlatformThreats.Leakage

/-- **The parameters of the model, for one provider type `j`.**
He, Savin, Goh & Teo, *Off-Platform Threats in On-Demand Services*, SSRN 3550646 (2021-03-25
version), §3.1–3.2, pp. 10–12 (unnumbered).

* `c` — a customer's cost of waiting per unit time ((4), p. 11);
* `phi` — the heavy-traffic constant `φ = (1 + c_s²)/2` of (2), p. 11;
* `mu` — the service rate of every provider (p. 10);
* `Ro` — the counterparty risk, the extra cost a customer bears off the platform (p. 11);
* `v` — the customers' value `v^j` of service by a `j`-type provider (p. 9);
* `K` — the opportunity cost `K^j` per unit time of a `j`-type provider's outside option (p. 12);
* `N` — the total number `N^j` of `j`-type providers (p. 10).

**Formalization Note.** The paper has two types `j = h, l` sharing `c, φ, µ, Ro`; every object
it defines for type `j` (demand (5), utilities (7), (10), Definition 1 per type, (21), (23), (25))
involves only the shared parameters and those of type `j`. A record of this structure is one
type together with the shared parameters. No sign conditions are bundled here: each theorem
states the ones it uses. -/
structure Market where
  c : ℝ
  phi : ℝ
  mu : ℝ
  Ro : ℝ
  v : ℝ
  K : ℝ
  N : ℕ

end OffPlatformThreats.Leakage


