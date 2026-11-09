-- Prove2me | Definitions.Def_SecondBestMatch_lagrangianValue
-- name    : SecondBestMatch_lagrangianValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:21:18.665062+00:00
-- url     : https://prove2.me/theorems/c93985ea-d05d-46f1-8817-9be130101ead
-- title:
--   Lagrangian value $\mathcal L_{\mathcal I}(\alpha)$
-- statement:
--   For finite-support priors and a multiplier $\alpha\ge0$, the **fixed-$\alpha$ Lagrangian value** is
--   $$
--   \mathcal L_{\mathcal I}(\alpha) := \max_{q\in\mathcal P}\big(\mathcal G(q) + \alpha\,\mathcal B(q)\big).
--   $$
--
--   **Formalization Note** Written as a real supremum over $\mathcal P$; that the maximum is attained is part of Proposition 3.3.
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Section 5.2, p.24 (inner maximum of Eq. (1), p.11)

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_SecondBestMatch_InPolytope
import Definitions.Def_SecondBestMatch_ordGFT
import Definitions.Def_SecondBestMatch_virtGFT

open MeasureTheory Set MatchingGFT.TightE

namespace SecondBestMatch

/-- The fixed-`α` Lagrangian value `ℒ_ℐ(α) := max_{q ∈ 𝒫} (𝒢(q) + α ℬ(q))` (Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §5.2, p.24;
the inner maximum of (1), p.11).

**Formalization Note** A real `sSup` over `𝒫`; Proposition 3.3 (ii) states that it is attained. -/
noncomputable def lagrangianValue {B S : Type*} [Fintype B] [Fintype S] [DecidableEq B]
    [DecidableEq S] (m : Market B S) (α : ℝ) : ℝ :=
  sSup ((fun q => ordGFT m q + α * virtGFT m q) '' {q | InPolytope m q})

end SecondBestMatch


