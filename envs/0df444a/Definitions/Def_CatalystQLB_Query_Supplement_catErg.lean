-- Prove2me | Definitions.Def_CatalystQLB_Query_Supplement_catErg
-- name    : CatalystQLB_Query_Supplement_catErg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:00:03.799849+00:00
-- url     : https://prove2.me/theorems/b4855590-d92d-4f78-af43-94d45d6a1927
-- title:
--   Catalytic ergotropy $\mathsf{cat}\text{-}\mathrm{erg}_{\rho,H}=\max_{\ell\ge0}\mathsf{cat}\text{-}\mathrm{erg}_{\rho,H}(\ell)$
-- statement:
--   With arbitrarily many catalyst qubits, the **catalytic ergotropy** is
--   $$\mathsf{cat}\text{-}\mathrm{erg}_{\rho,H} := \max_{\ell\ge0}\ \mathsf{cat}\text{-}\mathrm{erg}_{\rho,H}(\ell).$$
--
--   **Formalization Note** The real supremum over all $\ell\in\mathbb N$ ($\ell=0$ included). For density $\rho$ and Hermitian $H$ every term lies in $[-2\|H\|,2\|H\|]$, so the supremum is a genuine bound and not a default value.
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), Definition 84, p.53 (PDF 56)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_CatalystQLB_Query_Supplement_catErgL

namespace CatalystQLB.Query.Supplement

open QAlgorithms

/-- **Catalytic ergotropy with arbitrarily many catalysts**, `cat-erg_{ρ,H} := max_{ℓ ≥ 0}
cat-erg_{ρ,H}(ℓ)` (Arora, Chakraborty, Cojocaru, Saminathan, Singh, *Computational Work
Extraction: The Complexity of Catalysts*, arXiv:2609.40323 (version of 2026-11-03),
Definition 84, p.53 (PDF 56)).

**Formalization Note** The real supremum `⨆` over all `ℓ ∈ ℕ` (`ℓ = 0` included) of `catErgL`.
For a density `ρ` and Hermitian `H` every `catErgL n ℓ ρ H` lies in `[−2‖H‖, 2‖H‖]`, so the
family is bounded and `⨆` is the paper's maximum (supremum); no junk value occurs. -/
noncomputable def catErg (n : ℕ) (ρ H : Matrix (Qubits n) (Qubits n) ℂ) : ℝ :=
  ⨆ ℓ : ℕ, catErgL n ℓ ρ H

end CatalystQLB.Query.Supplement


