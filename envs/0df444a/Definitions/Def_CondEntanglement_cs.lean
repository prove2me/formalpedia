-- Prove2me | Definitions.Def_CondEntanglement_cs
-- name    : CondEntanglement_cs
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:05:31.812149+00:00
-- url     : https://prove2.me/theorems/935257cc-4735-4fa8-9df9-c902d0d5ed34
-- title:
--   Conditional entanglement $C_S$ of the dual multipartite mutual information
-- statement:
--   For an $n$-party state $\rho$ on $A_1\cdots A_n$, the **conditional entanglement of the dual multipartite mutual information** is
--
--   $$
--   C_S(\rho)=\inf\{S_n(A_1A_1':\cdots:A_nA_n')-S_n(A_1':\cdots:A_n')\},
--   $$
--
--   the infimum over all extensions $\rho_{A_1A_1'\cdots A_nA_n'}$ of $\rho$, where $S_n=\sum_i S(A_1\cdots A_{i-1}A_{i+1}\cdots A_n)-(n-1)S(A_1\cdots A_n)$. It is the second of the two multipartite versions of the conditional entanglement of mutual information on p.4; the first, $C_I$, uses $I_n=\sum_i S(A_i)-S(A_1\cdots A_n)$ instead.
--
--   **Formalization Note** The infimum is the real `sInf` of `CondEntanglement.csValues ρ`. For a state the set is nonempty (one-dimensional primed systems give an extension) and bounded below by $0$ (milestone `dualIncrement_nonneg`), so it is the true infimum; no theorem evaluates `cs` off density matrices, where `sInf` would return the junk value $0$. There is no factor $\tfrac12$, as on p.4. Entropies in bits.
-- source:
--   Yang–Horodecki–Wang, Conditional Entanglement, arXiv:quant-ph/0701149v3, definition of C_S, p.4

import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33
import Definitions.Def_CondEntanglement_csValues

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P33

namespace CondEntanglement

/-- Yang–Horodecki–Wang, *Conditional Entanglement*, arXiv:quant-ph/0701149v3, p.4: the
conditional entanglement of the dual multipartite mutual information,
"C_S = inf{Sₙ(A₁A′₁ : · · · : AₙA′ₙ) − Sₙ(A′₁ : · · · : A′ₙ)}", with
"Sₙ = Σᵢ S(A₁ · · · Aᵢ₋₁Aᵢ₊₁ · · · Aₙ) − (n − 1)S(A₁ · · · Aₙ)", the infimum over all extensions
`ρ_{A₁A′₁⋯AₙA′ₙ}` of `ρ_{A₁⋯Aₙ}`.

**Formalization Note.** The infimum is the real `sInf` of `csValues ρ`. For a density matrix `ρ`
the set is nonempty (one-dimensional primed registers give an extension) and bounded below by `0`
(milestone `dualIncrement_nonneg`), so `sInf` is the true infimum; the theorems only evaluate `cs`
at density matrices, never at the junk value `0` that `sInf` returns on an empty or unbounded set.
No factor `1/2` (p.4 defines `C_S` as a bare infimum). Entropies in bits. -/
noncomputable def cs {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) : ℝ :=
  sInf (csValues ρ)

end CondEntanglement


