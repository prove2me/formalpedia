-- Prove2me | Definitions.Def_NearOptOWF_famHprime
-- name    : NearOptOWF_famHprime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:15:31.302307+00:00
-- url     : https://prove2.me/theorems/52f66d38-36d4-434a-987f-9b29e0f4e4f2
-- title:
--   Hybrid family $\mathcal H' = \{i\mathcal O(G \circ H)\}$, $N = 10n$
-- statement:
--   The hybrid family
--   $$
--   \mathcal H' = \{\, i\mathcal O(G \circ H) : G : \{0,1\}^N \to \{0,1\}^m,\ H : \{0,1\}^n \to \{0,1\}^N \,\}, \qquad N = 10n,
--   $$
--   where $G$ and $H$ are puncturable PRFs at security parameter $\lambda(n)$. At input length $n$, sample keys of $G$ and $H$ and coins of $i\mathcal O$, and output $i\mathcal O(1^{\lambda(n)}, \mathrm{pad}_{S(n)}(G_{k_1} \circ H_{k_2}); \rho)$.
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), §4.2, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_NearOptOWF_FunFamily
import Definitions.Def_NearOptOWF_obfPad
import Definitions.Def_NearOptOWF_comp
import Definitions.Def_NearOptOWF_PPRF

namespace NearOptOWF

open LaconicBarrier

/-- The hybrid family **`H′ = {iO(G ∘ H) : G : {0,1}^N → {0,1}ᵐ, H : {0,1}ⁿ → {0,1}^N}`, `N = 10n`**
(Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), §4.2, p.14 (PDF p.16)): at input length `n`, sample a key `k₁` of `G` at
`(λ(n), 10n, m(n))`, a key `k₂` of `H` at `(λ(n), n, 10n)` and coins `ρ` of `iO`, and output
`iO(1^{λ(n)}, padTo S(n) (G_{k₁} ∘ H_{k₂}); ρ)`.

**Formalization Note** The padding to the common size `S(n)` is the paper's (pp.11–12). -/
def famHprime (O : MIOScheme) (G H : PPRF) (lam S m : ℕ → ℕ) : FunFamily m where
  coins n := G.keyLen (lam n) (10 * n) (m n) + H.keyLen (lam n) n (10 * n) + O.coins (lam n) n (S n)
  samp n ρ := obfPad O (lam n) n (S n)
    (comp (G.circ (lam n) (10 * n) (m n) (fun i => ρ (Fin.castAdd _ (Fin.castAdd _ i))))
      (H.circ (lam n) n (10 * n) (fun j => ρ (Fin.castAdd _ (Fin.natAdd _ j)))))
    (fun l => ρ (Fin.natAdd _ l))

end NearOptOWF


