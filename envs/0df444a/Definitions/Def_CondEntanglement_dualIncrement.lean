-- Prove2me | Definitions.Def_CondEntanglement_dualIncrement
-- name    : CondEntanglement_dualIncrement
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:03:40.142359+00:00
-- url     : https://prove2.me/theorems/132da59a-233f-47f2-a1ad-82ef36c73d98
-- title:
--   The $S_n$ increment $S_n(A_1A_1':\cdots:A_nA_n')-S_n(A_1':\cdots:A_n')$
-- statement:
--   Let $\omega$ be a state on $n$ paired systems $A_1A_1',\dots,A_nA_n'$, party $i$ holding $A_iA_i'$. With $S$ the von Neumann entropy and
--
--   $$
--   S_n(X_1:\cdots:X_n)=\sum_{i=1}^n S(X_1\cdots X_{i-1}X_{i+1}\cdots X_n)-(n-1)\,S(X_1\cdots X_n)
--   $$
--
--   the dual multipartite mutual information, the **$S_n$ increment** of $\omega$ is
--
--   $$
--   \Delta S_n(\omega)=S_n(A_1A_1':\cdots:A_nA_n')_\omega-S_n(A_1':\cdots:A_n')_\omega ,
--   $$
--
--   where the second term is evaluated on the marginal $\omega_{A_1'\cdots A_n'}$. It is the quantity whose infimum over extensions defines the conditional entanglement $C_S$ (p.4).
--
--   **Formalization Note** $S_n$ is the published `info .dual · (singleParties n) ∅`, which also subtracts the entropy of the empty marginal, a $1\times1$ matrix $(\operatorname{Tr}M)$; that term is $0$ on states, so on states this is the page's $S_n$. Entropies are in bits (`QAlgorithms.vnEntropy`); the page leaves the base unstated. The primed systems are arbitrary finite types; the definition is total on matrices and every theorem assumes $\omega$ is a density matrix.
-- source:
--   Yang–Horodecki–Wang, Conditional Entanglement, arXiv:quant-ph/0701149v3, definition of C_S and S_n, p.4

import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P33

namespace CondEntanglement

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Yang–Horodecki–Wang, *Conditional Entanglement*, arXiv:quant-ph/0701149v3, p.4: the quantity
inside the infimum defining `C_S`,
"Sₙ(A₁A′₁ : · · · : AₙA′ₙ) − Sₙ(A′₁ : · · · : A′ₙ)", where
"Sₙ = Σᵢ S(A₁ · · · Aᵢ₋₁Aᵢ₊₁ · · · Aₙ) − (n − 1)S(A₁ · · · Aₙ)" is the dual multipartite mutual
information of the n parties.

The state `ω` lives on `n` paired registers: party `i` holds `Aᵢ = D i` and the primed register
`A′ᵢ = F i`. The first term is `Sₙ` of `ω` with party `i` taken to be the pair `AᵢA′ᵢ`; the second
is `Sₙ` of the primed marginal `ω_{A′₁⋯A′ₙ}` (every `Aᵢ` traced out).

**Formalization Note.** `Sₙ` is the published `info .dual · (singleParties n) ∅`, which unfolds to
`Σᵢ S(all parties but i) − (n − 1)·S(all parties) − S(∅)`; the last term is the entropy of the
1 × 1 marginal `(Tr M)` and vanishes on density matrices, so for states it is the page's `Sₙ`.
`S` is the published `QAlgorithms.vnEntropy`, in bits; the paper leaves the base unstated and
`Sₙ` is a single multiple of `log`, so every base gives the same statements. For `n ≤ 1`, `Sₙ ≡ 0`
on states. The definition is total; the theorems assume `ω` is a density matrix. Party `i` of
the product index `(i : Fin n) → D i × F i` is the pair `AᵢA′ᵢ`, the published
`unprimedMarginal`/`primedMarginal` convention. -/
noncomputable def dualIncrement {n : ℕ} {D F : Fin n → Type} [∀ i, Fintype (D i)]
    [∀ i, Fintype (F i)]
    (ω : Matrix (RegisterBasis (fun i => D i × F i)) (RegisterBasis (fun i => D i × F i)) ℂ) :
    ℝ :=
  info .dual ω (singleParties n) ∅ - info .dual (primedMarginal ω) (singleParties n) ∅

end CondEntanglement


