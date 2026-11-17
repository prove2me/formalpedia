-- Prove2me | Definitions.Def_RestrictedDec_Supplement_SepWitness
-- name    : RestrictedDec_Supplement_SepWitness
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:25:55.413053+00:00
-- url     : https://prove2.me/theorems/8316b960-95d5-4f69-ba3f-7e4bab60dbc5
-- title:
--   Efficiently found separating witness for $(\mathcal F,\mathcal G)$ (§3.3)
-- statement:
--   An **efficiently found separating witness** for the adjacent classes $(\mathcal F,\mathcal G)$ over $M$ is a polynomial-time machine mapping $1^\lambda$ to $(m_0(\lambda),m_1(\lambda),d^*(\lambda))$ such that
--
--   1. at **every** $\lambda$: $m_0(\lambda),m_1(\lambda)\in M_\lambda$, $|m_0(\lambda)|=|m_1(\lambda)|$, and $F(m_0(\lambda))=F(m_1(\lambda))$ for every admissible $F\in\mathcal F$;
--   2. on **infinitely many** $\lambda$: $d^*(\lambda)$ describes an admissible $G^*\in\mathcal G$ with $G^*(m_0(\lambda))\neq G^*(m_1(\lambda))$.
--
--   This is the separation condition of §3.3 used by Theorems 3 and 4.
--
--   **Formalization Note** Classes are $\lambda$-indexed families of descriptions, which covers the paper's binary-indexed classes along a uniformly computable index sequence.
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), §3.3, pp.18–19; Theorem 3, p.19

import Mathlib
import Definitions.Def_BeyondDS_tup
import Definitions.Def_RestrictedDec_Family
open QAlgorithms.Complexity
open Filter
set_option autoImplicit false

namespace RestrictedDec

namespace Supplement

/-- An **efficiently found separating witness** for the adjacent pair of classes `(𝓕, 𝓖)` over
the message space `M`: one polynomial-time machine maps `1^λ` to `tup [m₀(λ), m₁(λ), d*(λ)]` such
that
1. at every `λ`, `m₀(λ), m₁(λ) ∈ M_λ`, `|m₀(λ)| = |m₁(λ)|`, and `F(m₀(λ)) = F(m₁(λ))` for every
   admissible `F ∈ 𝓕`;
2. on infinitely many `λ`, `d*(λ)` is an admissible description of some `G* ∈ 𝓖` with
   `G*(m₀(λ)) ≠ G*(m₁(λ))`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), §3.3, pp.18–19 ("The messages
and a description of F⋆_i must be produced by a single polynomial-time algorithm from 1λ and the
binary index i. For a varying index, the two valid equal-length messages must agree under every
weaker function at all security parameters. The stronger function need distinguish them on only
infinitely many parameters. On an inactive parameter the algorithm may return two identical default
messages."); Theorem 3, p.19.

**Formalization Note.** The classes are λ-indexed families (`Family` descriptions are read at each
`λ`), which covers the paper's classes `𝓕_{i(λ)}` along a uniformly computable index sequence. -/
def SepWitness (M : ℕ → Str → Prop) (F G : Family) : Prop :=
  ∃ (w : Str → Str) (m0 m1 d : ℕ → Str), PolyTimeComputable w ∧
    (∀ lam, w (encNat lam) = BeyondDS.tup [m0 lam, m1 lam, d lam]) ∧
    (∀ lam, M lam (m0 lam) ∧ M lam (m1 lam) ∧ (m0 lam).length = (m1 lam).length ∧
      ∀ d', F.admissible lam d' = true → F.eval lam d' (some (m0 lam)) = F.eval lam d' (some (m1 lam))) ∧
    ∃ᶠ lam in atTop, G.admissible lam (d lam) = true ∧
      G.eval lam (d lam) (some (m0 lam)) ≠ G.eval lam (d lam) (some (m1 lam))

end Supplement

end RestrictedDec


