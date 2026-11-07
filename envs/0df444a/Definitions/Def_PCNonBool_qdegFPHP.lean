-- Prove2me | Definitions.Def_PCNonBool_qdegFPHP
-- name    : PCNonBool_qdegFPHP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:31:23.353832+00:00
-- url     : https://prove2.me/theorems/ac1d42c2-d209-416e-9b9a-b9aa28352e0a
-- title:
--   Quadratic degree $\mathrm{Qdeg}(m_1,m_2)$ for FPHP$(G)$
-- statement:
--   Definition 4.9 instantiated to FPHP$(G)$: the **Q-support** of a monomial pair $(m_1,m_2)$ is the set of pigeons $i$ such that $(m_1)_{X_i}\cdot(m_2)_{X_i}^{-1}$ is not constant modulo the ideal $\langle A_i\rangle$, where $(m)_{X_i}$ is the part of $m$ in the variables of pigeon $i$, and a polynomial $q$ is *constant modulo $I$* if $q-a\in I$ for some $a\in\mathbb F$. The **quadratic degree** $\mathrm{Qdeg}(m_1,m_2)$ is the size of the Q-support.
--
--   **Formalization Note** Since $x^2-1\in A_i$, the inverse of a monomial in $X_i$ is congruent to the monomial itself, so the product $(m_1m_2)_{X_i}$ is used.
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Definition 4.9 (Q-support, Q-degree), instantiated in §5.1, pp.15, 27 (PDF pp.18, 30)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_Var
import Definitions.Def_PCNonBool_localAxioms

namespace PCNonBool

/-- The quadratic degree (Q-degree) of a monomial pair for FPHP(G): Definition 4.9
(Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), p.15 (PDF p.18)) instantiated as in §5.1 (p.27): all variables are non-singular,
there are no extension variables, and the groups are `X_i = {x_{i,j} : j ∈ N(i)}`. So
`Qsupp(m₁, m₂)` is the set of pigeons `i` for which `(m₁)_{X_i} · (m₂)_{X_i}⁻¹` is not constant
modulo `⟨A_i⟩`, and `Qdeg = |Qsupp|`.

**Formalization Note** Modulo `x² - 1 ∈ A_i`, the inverse of a monomial in `X_i` is the monomial
itself, so `(m₁)_{X_i} (m₂)_{X_i}⁻¹` is constant modulo `⟨A_i⟩` iff `(m₁ m₂)_{X_i}` is; the latter
is used. "Constant modulo `I`" is `∃ a ∈ F, m - a ∈ I` (proof of Proposition 5.6). -/
noncomputable def qdegFPHP (F : Type*) [Field F] {U V : Type*} [Fintype U] [Fintype V]
    (G : BipGraph U V) (m₁ m₂ : Var G →₀ ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i : U => ¬ ∃ a : F,
    MvPolynomial.monomial ((m₁ + m₂).filter (fun e => e.1.1 = i)) (1 : F) - MvPolynomial.C a ∈
      Ideal.span (localAxioms G i))).card

end PCNonBool


