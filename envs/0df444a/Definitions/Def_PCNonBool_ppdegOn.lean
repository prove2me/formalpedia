-- Prove2me | Definitions.Def_PCNonBool_ppdegOn
-- name    : PCNonBool_ppdegOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:31:20.895793+00:00
-- url     : https://prove2.me/theorems/990188b0-e59f-4fbb-ac89-9efa93ccaffc
-- title:
--   Pairwise pigeon degree $\mathrm{ppdeg}(m_0,m_1)$
-- statement:
--   The **parity axioms** of FPHP$(G)$ are $\prod_{j\in N(i)}x_{i,j}+1$, $i\in U$. For a pair of monomials $(m_0,m_1)$, the **pairwise pigeon degree** is
--   $$\mathrm{ppdeg}(m_0,m_1)=\mathrm{pdeg}\bigl(m_0m_1 \bmod \langle \mathrm{PA}\cup\{x_{i,j}^2-1\}\rangle\bigr),$$
--   the number of pigeons mentioned by the reduced product. Concretely, with $H_i$ the set of holes of pigeon $i$ occurring to an odd power in $m_0m_1$, pigeon $i$ is counted if and only if $\emptyset\ne H_i\ne N(i)$.
--
--   Here the definition is taken in an induced subgraph $G[U_a\sqcup V_a]$: only pigeons of $U_a$ are counted, and holes are taken in $V_a$ (so the parity axiom of $i$ is $\prod_{j\in N(i)\cap V_a}x_{i,j}+1$). The pair is unordered.
--
--   **Formalization Note** Definition 5.5 names "the unique monomial with minimum degree" in the class of $m_0m_1$; it is not unique when $|H_i|=|N(i)|/2$, but whether $i$ is mentioned does not depend on the representative, and that is what is counted. When some pigeon has no hole, $\langle\mathrm{PA}\cup\{x^2-1\}\rangle$ is the unit ideal; the pigeon-by-pigeon count used here is then still the quadratic degree of Definition 4.9.
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Definition 5.5 (pairwise pigeon degree), p.27 (PDF p.30)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_nbrOn
import Definitions.Def_PCNonBool_Var
import Definitions.Def_PCNonBool_oddHolesOn

namespace PCNonBool

/-- The pairwise pigeon degree of an unordered pair of monomials `(m₀, m₁)` in the instance
`G[Ua ⊔ Va]` (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Definition 5.5, p.27 (PDF p.30)): `pdeg(m₀ m₁ mod ⟨PA ∪ {x² - 1}⟩)`,
the number of pigeons `i ∈ Ua` mentioned by the reduced product. Pigeon `i` is mentioned iff the
set of its holes in `Va` occurring in `m₀ m₁` to an odd power is neither empty nor all of
`N(i) ∩ Va`.

**Formalization Note** Definition 5.5 speaks of "the unique monomial with minimum degree" in the
class of `m₀ m₁`. That monomial is not unique when exactly half of a pigeon's holes are odd (`H`
and `N(i) \ H` have the same size); whether pigeon `i` is mentioned is the same for every
representative, and that is what is counted here. If some pigeon has no hole at all, the ideal
`⟨PA ∪ {x² - 1}⟩` contains `2` and is the unit ideal (characteristic ≠ 2); this definition
still counts pigeons pigeon by pigeon, which is the Q-degree of Definition 4.9 (Proposition 5.6).
`(Ua, Va) = (univ, univ)` is the paper's FPHP(G); `(U_ℓ, V_ℓ)` is Algorithm 1's FPHP(G_ℓ), whose
parity axioms are `∏_{j ∈ N(i) ∩ V_ℓ} x_{i,j} + 1`. -/
noncomputable def ppdegOn {U V : Type*} [DecidableEq V] (G : BipGraph U V) (Ua : Finset U)
    (Va : Finset V) : Sym2 (Var G →₀ ℕ) → ℕ :=
  Sym2.lift ⟨fun m₀ m₁ => (Ua.filter (fun i => oddHolesOn G Va (m₀ + m₁) i ≠ ∅ ∧
      oddHolesOn G Va (m₀ + m₁) i ≠ nbrOn G Va i)).card,
    fun m₀ m₁ => by simp only [add_comm]⟩

end PCNonBool


