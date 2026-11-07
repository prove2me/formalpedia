-- Prove2me | Definitions.Def_PCNonBool_touches
-- name    : PCNonBool_touches
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:30:21.787526+00:00
-- url     : https://prove2.me/theorems/63920555-6853-4e91-9eb6-61827645c640
-- title:
--   A pair of monomials touched by $(x_{i,j},x_{i,j'})$
-- statement:
--   A monomial $m$ is **touched** by a pair of variables $(x,y)$ if exactly one of $x$ and $y$ appears in $m$. A pair of monomials $(m_0,m_1)$ is touched by $(x_{i,j},x_{i,j'})$ if this pair touches $m_0m_1 \bmod \langle\mathrm{PA}\cup\{x^2-1\}\rangle$, i.e. if exactly one of $x_{i,j}$, $x_{i,j'}$ occurs to an odd power in $m_0m_1$.
--
--   **Formalization Note** For $j,j'\in N(i)$ this is independent of the representative of the reduced class.
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §5.1 (definition of touched), p.28 (PDF p.31)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_Var
import Definitions.Def_PCNonBool_edgeExp

namespace PCNonBool

/-- The unordered monomial pair `(m₀, m₁)` is touched by the variable pair `(x_{i,j}, x_{i,j'})`
(Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), p.28 (PDF p.31): "a monomial m is touched by a pair of variables (x, y) if exactly
one of x and y appears in m, and … a pair of monomials (m₀, m₁) is touched by (x, y) if (x, y)
touches the monomial m₀m₁ mod ⟨PA ∪ {x² - 1}⟩"). Exactly one of `x_{i,j}`, `x_{i,j'}` occurs to
an odd power in `m₀ m₁`.

**Formalization Note** For `j, j' ∈ N(i)` this does not depend on the representative of the class
of `m₀ m₁`: passing from the hole set `H` to `N(i) \ H` keeps "exactly one of `j, j'`". -/
noncomputable def touches {U V : Type*} (G : BipGraph U V) (i : U) (j j' : V) :
    Sym2 (Var G →₀ ℕ) → Prop :=
  Sym2.lift ⟨fun m₀ m₁ => Xor (Odd (edgeExp G (m₀ + m₁) i j)) (Odd (edgeExp G (m₀ + m₁) i j')),
    fun m₀ m₁ => by simp only [add_comm]⟩

end PCNonBool


