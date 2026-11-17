-- Prove2me | Definitions.Def_OracleStateHSP_Supplement_perp
-- name    : OracleStateHSP_Supplement_perp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:06:41.749954+00:00
-- url     : https://prove2.me/theorems/f403e7bf-d943-42b8-8d08-98524a605aad
-- title:
--   Dual subgroup $H^\perp = \{\lambda : \chi_\lambda(h) = 1\ \forall h \in H\}$ (Definition 2.3)
-- statement:
--   For a subgroup $H$ of the finite abelian group $G$, the **dual subgroup** (annihilator) of $H$ consists of the characters of $G$ that are trivial on $H$:
--   $$
--   H^\perp := \{\lambda \in \hat G : \chi_\lambda(h) = 1 \text{ for all } h \in H\}.
--   $$
--   It is a subgroup of $\hat G$ with $|H^\perp| = |G|/|H|$, and $(H^\perp)^\perp = H$. Fourier sampling returns elements of $H^\perp$, and the hidden subgroup is recovered from a generating set of $H^\perp$ by taking the dual again.
--
--   **Formalization Note** The definition is stated, as on the page, as a set, for any set of group elements; the subgroup property, the cardinality and the double-dual identity are facts, not part of the definition. Because the pairing $\chi_\lambda(g)$ is symmetric, the same definition gives the dual $(K^\perp)^\perp \le G$ of a subgroup $K^\perp \le \hat G$ used in Definition 3.3.
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, Definition 2.3, p.16

import Mathlib
import Definitions.Def_OracleStateHSP_Supplement_chi

namespace OracleStateHSP

namespace Supplement

/-- The dual subgroup (annihilator) of Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, Definition 2.3, p.16:
`H⊥ := {λ ∈ Ĝ : χ_λ(h) = 1 for all h ∈ H}`.

**Formalization Note.** It is defined, as on the page, as a set, for any set `S` of group
elements (in the theorems `S` is a subgroup `H ≤ G`, or the subgroup `K⊥ ≤ Ĝ` in
`(K⊥)⊥`, Definition 3.3). That it is a subgroup with `|H⊥| = |G|/|H|` and `(H⊥)⊥ = H`
(Appendix A) are facts, not part of the definition. Because `χ_λ(g)` is symmetric in `λ` and `g`,
the same definition gives the dual `(K⊥)⊥ = {g ∈ G : χ_λ(g) = 1 for all λ ∈ K⊥}`. -/
def perp {n : ℕ} {M : Fin n → ℕ} (S : Set (CycProd n M)) : Set (CycProd n M) :=
  {lam | ∀ h ∈ S, chi lam h = 1}

end Supplement

end OracleStateHSP


