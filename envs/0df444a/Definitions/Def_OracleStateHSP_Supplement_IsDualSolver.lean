-- Prove2me | Definitions.Def_OracleStateHSP_Supplement_IsDualSolver
-- name    : OracleStateHSP_Supplement_IsDualSolver
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:08:31.8165+00:00
-- url     : https://prove2.me/theorems/ba2a8b37-28ee-4811-8cf8-c306ae4a152c
-- title:
--   DUAL-SOLVER: generators of $(K^\perp)^\perp$ from generators of $K^\perp$ (Definition 3.3)
-- statement:
--   Let $S^\perp$ be a data structure encoding a generating set for a subgroup $K^\perp \le \hat G$. A **DUAL-SOLVER** is a deterministic classical routine $\mathrm{DUAL\text{-}SOLVER}(S^\perp)$ that outputs a data structure encoding a generating set $S$ for the corresponding group
--   $$
--   K := (K^\perp)^\perp = \{g \in G : \chi_\lambda(g) = 1 \text{ for all } \lambda \in K^\perp\} \le G .
--   $$
--
--   **Formalization Note** Data structures are finite sets; a DUAL-SOLVER is any function whose output generates the dual of $\langle S^\perp \rangle$.
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, Definition 3.3, p.20

import Mathlib
import Definitions.Def_OracleStateHSP_Supplement_perp

namespace OracleStateHSP

namespace Supplement

/-- DUAL-SOLVER (Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, Definition 3.3, p.20): for a data structure `S⊥` encoding a generating set
for `K⊥ ≤ Ĝ`, the deterministic routine `DUAL-SOLVER(S⊥)` outputs a data structure encoding a
generating set `S` for `K := (K⊥)⊥ ≤ G`.

**Formalization Note.** Data structures are finite sets; `dual` is any function whose output
generates `(⟨S⊥⟩)⊥ = {g : χ_λ(g) = 1 for all λ ∈ ⟨S⊥⟩}` (`perp`, using the symmetric pairing). -/
def IsDualSolver {n : ℕ} {M : Fin n → ℕ}
    (dual : Finset (CycProd n M) → Finset (CycProd n M)) : Prop :=
  ∀ S, ((AddSubgroup.closure (dual S : Set (CycProd n M)) : AddSubgroup (CycProd n M)) : Set (CycProd n M)) =
    perp ((AddSubgroup.closure (S : Set (CycProd n M)) : AddSubgroup (CycProd n M)) : Set (CycProd n M))

end Supplement

end OracleStateHSP


