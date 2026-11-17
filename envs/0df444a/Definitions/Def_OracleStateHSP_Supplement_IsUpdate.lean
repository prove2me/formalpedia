-- Prove2me | Definitions.Def_OracleStateHSP_Supplement_IsUpdate
-- name    : OracleStateHSP_Supplement_IsUpdate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:07:55.110314+00:00
-- url     : https://prove2.me/theorems/17c0a7b6-f25b-494b-9e5e-d72a70d55599
-- title:
--   UPDATE: $\langle \mathrm{UPDATE}(S^\perp, s^\perp)\rangle = \langle S^\perp \cup \{s^\perp\}\rangle$ (Definition 3.2)
-- statement:
--   The classical deterministic routine $\mathrm{UPDATE}(S^\perp, s^\perp)$ takes a data structure encoding a generating set $S^\perp$ and a new element $s^\perp \in \hat G$, and returns a data structure encoding a generating set for
--   $$
--   \langle S^\perp \cup \{s^\perp\}\rangle .
--   $$
--
--   **Formalization Note** The data structure is a finite set of dual labels and only the subgroup it generates is specified, so an UPDATE is any function with $\langle \mathrm{UPDATE}(S, s)\rangle = \langle S \cup \{s\}\rangle$; the simplest is $S \mapsto S \cup \{s\}$.
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, Definition 3.2, p.20

import Mathlib
import Definitions.Def_OracleStateHSP_Supplement_CycProd

namespace OracleStateHSP

namespace Supplement

/-- UPDATE (Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, Definition 3.2, p.20): the deterministic routine `UPDATE(S⊥, s⊥)` takes a data
structure encoding a generating set `S⊥` and returns one encoding a generating set for
`⟨S⊥ ∪ {s⊥}⟩`.

**Formalization Note.** The data structure is a finite set of dual labels; only the subgroup it
generates is specified, so `upd` is any function with `⟨upd S s⟩ = ⟨S ∪ {s}⟩`. -/
def IsUpdate {n : ℕ} {M : Fin n → ℕ}
    (upd : Finset (CycProd n M) → CycProd n M → Finset (CycProd n M)) : Prop :=
  ∀ S s, AddSubgroup.closure (upd S s : Set (CycProd n M)) =
    AddSubgroup.closure (insert s (S : Set (CycProd n M)))

end Supplement

end OracleStateHSP


