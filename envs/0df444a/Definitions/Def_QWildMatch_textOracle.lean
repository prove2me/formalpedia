-- Prove2me | Definitions.Def_QWildMatch_textOracle
-- name    : QWildMatch_textOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T10:15:31.977222+00:00
-- url     : https://prove2.me/theorems/b6f58fb6-00a2-4d93-b56b-965bf12d39a1
-- title:
--   The quantum text oracle $O_T$
-- statement:
--   The quantum text oracle is the unitary $O_T:|j,z\rangle\mapsto|j,z\oplus T[j]\rangle$, and an inverse call is charged as one query.
--
--   **Formalization Note** It is the published `xorOracle` of the function sending $j$ to $\mathrm{enc}(T[j])$, with index type `Option (Fin n)` and target `Fin w → ZMod 2`. The extra index `none` answers $0$: the state space stays nonempty at $n=0$, and a query at `none` is a no-op, so counting exactly $Q$ applications loses nothing. A symbol is written through `enc : Sym → (Fin w → ZMod 2)`, which the theorems take injective and quantify over. In characteristic 2 the oracle is its own inverse, so the paper's charging rule for inverses holds automatically.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu, Yue, Quantum Approximate Pattern Matching with Wildcards and Weighted Edits, STOC 2027 submission (file sha256 9e87a9dd…), §3, p.4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query

namespace QWildMatch

open QAlgorithms

/-- The text oracle `O_T : |j, z⟩ ↦ |j, z ⊕ T[j]⟩` (Zhao et al., STOC 2027 submission (file sha256
9e87a9dd…), §3, p.4).

**Formalization Note** The index register is `Option (Fin n)`, and the index `none` answers `0`: the
state space stays nonempty at `n = 0`, and a query at `none` is a no-op, so counting exactly `Q`
queries loses nothing. A symbol is written through `enc : Sym → (Fin w → ZMod 2)`, which the theorems
take injective. Over characteristic 2 the oracle is its own inverse, so "an inverse oracle call is
charged as one query" holds automatically. -/
noncomputable def textOracle {Sym : Type} {n w : ℕ} (enc : Sym → (Fin w → ZMod 2)) (T : Fin n → Sym) :
    Matrix (Option (Fin n) × (Fin w → ZMod 2)) (Option (Fin n) × (Fin w → ZMod 2)) ℂ :=
  xorOracle (fun i : Option (Fin n) => i.elim 0 (fun j => enc (T j)))

end QWildMatch


