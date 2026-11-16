-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_Supplement_IsPSPACEComplete
-- name    : QAdvFew_PoQOracle_Supplement_IsPSPACEComplete
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:15:13.3838+00:00
-- url     : https://prove2.me/theorems/5bf9724a-72a8-4217-9e81-292a3b2f4761
-- title:
--   PSPACE-complete languages as classical oracles
-- statement:
--   A language $L\subseteq\{0,1\}^*$ is identified with the classical oracle $x\mapsto[x\in L]$. $L$ is **PSPACE-complete** if $L\in\mathsf{PSPACE}$ and every language in $\mathsf{PSPACE}$ reduces to $L$ by a deterministic polynomial-time many-one reduction.
--
--   Section 5 fixes "an oracle PSPACE for a PSPACE-complete problem", independent of the random oracle; the supplement's statements hold for every such choice.
--
--   **Formalization Note** Unrelativized $\mathsf{PSPACE}$ is the published `QAdvFew.PoQOracle.PSPACE` at the constant-$0$ oracle.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, §3.2.3, p. 13 (PDF p. 15); §5.1, p. 33 (PDF p. 35)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_PSPACE

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle.Supplement

open QAdvFew.PoQOracle

open Classical in
/-- A language as a classical oracle, `x ↦ [x ∈ L]` (Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1, §3.2.3, p. 12 (PDF p. 14): "We identify a
language `L ⊆ {0,1}*` with its characteristic function"). -/
noncomputable def langOracle (L : Set Str) : Oracle := fun x => decide (x ∈ L)

/-- `L` is **PSPACE-complete** (Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1, §3.2.3, p. 13 (PDF p. 15): "A complexity class in an oracle
superscript denotes a fixed complete problem for that class"; §5.1, p. 33 (PDF p. 35): "fix an
oracle PSPACE for a PSPACE-complete problem"): `L ∈ PSPACE` and every language in `PSPACE` reduces
to `L` by a deterministic polynomial-time many-one reduction.

**Formalization Note** Unrelativized `PSPACE` is the published `QAdvFew.PoQOracle.PSPACE` at the
constant-`false` oracle ("Omitting the oracle gives the corresponding unrelativized classes"). -/
def IsPSPACEComplete (L : Set Str) : Prop :=
  L ∈ PSPACE (fun _ => false) ∧
    ∀ L' ∈ PSPACE (fun _ => false), ∃ r : Str → Str, PolyTimeComputable r ∧ ∀ x, x ∈ L' ↔ r x ∈ L

end QAdvFew.PoQOracle.Supplement


