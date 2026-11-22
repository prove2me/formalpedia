-- Prove2me | Definitions.Def_AvgPHETH_Supplement_OracleData
-- name    : AvgPHETH_Supplement_OracleData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:45:24.465542+00:00
-- url     : https://prove2.me/theorems/bb018e2f-1cf0-494f-8a7e-4f57332e4543
-- title:
--   The data of the oracle construction of §8.1
-- statement:
--   The oracle construction of Section 8 depends, besides its random restrictions, on the following data:
--
--   1. the function $\varepsilon$;
--   2. a numbering $i\mapsto M_i$ of deterministic oracle machines, which fixes the codes $\langle M,d\rangle$ in $A$-queries;
--   3. the enumeration $s\mapsto(k_s,M_s,m_s)$ of triples;
--   4. the rule by which step 3(b)iii selects a disagreeing pair $(\alpha,x)$;
--   5. the sequence $n_s$ of reserved input lengths.
--
--   The paper leaves these choices open. They are parameters, and Theorems 8.5 and 8.7 are stated for every admissible choice.
--
--   **Formalization Note** The published oracle machines have arbitrary alphabet and state types and cannot be enumerated, so the numbering is only required to contain every machine up to its acceptance behaviour. The selection rule replaces the paper's unspecified lexicographic order.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, pp.38–41 (PDF 40–43)

import Mathlib
import Definitions.Def_AvgPHETH_Supplement_CVar
import Definitions.Def_KarpLiptonOM_OracleTM

namespace AvgPHETH.Supplement

open KarpLiptonOM

/-- The data on which the oracle construction of §8.1 depends, besides its random choices
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, pp.38–41 (PDF 40–43)):

* `eps`: the function `ε` fixed throughout Section 8;
* `mach`: a numbering `i ↦ M_i` of deterministic oracle machines, which fixes the codes `⟨M, d⟩` in the
  `A`-queries and the machines `M_s` of the enumeration;
* `enum`: the enumeration `s ↦ (k_s, i_s, m_s)` of the triples `(k, M, m)`, with `M_s = mach i_s`;
* `pick`: the rule by which step 3(b)iii selects a pair `(α, x)` among the disagreeing ones ("in
  lexicographic order");
* `ns`: the sequence `n_s` of reserved input lengths.

**Formalization Note** The page leaves all of these open ("an enumeration of all triples", "set `n_s`
to be large enough", an unspecified lexicographic order, unspecified machine codes). They are
parameters here, and Theorems 8.5 and 8.7 are stated for every choice satisfying
`OracleData.Admissible`. The published machines `KarpLiptonOM.OracleTM` form a proper class of
structures (arbitrary alphabet and state types) and cannot be enumerated; `mach` is required to
contain every machine up to its acceptance behaviour. -/
structure OracleData where
  /-- the function `ε` of Section 8 -/
  eps : ℕ → ℝ
  /-- the numbering of oracle machines -/
  mach : ℕ → OracleTM
  /-- the enumeration `s ↦ (k_s, i_s, m_s)`, with `M_s = mach i_s` -/
  enum : ℕ → ℕ × ℕ × ℕ
  /-- the selection rule of step 3(b)iii -/
  pick : Set ((CVar → List Bool) × List Bool) → (CVar → List Bool) × List Bool
  /-- the reserved input lengths `n_s` -/
  ns : ℕ → ℕ

end AvgPHETH.Supplement


