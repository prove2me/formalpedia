-- Prove2me | Definitions.Def_GPTIP632_Classical_Supplement_SpaceTransducer
-- name    : GPTIP632_Classical_Supplement_SpaceTransducer
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:14:15.526066+00:00
-- url     : https://prove2.me/theorems/2f5f20fc-f9dd-453a-ae66-24a5bc454944
-- title:
--   Total space-bounded machines and unary output computation
-- statement:
--   Fix the published deterministic oracle Turing machine model with the empty oracle. A machine $M$ is total in space $s$ if it halts on every bit string $x$ while visiting at most $s(|x|)$ cells, counting input and query cells. Its decision function is true exactly when its run eventually accepts; totality makes false equivalent to rejection.
--
--   For a string-valued function $f$ of a positive integer, a transducer computes $f$ in space $s$ when
--
--   $$\forall m\ge1\;\exists T:\ M(1^m)\text{ halts by }T,\quad\operatorname{output}_M(1^m,T)=f(m),\quad\operatorname{space}_M(1^m,T)\le s(m).$$
--
--   This interface states the space assertion in Lemma G.2 without imposing a time bound or assuming the machine already computes the desired maximum.
-- source:
--   Kishor Bharti, Beyond IP = PSPACE and QIP = PSPACE: Interactive Proofs in Arbitrary Physical Theories, STOC 2027 submission #632 (October 2026), source.pdf SHA-256 ebbc45027e7a3b48cbfb1a2deb89e9a7d8374373b23763680b948fda16cf4da7, p.33 (PDF p.35), Lemma G.2, space assertion

import Mathlib
import Definitions.Def_GPTIP632_Classical_Theory

namespace GPTIP632.Classical.Supplement

open QAdvFew.PoQOracle QAlgorithms.Complexity

/-- A deterministic empty-oracle machine halting on all inputs in space `s(|x|)`.
Space is precisely the published OTM accounting, including input and query cells. -/
def TotalInSpace (M : OTM) (s : ℕ → ℕ) : Prop :=
  ∀ x : Str, ∃ T : ℕ, M.result O₀ x T ≠ none ∧ M.space O₀ x T ≤ s x.length

/-- The language accepted by a deterministic machine, presented as a total Boolean function.
For a total machine, `false` means rejection. No effectiveness is asserted by this definition. -/
noncomputable def machineDecision (M : OTM) (x : Str) : Bool := by
  classical
  exact if ∃ T : ℕ, M.result O₀ x T = some true then true else false

/-- A function of a positive unary argument is computed in the indicated space by one transducer
halting on every such input. The halting state and entire output string are required. -/
def ComputesUnaryInSpace (M : OTM) (f : ℕ → Str) (s : ℕ → ℕ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∃ T : ℕ,
    M.result O₀ (unary m) T ≠ none ∧
    M.output O₀ (unary m) T = f m ∧ M.space O₀ (unary m) T ≤ s m

end GPTIP632.Classical.Supplement


