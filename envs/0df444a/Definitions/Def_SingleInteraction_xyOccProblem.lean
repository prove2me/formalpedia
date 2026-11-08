-- Prove2me | Definitions.Def_SingleInteraction_xyOccProblem
-- name    : SingleInteraction_xyOccProblem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:56:36.552547+00:00
-- url     : https://prove2.me/theorems/6c2782c9-0e14-4726-bd01-3c37b13dd3e0
-- title:
--   The XY occurrence-list problem
-- statement:
--   For a polynomial exponent $c$, an input $(n,(u_e,v_e)_{e=1}^M,a,b)$ is valid when every occurrence has $u_e,v_e<n$ and $u_e\ne v_e$, $M\le(n+1)^c$, and the thresholds are valid. With $K=\sum_{e=1}^MK_{u_ev_e}$ (repeated occurrences on the same pair allowed), YES if some state has energy at most $a$, NO if every state has energy at least $b$.
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), Lemma 61, p.55

import Mathlib
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_SingleInteraction_XYOccInstance
import Definitions.Def_SingleInteraction_ThresholdsValid
import Definitions.Def_SingleInteraction_xyHam
import Definitions.Def_SingleInteraction_hamPromise

open OAI.ContinuumCoulomb OAI.ContinuumCoulomb.BinaryEncoding

namespace SingleInteraction

/-- Validity of an XY occurrence-list input for the polynomial exponent `c` (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), Lemma 61, p.55):
every occurrence `(u, v)` has `u, v < n` and `u ≠ v`; there are at most `(n+1)^c` occurrences (repeats
allowed); the thresholds satisfy `ThresholdsValid n c a b`. -/
def XYOccInstance.Valid (c : ℕ) (x : XYOccInstance) : Prop :=
  (∀ p ∈ x.pairs, p.1 < x.n ∧ p.2 < x.n ∧ p.1 ≠ p.2) ∧ x.pairs.length ≤ (x.n + 1) ^ c ∧
    ThresholdsValid x.n c x.a x.b

/-- The XY occurrence-list problem at the polynomial exponent `c` (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), Lemma 61, p.55):
`K = Σ_{e=1}^M K_{u_e v_e}`; YES if some `n`-qubit state has energy `≤ a`, NO if every `n`-qubit state has
energy `≥ b`. -/
noncomputable def xyOccProblem (c : ℕ) : PromiseProblem XYOccInstance :=
  hamPromise (XYOccInstance.Valid c) (fun x => x.n)
    (fun x => xyHam x.n (x.pairs.map fun p => (p.1, p.2, (1 : ℝ))))
    (fun x => (x.a.value : ℝ)) (fun x => (x.b.value : ℝ)) (fun _ hx => hx.2.2.lt)

end SingleInteraction


