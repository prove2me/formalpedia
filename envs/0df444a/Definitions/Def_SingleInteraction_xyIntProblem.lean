-- Prove2me | Definitions.Def_SingleInteraction_xyIntProblem
-- name    : SingleInteraction_xyIntProblem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:56:39.076051+00:00
-- url     : https://prove2.me/theorems/30e674c1-5b38-4674-99ad-4a4172a6db17
-- title:
--   The positive-integer-weight XY problem
-- statement:
--   For a polynomial exponent $c$, an input $(n,(u_i,v_i,w_i)_i,a,b)$ is valid when every term has $u_i,v_i<n$, $u_i\ne v_i$ and an integer weight $1\le w_i\le(n+1)^c$; there are at most $(n+1)^c$ terms; and the thresholds are valid. With $H=\sum_iw_iK_{u_iv_i}$, YES if some state has energy at most $a$, NO if every state has energy at least $b$.
--
--   This is the restriction of $\{X\otimes X+Y\otimes Y\}^+$-Hamiltonian to positive integer coupling strengths of polynomial magnitude.
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), Lemma 61, p.55

import Mathlib
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_SingleInteraction_XYIntInstance
import Definitions.Def_SingleInteraction_ThresholdsValid
import Definitions.Def_SingleInteraction_xyHam
import Definitions.Def_SingleInteraction_hamPromise

open OAI.ContinuumCoulomb OAI.ContinuumCoulomb.BinaryEncoding

namespace SingleInteraction

/-- Validity of a positive-integer-weight XY input for the polynomial exponent `c` (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), Lemma 61,
p.55: "The restriction of `{X ⊗ X + Y ⊗ Y}⁺`-Hamiltonian to positive integer coupling strengths of
polynomial magnitude"):

1. every term `(u, v, w)` has `u, v < n`, `u ≠ v` and `1 ≤ w ≤ (n+1)^c`;
2. there are at most `(n+1)^c` terms;
3. the thresholds satisfy `ThresholdsValid n c a b`. -/
def XYIntInstance.Valid (c : ℕ) (x : XYIntInstance) : Prop :=
  (∀ t ∈ x.terms, t.1 < x.n ∧ t.2.1 < x.n ∧ t.1 ≠ t.2.1 ∧ 1 ≤ t.2.2 ∧ t.2.2 ≤ (x.n + 1) ^ c) ∧
    x.terms.length ≤ (x.n + 1) ^ c ∧ ThresholdsValid x.n c x.a x.b

/-- The positive-integer-weight XY problem at the polynomial exponent `c` (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), Lemma 61, p.55):
`H = Σ_i w_i K_{u_i v_i}` with integer `w_i ≥ 1`; YES if some `n`-qubit state has energy `≤ a`, NO if
every `n`-qubit state has energy `≥ b`. -/
noncomputable def xyIntProblem (c : ℕ) : PromiseProblem XYIntInstance :=
  hamPromise (XYIntInstance.Valid c) (fun x => x.n)
    (fun x => xyHam x.n (x.terms.map fun t => (t.1, t.2.1, (t.2.2 : ℝ))))
    (fun x => (x.a.value : ℝ)) (fun x => (x.b.value : ℝ)) (fun _ hx => hx.2.2.lt)

end SingleInteraction


