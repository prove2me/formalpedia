-- Prove2me | Definitions.Def_SingleInteraction_xyPlusProblem
-- name    : SingleInteraction_xyPlusProblem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:56:47.630727+00:00
-- url     : https://prove2.me/theorems/cc9696e4-34d8-41cd-8171-d72565c783a4
-- title:
--   The problem $\{X\otimes X+Y\otimes Y\}^+$-Hamiltonian
-- statement:
--   For a polynomial exponent $c$, an input $(n,(u_i,v_i,\alpha_i)_i,a,b)$ is valid when every term has $u_i,v_i<n$, $u_i\ne v_i$, a positive denominator, $0\le\alpha_i\le(n+1)^c$ and a code of at most $(n+1)^c$ bits; there are at most $(n+1)^c$ terms; and the thresholds are valid. With $H=\sum_i\alpha_iK_{u_iv_i}$:
--
--   1. YES: some $n$-qubit state has $\langle\phi|H|\phi\rangle\le a$;
--   2. NO: every $n$-qubit state has $\langle\phi|H|\phi\rangle\ge b$.
--
--   This is the positive-weight XY problem of §2.3.5 with the promise of Definition 6.
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), §2.3.5, pp.25–26; Definition 6, pp.17–18

import Mathlib
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_SingleInteraction_XYWeightedInstance
import Definitions.Def_SingleInteraction_ThresholdsValid
import Definitions.Def_SingleInteraction_xyHam
import Definitions.Def_SingleInteraction_hamPromise

open OAI.ContinuumCoulomb OAI.ContinuumCoulomb.BinaryEncoding

namespace SingleInteraction

/-- Validity of a `{X⊗X + Y⊗Y}⁺`-Hamiltonian input for the polynomial exponent `c` (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §2.3.5,
p.25: "`M = poly(n)`, the coefficients `α_i ∈ ℝ` are polynomially bounded and specified with polynomially
many bits, and `V_i` specifies the qubits on which the interaction is applied. We write
`S⁺`-Hamiltonian for the restriction in which all coupling strengths are nonnegative, `α_i ≥ 0`"; with
the thresholds of Definition 6, p.17):

1. every term `(u, v, α)` has `u, v < n`, `u ≠ v`, a positive denominator, `0 ≤ α ≤ (n+1)^c`, and a code
   of at most `(n+1)^c` bits;
2. there are at most `(n+1)^c` terms;
3. the thresholds satisfy `ThresholdsValid n c a b`. -/
def XYWeightedInstance.Valid (c : ℕ) (x : XYWeightedInstance) : Prop :=
  (∀ t ∈ x.terms, t.1 < x.n ∧ t.2.1 < x.n ∧ t.1 ≠ t.2.1 ∧ 0 < t.2.2.denominator ∧
      0 ≤ t.2.2.value ∧ (t.2.2.value : ℝ) ≤ ((x.n : ℝ) + 1) ^ c ∧
      (binaryRationalCodec.encode t.2.2).length ≤ (x.n + 1) ^ c) ∧
    x.terms.length ≤ (x.n + 1) ^ c ∧ ThresholdsValid x.n c x.a x.b

/-- The positive-weight XY problem `{X⊗X + Y⊗Y}⁺`-Hamiltonian at the polynomial exponent `c` (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…),
§2.3.5, pp.25–26, with the promise of Definition 6, pp.17–18). For a valid input with
`H = Σ_i α_i (X_{u_i}X_{v_i} + Y_{u_i}Y_{v_i})`: YES if some `n`-qubit state has energy `≤ a`, NO if every
`n`-qubit state has energy `≥ b`.

**Formalization Note** "`poly(n)`" (number of terms, coefficient bound, bit lengths, inverse gap) is the
single exponent `c`. -/
noncomputable def xyPlusProblem (c : ℕ) : PromiseProblem XYWeightedInstance :=
  hamPromise (XYWeightedInstance.Valid c) (fun x => x.n)
    (fun x => xyHam x.n (x.terms.map fun t => (t.1, t.2.1, (t.2.2.value : ℝ))))
    (fun x => (x.a.value : ℝ)) (fun x => (x.b.value : ℝ)) (fun _ hx => hx.2.2.lt)

end SingleInteraction


