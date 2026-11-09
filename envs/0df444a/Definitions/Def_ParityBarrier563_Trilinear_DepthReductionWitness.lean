-- Prove2me | Definitions.Def_ParityBarrier563_Trilinear_DepthReductionWitness
-- name    : ParityBarrier563_Trilinear_DepthReductionWitness
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:09:13.350316+00:00
-- url     : https://prove2.me/theorems/d93b7787-c78f-42d7-913a-0dbcd8720195
-- title:
--   Lemma 2.2 — the property of the depth-reduction parameters k, q and the exponent A
-- statement:
--   Fix a depth $d$. Let $k:\mathbb N\to\mathbb N$ and $q:\mathbb N\to\mathbb R$ assign numbers $k(s)$ and $q(s)$ to every size bound $s$, and let $A$ be a real number. The triple $(k,q,A)$ is a **depth-reduction witness for depth $d$** if:
--
--   1. $0<q(s)\le1$ for every $s\ge2$;
--   2. $k(s)=\Theta(\log s)$: there are constants $0<c_1,c_2$ with $c_1\log s\le k(s)\le c_2\log s$ for all $s\ge2$;
--   3. $1/q(s)=\Theta(\log^{d-3}s)$: there are constants $0<c_1,c_2$ with $c_1\log^{d-3}s\le 1/q(s)\le c_2\log^{d-3}s$ for all $s\ge2$;
--   4. for every $s\ge2$, every finite set $V$ with $2\le|V|\le s$, and every function $F$ computed by a circuit on $V$ of depth at most $d$ with at most $s$ gates and an OR output gate, a $q(s)$-random restriction $\varphi$ of $V$ satisfies
--   $$\Pr_\varphi\bigl[F_\varphi\text{ is the OR of at most }s^{A}\ k(s)\text{-CNFs}\bigr]\ge\frac34 .$$
--
--   Lemma 2.2 states that such a witness exists for every fixed $d\ge3$, and Lemma 5.1 is stated for any witness. Naming the property lets the two lemmas share the same numbers $k$ and $q$, as the source does ("let $k$ and $q$ be the numbers given by Lemma 2.2").
--
--   **Formalization Note** Logarithms are base two (`Real.logb 2`). The constants in items 2 and 3 are existentially quantified inside the property, so they may depend on $d$ and on the witness, never on $s$, $V$ or the circuit.
-- source:
--   Nikolai Chukhin, Xin Li, Ivan Mihajlin, Yan Zhong, Breaking the Parity Barrier for Constant-Depth Circuits, STOC 2027 submission #563 (October 2026), SHA-256 e50e7ff9480ef7c23095e91345faf20f73773bc111e3b0eed2da71a28f7f9462, Lemma 2.2, printed p.10 (PDF p.12)

import Mathlib
import Definitions.Def_ParityBarrier563_Trilinear_Circuit
import Definitions.Def_ParityBarrier563_Trilinear_CNF
import Definitions.Def_ParityBarrier563_Trilinear_Restriction

set_option autoImplicit false

namespace ParityBarrier563.Trilinear

/-! The parameters of Håstad's depth reduction, Lemma 2.2, printed p.10 / PDF 12. -/

/-- `DepthReductionWitness d k q A`: the size-indexed numbers `k(s)` and `q(s)` and the exponent
`A` have the properties that Lemma 2.2 asserts for depth `d`:
1. `0 < q(s) ≤ 1` for every `s ≥ 2`;
2. `k(s) = Θ(log₂ s)`: there are `0 < c₁, c₂` with `c₁ log₂ s ≤ k(s) ≤ c₂ log₂ s` for all `s ≥ 2`;
3. `1/q(s) = Θ(log₂^{d−3} s)`: there are `0 < c₁, c₂` with
   `c₁ (log₂ s)^{d−3} ≤ 1/q(s) ≤ c₂ (log₂ s)^{d−3}` for all `s ≥ 2`;
4. for every `s ≥ 2`, every finite variable set `V` with `2 ≤ |V| ≤ s`, and every circuit on `V`
   of depth at most `d` with at most `s` gates and an OR output gate, computing `F`, the
   restricted function `F_φ` of a `q(s)`-random restriction `φ` of `V` is the OR of at most `s^A`
   `k(s)`-CNFs with probability at least `3/4`. -/
def DepthReductionWitness (d : ℕ) (k : ℕ → ℕ) (q : ℕ → ℝ) (A : ℝ) : Prop :=
  (∀ s : ℕ, 2 ≤ s → 0 < q s ∧ q s ≤ 1) ∧
  (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ s : ℕ, 2 ≤ s →
    c₁ * Real.logb 2 s ≤ (k s : ℝ) ∧ (k s : ℝ) ≤ c₂ * Real.logb 2 s) ∧
  (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ s : ℕ, 2 ≤ s →
    c₁ * (Real.logb 2 s) ^ (d - 3) ≤ 1 / q s ∧ 1 / q s ≤ c₂ * (Real.logb 2 s) ^ (d - 3)) ∧
  (∀ s : ℕ, 2 ≤ s → ∀ (V : Type) [Fintype V] [DecidableEq V],
    2 ≤ Fintype.card V → Fintype.card V ≤ s →
    ∀ C : Circuit V, C.size ≤ s → C.depth ≤ d → C.OutputIsOr →
      3 / 4 ≤ restrProb (q s) (fun φ => IsOrOfCNFs (k s) ((s : ℝ) ^ A) (restrict φ C.eval)))

end ParityBarrier563.Trilinear


