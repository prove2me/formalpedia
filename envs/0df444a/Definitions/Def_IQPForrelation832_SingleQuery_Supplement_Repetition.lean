-- Prove2me | Definitions.Def_IQPForrelation832_SingleQuery_Supplement_Repetition
-- name    : IQPForrelation832_SingleQuery_Supplement_Repetition
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:50:54.919905+00:00
-- url     : https://prove2.me/theorems/cf6d609b-1c57-4a9c-98e9-3c170248ad2c
-- title:
--   Independent two-run equality procedure
-- statement:
--   Let $p_{n,b}$ be a published one-query program, $b\in\{0,1\}$ its branch, and $a$ its accepting decider. For two independent fresh-register executions, define the acceptance event to mean equality of the two decoded decision bits. If their output states are $\psi_b$ and $\psi_c$, its conditional probability is the ordinary Born probability of that event in $\psi_b\otimes\psi_c$. Average over two independent fair branch coins:
--   $$
--   P_{\mathrm{eq}}(f,g)=\frac14\sum_{b,c\in\{0,1\}}\sum_{z,w:\,a(n,b,z)=a(n,c,w)}\Pr_b[z]\Pr_c[w].
--   $$
--   Here equality compares the Boolean acceptance predicates, including equality when both predicates are false. Two-run validity requires actual compilations of the two programs into IQP middle blocks whose joint-oracle counts sum to two. The published per-run compiler, decider and efficiency model are reused without alteration. This definition supplies only the composition and its measurement event, with no acceptance identity assumed.
-- source:
--   Quentin Buzet, André Chailloux, IQP circuits for 2-Forrelation, STOC 2027 submission #832 (October 2026), pp. 20–21, Theorem 2 and its proof. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/832.pdf

import Definitions.Def_IQPForrelation832_SingleQuery_Programs

set_option autoImplicit false

namespace IQPForrelation832.SingleQuery.Supplement

open QAlgorithms QAlgorithms.Complexity

/-- Two independent measurements on fresh registers; the event compares the two decoded
bits. The uniform branch coins are summed separately in `twoRunBorn`. -/
noncomputable def equalDecisionBorn (n : ℕ) (p q : Program) (a : Str → Str)
    (b c : Bool) (f g : Cube n → ℝ) : ℝ := by
  classical
  exact match compile n p, compile n q with
  | some cp, some cq =>
      probEvent (tensorVec (run cp f g) (run cq f g))
        (fun z => accepts a n b z.1 ↔ accepts a n c z.2)
  | _, _ => 0

noncomputable def twoRunBorn (n : ℕ) (p : ℕ → Bool → Program) (a : Str → Str)
    (f g : Cube n → ℝ) : ℝ :=
  (∑ b : Bool, ∑ c : Bool, equalDecisionBorn n (p n b) (p n c) a b c f g) / 4

/-- The two physical runs have exactly two occurrences of the joint oracle altogether. -/
def TwoRunValid (n : ℕ) (p : ℕ → Bool → Program) : Prop :=
  ∀ b c, ∃ cp cq, compile n (p n b) = some cp ∧ compile n (p n c) = some cq ∧
    IsIQP cp ∧ IsIQP cq ∧
    OracleCircuit.queryCount cp 0 + OracleCircuit.queryCount cq 0 = 2

end IQPForrelation832.SingleQuery.Supplement


