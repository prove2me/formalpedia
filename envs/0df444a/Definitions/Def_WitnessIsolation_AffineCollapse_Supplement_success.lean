-- Prove2me | Definitions.Def_WitnessIsolation_AffineCollapse_Supplement_success
-- name    : WitnessIsolation_AffineCollapse_Supplement_success
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:50:08.891548+00:00
-- url     : https://prove2.me/theorems/0787cb41-cdc5-46cf-8fe6-6238704777b1
-- title:
--   General-input and two-point success guarantees
-- statement:
--   Let $I$ be a pruning family (the published `PruningFamily`, with its run map $I(H;\rho)$ on a description $H$ of bit length $L$ and a uniform random tape $\rho$), and let $p,\gamma:\mathbb N\to\mathbb R$ be arbitrary functions. Write $\mathrm{Sol}(H)$ for the set of satisfying assignments of a decoded description $H$ with $n$ declared variables.
--
--   1. $I$ has **general witness-length guarantee** $p$ if there is $n_0$ such that for every $L$, every bit string $h$ of length $L$ that decodes to a description $H$ with $n\ge n_0$ declared variables and $\mathrm{Sol}(H)\neq\emptyset$,
--   $$\Pr_\rho\big[\,|\mathrm{Sol}(I(H;\rho))|=1\,\big]\ \ge\ p(n).$$
--   2. $I$ has **two-point success** $1/2+\gamma$ if there is $n_0$ such that the same holds with $|\mathrm{Sol}(H)|=2$ in place of $\mathrm{Sol}(H)\ne\emptyset$ and with $1/2+\gamma(n)$ in place of $p(n)$.
--
--   These are the success promises of Theorems 1.3 and 1.4. They differ from the published affine guarantee `HasGuarantee` only in the class of inputs on which success is promised: one threshold $n_0$ serves every description length, and nothing is assumed about $p$ or $\gamma$ (no monotonicity, positivity or computability). The pruning and resource requirements are not part of these predicates; theorems add them through the published `IsPruner`.
-- source:
--   Sebastian ben daniel, STOC 2027 submission #346 (October 2026), p. 2, PDF p. 3 (general witness-length guarantee, §1.1, referring to (2.1) of Definition 2.1 on p. 6–7, PDF pp. 7–8); p. 3, PDF p. 4 (Theorem 1.4 hypothesis)

import Definitions.Def_WitnessIsolation_AffineCollapse_model

set_option autoImplicit false
noncomputable section

namespace WitnessIsolation.AffineCollapse.Supplement

/-- A single eventual witness threshold, uniform over all description lengths. -/
def GeneralGuarantee (I : PruningFamily) (p : ℕ → ℝ) : Prop :=
  ∃ N : ℕ, ∀ L (h : Bits L) d, decode (List.ofFn h) = some d →
    N ≤ d.inputs → d.sol.Nonempty →
    uniformProb (fun r : Bits (I.randomLength L) =>
      ∃ e, decode (I.run L h r) = some e ∧ e.sol.card = 1) ≥ p d.inputs

/-- Success is promised only on two-solution inputs; pruning is separate. -/
def TwoPointGuarantee (I : PruningFamily) (γ : ℕ → ℝ) : Prop :=
  ∃ N : ℕ, ∀ L (h : Bits L) d, decode (List.ofFn h) = some d →
    N ≤ d.inputs → d.sol.card = 2 →
    uniformProb (fun r : Bits (I.randomLength L) =>
      ∃ e, decode (I.run L h r) = some e ∧ e.sol.card = 1) ≥ 1/2 + γ d.inputs

end WitnessIsolation.AffineCollapse.Supplement


