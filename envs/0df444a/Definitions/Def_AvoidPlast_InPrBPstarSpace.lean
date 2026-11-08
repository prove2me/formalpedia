-- Prove2me | Definitions.Def_AvoidPlast_InPrBPstarSpace
-- name    : AvoidPlast_InPrBPstarSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:47:25.386923+00:00
-- url     : https://prove2.me/theorems/9939e1ae-7b96-4ef1-8215-7a7a8f04d14c
-- title:
--   The class prBP$^*$SPACE$[O(s(n))]$
-- statement:
--   A promise problem $\Pi$ is in **prBP$^*$SPACE$[O(s(n))]$** if there are a machine $M$ with read-only tapes $x$ and $\rho$ and a constant $C$ such that, with $R(n)=\lceil 2^{C(s(n)+1)}\rceil$: on every $x$ and $\rho\in\{0,1\}^{R(|x|)}$, $M$ halts within $R(|x|)$ steps with work space at most $C(s(|x|)+1)$; $\Pr_\rho[M(x,\rho)\text{ accepts}]\ge 2/3$ on yes-instances and $\le 1/3$ on no-instances. The random string sits on a read-only tape and costs no space (Definition 3.6: $s(n)$ memory bits, time $2^{O(s(n))}$, two-way access to the randomness).
--
--   **Formalization Note** The length of $\rho$ is fixed to the time bound so that it carries no information beyond $s$; a free length function would act as non-uniform advice.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Definition 3.6, p.14; Section 1.2, p.3

import Mathlib
import Definitions.Def_KarpLiptonOM_PromiseProblem
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_HaltsWithin
import Definitions.Def_AvoidPlast_Accepts
import Definitions.Def_AvoidPlast_workSpace
import Definitions.Def_AvoidPlast_prob

namespace AvoidPlast

/-- The class prBP\*SPACE[O(s(n))] (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Definition 3.6, p.14; p.3): promise problems solvable by a
probabilistic machine that on an `n`-bit input uses `O(s(n))` memory bits, runs for at most
`2^{O(s(n))}` time and has 2-way access to its randomness, whose contents do not count towards the
space. The machine has read-only tapes for `x` and for the random string `ρ`.

**Formalization Note** The random string has the fixed length `⌈2^{C(s(n)+1)}⌉`, the machine's own
time bound, so that the length of `ρ` carries no information beyond `s`: a free length function
would act as non-uniform advice. A longer tape than the machine can use costs nothing. -/
def InPrBPstarSpace (s : ℕ → ℝ) (P : KarpLiptonOM.PromiseProblem) : Prop :=
  ∃ (M : Machine 2) (C : ℝ),
    (∀ x ρ : List Bool, ρ.length = ⌈(2 : ℝ) ^ (C * (s x.length + 1))⌉₊ →
      HaltsWithin M ![x, ρ] ⌈(2 : ℝ) ^ (C * (s x.length + 1))⌉₊ ∧
      (workSpace M ![x, ρ] : ℝ) ≤ C * (s x.length + 1)) ∧
    (∀ x ∈ P.yes, (2 : ℝ) / 3 ≤
      prob ⌈(2 : ℝ) ^ (C * (s x.length + 1))⌉₊ fun ρ => Accepts M ![x, ρ]) ∧
    (∀ x ∈ P.no,
      prob ⌈(2 : ℝ) ^ (C * (s x.length + 1))⌉₊ (fun ρ => Accepts M ![x, ρ]) ≤ (1 : ℝ) / 3)

end AvoidPlast


