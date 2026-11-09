-- Prove2me | Definitions.Def_IPPComplexities_Unconditional_validity
-- name    : IPPComplexities_Unconditional_validity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:25:23.020049+00:00
-- url     : https://prove2.me/theorems/704ef1f0-1e59-4ec6-9444-57e84bb27f45
-- title:
--   IPP completeness, soundness, and worst-case resource families
-- statement:
--   Let $L$ be a property and $V=(V_n)_{n\ge0}$ a family of private randomized oracle verifiers. For a positive proximity $\varepsilon$, validity at that proximity means
--
--   $$\begin{aligned}
--   x\in L_n&\implies \exists P,\quad \Pr_{V_n}^{P}[1\mid x]\ge 2/3,\\
--   \operatorname{Far}(L,\varepsilon,x)&\implies \forall P,\quad \Pr_{V_n}^{P}[0\mid x]\ge 2/3.
--   \end{aligned}$$
--
--   These conditions hold for every length and input; nonmembers that are close to the property carry no requirement. Completeness need not be perfect. A full verifier family additionally takes $\varepsilon$ and satisfies these conditions for every positive $\varepsilon$. Resource bounds $q,c:\mathbb N\to\mathbb N$ mean that the actual execution of $V_n$ has at most $q(n)$ queries and $c(n)$ communicated bits in the worst case. Zero values are permitted. These predicates separate validity from cost, without assuming a lower bound or a description-length claim.
-- source:
--   Noga Amit, Oded Goldreich, STOC 2027 submission #297 (October 2026), pp. 5–7, Definition 2.1, complexity measures, and convention for lower bounds (PDF pp. 7–9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/297.pdf

import Definitions.Def_IPPComplexities_Unconditional_interaction

namespace IPPComplexities.Unconditional

abbrev System := (n : ℕ) → Verifier n
abbrev VerifierFamily := (n : ℕ) → ℝ → Verifier n

/-- Full 2/3 completeness and soundness, at a fixed positive proximity.
No condition is imposed on nonmembers that are close to the property. -/
def ValidAt (L : Property) (ε : ℝ) (V : System) : Prop :=
  0 < ε ∧ ∀ (n : ℕ) (x : Input n),
    (inputList x ∈ L → ∃ P : Prover, (2 : ℝ) / 3 ≤ verdictProbability (V n) x P true) ∧
    (Far L ε x → ∀ P : Prover, (2 : ℝ) / 3 ≤ verdictProbability (V n) x P false)

/-- Definition 2.1 with every positive proximity parameter. -/
def Valid (L : Property) (V : VerifierFamily) : Prop :=
  ∀ ε : ℝ, 0 < ε → ValidAt L ε (fun n => V n ε)

def ResourceBounds (V : System) (q c : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, Bounded (V n) (q n) (c n)

end IPPComplexities.Unconditional


