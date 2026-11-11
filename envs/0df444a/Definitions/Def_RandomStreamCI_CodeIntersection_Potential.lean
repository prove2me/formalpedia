-- Prove2me | Definitions.Def_RandomStreamCI_CodeIntersection_Potential
-- name    : RandomStreamCI_CodeIntersection_Potential
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:30:21.91979+00:00
-- url     : https://prove2.me/theorems/be81e9eb-3ddc-44f4-b144-22dcb8a818af
-- title:
--   Threshold crossing potentials and integer ceiling
-- statement:
--   For a classical program, code $C$, threshold $\kappa$ and cutoff $\eta$, the vertex potential is the finite weighted sum
--
--   $$\Phi_{\eta,\kappa}(t)=\sum_{v,A}\Pr(E_{v,A})\sum_{c\in C:k_c\ge\kappa}2^{-(n-k_c)}[\Pr(H_{T_c\cap A}\equiv1\mid E_{v,A})-2\eta]^+.$$
--
--   The edge potential uses incoming-edge events instead. The completion factor remains outside the positive part. Thresholds are integers and the crossing threshold is exactly $\lceil\rho n+\log_2(1/\eta)/\gamma\rceil+1$. Potentials and posteriors are computed quantities, with no assumed growth inequality.
-- source:
--   Bouland–Ding–Jain, Exponential quantum space advantage in random data streams, STOC 2027 submission #71, preprint dated 2026-11-02, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/71.pdf, SHA256 3fe1835efedc1b9f29103379085d28d84ab1057dc30c3e3f05a8dce9f536a797, Definition 13 (29), p. 11; (36), p. 12; Lemma 17, p. 14

import Definitions.Def_RandomStreamCI_CodeIntersection_Branching

noncomputable section

namespace RandomStreamCI.CodeIntersection

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Definition 13, equation (29). All sums are finite; the completion factor
is OUTSIDE max. Exponent subtraction is in ℝ, not truncated ℕ subtraction. -/
def vertexPotential {n w : ℕ} {Alphabet : Type*} [Fintype Alphabet] [DecidableEq Alphabet]
    (B : BranchingProgram n Alphabet w) (C : Finset (Word n Alphabet)) (η : ℝ) (κ : ℤ) (t : ℕ) : ℝ :=
  ∑ v : Fin w, ∑ A ∈ Finset.univ.powersetCard t,
    streamProbability (B.vertexEvent t v A) *
      ∑ c ∈ C.filter (fun c => κ ≤ (observedCount c A : ℤ)),
        (2 : ℝ) ^ (-((n : ℝ) - observedCount c A)) *
          max (B.posterior t v A (fun H => value H c A = observedCount c A) - 2 * η) 0

/-- Equation (36), incoming-edge potential at time t+1. -/
def edgePotential {n w : ℕ} {Alphabet : Type*} [Fintype Alphabet] [DecidableEq Alphabet]
    (B : BranchingProgram n Alphabet w) (C : Finset (Word n Alphabet)) (η : ℝ) (κ : ℤ)
    (t : Fin (Fintype.card (Address n Alphabet))) : ℝ :=
  ∑ e : Fin w × Input n Alphabet, ∑ A ∈ Finset.univ.powersetCard (t.val + 1),
    streamProbability (B.edgeEvent t e A) *
      ∑ c ∈ C.filter (fun c => κ ≤ (observedCount c A : ℤ)),
        (2 : ℝ) ^ (-((n : ℝ) - observedCount c A)) *
          max (B.edgePosterior t e A (fun H => value H c A = observedCount c A) - 2 * η) 0

/-- The threshold of Lemma 17. The ceiling is integer-valued, with no truncation at zero. -/
def crossingThreshold (n : ℕ) (ρ γ η : ℝ) : ℤ :=
  ⌈ρ * n + log₂ (1 / η) / γ⌉ + 1

end RandomStreamCI.CodeIntersection


