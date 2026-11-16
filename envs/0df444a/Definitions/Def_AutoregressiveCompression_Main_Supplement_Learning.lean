-- Prove2me | Definitions.Def_AutoregressiveCompression_Main_Supplement_Learning
-- name    : AutoregressiveCompression_Main_Supplement_Learning
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:08:59.105048+00:00
-- url     : https://prove2.me/theorems/e8550c6a-7b36-4d7f-aae8-7da4718ea577
-- title:
--   Uniform polynomial-time learning with evaluators and generators
-- statement:
--   Let $\mathcal D=(\mathcal D_n)_{n\in\mathbb N}$ be any size-indexed class of string distributions over a finite alphabet. A learner uses one finite Turing machine, one polynomial running-time bound, and fixed polynomial sample and fair-coin bounds. From unary $n,a,b$, where $a,b\ge2$, samples, and its coins, it outputs an explicitly encoded circuit. On every possible sample block and coin tape of these lengths the output must be a normalized evaluator, or a generator for the target length, respectively. It receives no description or probability table of the target distribution.
--
--   Writing $\varepsilon=1/a$ and $\delta=1/b$, one accuracy mode is fixed for the entire learner: either KL divergence in bits is at most $\varepsilon$ with probability at least $1-\delta$, or total variation distance is at most $\varepsilon$ with that probability. Thus
--
--   $$\Pr[\operatorname{KL}_2(D\Vert Q_H)\le\varepsilon]\ge1-\delta\quad\text{or}\quad\Pr[\Delta_{\rm tv}(D,Q_H)\le\varepsilon]\ge1-\delta.$$
--
--   The generic circuit-learning contract is instantiated separately with the two actual circuit encodings and their evaluated masses. It neither assumes nor asserts an interconversion between tasks. Its uniform witnesses precede every size, law, accuracy and confidence parameter. Infinite KL is retained by the published extended-real convention. These predicates extend the existing seven task interfaces without redefining them.
-- source:
--   Shuichi Hirahara, Mikito Nanashima, STOC 2027 submission #793 (October 2026); source.pdf, SHA-256 31e908b0cf51447e89626d9dc6d947c279aec5642ec7b320ceb07ec9b1348341; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/793.pdf, Definition 4.5, printed pp.17–18 / PDF pp.19–20

import Mathlib
import Definitions.Def_AutoregressiveCompression_Main_Supplement_Representations

noncomputable section

namespace AutoregressiveCompression.Main.Supplement

open scoped Classical

/-! Definition 4.5, printed pp.17–18 / PDF pp.19–20.
One finite machine outputs a circuit description from samples, unary parameters
and its fair coins. All polynomial bounds are fixed before n and the target.
The two modes of accuracy are alternatives for the whole learner, not per target.
-/

/-- Distribution learning with a specified, independently defined hypothesis
representation. `valid` expresses output typing/normalization only; `weights`
is the evaluated law, not a promise of accuracy or a task interconversion. -/
def CircuitLearnable {Sym H : Type} [Fintype Sym] (𝒟 : DistributionClass Sym)
    (encode : H → Bits) (valid : H → ℕ → Prop)
    (weights : H → (N : ℕ) → Word Sym N → ℝ) : Prop :=
  ∃ (L : Program) (time : Polynomial ℕ) (ρ r : MvPolynomial (Fin 3) ℕ)
    (hyp : ℕ → ℕ → ℕ → List (List Sym) → Bits → H),
    (∀ n, ∀ D ∈ 𝒟.members n, ∀ a b : ℕ, 2 ≤ a → 2 ≤ b →
      ∀ (xs : Fin (eval3 ρ n a b) → Word Sym D.length)
        (ω : Fin (eval3 r n a b) → Bool),
      L.OutputsWithin
        (frame [unary n, unary a, unary b, blockBits (blockList xs), coinBits ω])
        (encode (hyp n a b (blockList xs) (coinBits ω))) (time.eval (n + a + b)) ∧
      valid (hyp n a b (blockList xs) (coinBits ω)) D.length) ∧
    ((∀ n, ∀ D ∈ 𝒟.members n, ∀ a b : ℕ, 2 ≤ a → 2 ≤ b →
      1 - 1 / (b : ℝ) ≤ eventProbability
        (samplesAndCoins D.law (eval3 ρ n a b) (eval3 r n a b))
        (fun p => klBitsWeights D.law
          (weights (hyp n a b (blockList p.1) (coinBits p.2)) D.length) ≤
            ((1 / (a : ℝ) : ℝ) : EReal))) ∨
     (∀ n, ∀ D ∈ 𝒟.members n, ∀ a b : ℕ, 2 ≤ a → 2 ≤ b →
      1 - 1 / (b : ℝ) ≤ eventProbability
        (samplesAndCoins D.law (eval3 ρ n a b) (eval3 r n a b))
        (fun p => tvWeights D.law
          (weights (hyp n a b (blockList p.1) (coinBits p.2)) D.length) ≤ 1 / (a : ℝ))))

/-- Definition 4.5(a), using actual rational evaluator circuits. -/
def EvaluatorLearnable {Sym : Type} [Fintype Sym] (𝒟 : DistributionClass Sym) : Prop :=
  CircuitLearnable 𝒟 Circuit.bits (IsEvaluator (Sym := Sym)) evaluatorMass

/-- Definition 4.5(b), using actual finite vector-output circuits with fair seeds.
Only samples of the target are inputs to the learning program. -/
def GeneratorLearnable {Sym : Type} [Fintype Sym] (𝒟 : DistributionClass Sym) : Prop :=
  CircuitLearnable 𝒟 SamplerCode.bits (IsGeneratorAt (Sym := Sym)) SamplerCode.modelMass

end AutoregressiveCompression.Main.Supplement


