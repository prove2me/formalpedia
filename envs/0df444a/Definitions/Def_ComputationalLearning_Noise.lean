-- Prove2me | Definitions.Def_ComputationalLearning_Noise
-- name    : ComputationalLearning_Noise
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-24T03:22:08.424987+00:00
-- url     : https://prove2.me/theorems/1bd7b57b-a14b-4a22-bc6d-8d629304f89f
-- title:
--   Chapter 5: the noisy oracle EX_CN, the value P_χ of a statistical query, the label-sensitive region X₁; p₀(z), p₀₁(z) and the conjunction of significant non-harmful literals
-- statement:
--   The objects of Chapter 5, on the framework of Missions I and IV.
--
--   **The noisy oracle (§5.1).** `noisyExampleLaw D c η` is the law of one example of $EX^\eta_{CN}(c, D)$: $x \sim D$ and, independently, the label $c(x)$ flipped with probability $\eta$ (a Bernoulli($\eta$) coin from Mission IV), so the pair is $(x, c(x))$ with probability $1-\eta$ and $(x, \neg c(x))$ with probability $\eta$.
--
--   **Statistical queries (§5.3).** A query is a predicate $\chi : X \times \{0,1\} \to \{0,1\}$; `queryProb D c χ` is $P_\chi = \Pr_{x \sim D}[\chi(x, c(x)) = 1]$. `labelSensitive χ` is $X_1 = \{x : \chi(x, 0) \ne \chi(x, 1)\}$, the inputs on which the label matters to $\chi$; its complement is $X_2$ (§5.4.1).
--
--   **Conjunctions from statistics (§5.2).** For a literal $z$ over $x_1, \dots, x_n$ (a pair `(i, b)`, set to $0$ in $a$ iff $a_i \ne b$), `zeroProb D z` is $p_0(z) = \Pr_{a \sim D}[z \text{ is } 0 \text{ in } a]$ and `zeroPosProb D c z` is $p_{01}(z) = \Pr[z \text{ is } 0 \text{ in } a \wedge c(a) = 1]$; `statisticsConj D c ε` is the conjunction of all the **significant** literals ($p_0(z) \ge \epsilon/8n$) that are **not harmful** ($p_{01}(z) < \epsilon/8n$).
--
--   **Conventions.** The noise rate is a real $\eta$; the theorems assume $0 \le \eta < 1/2$ (or $\le 1$ where only the Bernoulli coin must exist); probabilities are `toReal` of measures; the conditional $D[\cdot \mid X_1]$ is Mathlib's `cond` (zero measure when $D(X_1) = 0$).
-- source:
--   Kearns and Vazirani, An Introduction to Computational Learning Theory, MIT Press 1994, doi:10.7551/mitpress/3897.001.0001, Chapter 5: §5.1 the classification noise model (p. 104), §5.2 p₀, p₀₁, significant and harmful literals (p. 107), §5.3 statistical queries and P_χ (p. 109), §5.4.1 the regions X₁, X₂ (p. 112)

import Definitions.Def_ComputationalLearning_Boosting

/-!
# Kearns and Vazirani, Chapter 5: learning in the presence of noise

Kearns and Vazirani, *An Introduction to Computational Learning Theory*, MIT Press 1994,
doi:10.7551/mitpress/3897.001.0001, Chapter 5 (pp. 103–122).

**The classification noise model (§5.1, p. 104).** The noisy oracle `EX^η_CN(c, D)` draws `x ~ D`
and returns `(x, c(x))` with probability `1 − η` and `(x, ¬c(x))` with probability `η`, the noise
rate `η < 1/2` being fixed and the flips independent.

**Learning from statistics (§5.2, pp. 106–108).** For a literal `z`, `p₀(z)` is the probability that
`z` is set to `0` in a random instance and `p₀₁(z)` the probability that `z` is `0` and the instance
is positive; `z` is *significant* if `p₀(z) ≥ ε/8n` and *harmful* if `p₀₁(z) ≥ ε/8n`; the
conjunction of all significant, non-harmful literals has error at most `ε/2`.

**Statistical queries (§5.3, p. 109).** A statistical query is a predicate `χ : X × {0,1} → {0,1}`
(with a tolerance `τ`); its value is `P_χ = Pr_{x ~ D}[χ(x, c(x)) = 1]`, and the oracle `STAT(c, D)`
returns any estimate within `τ` of it.

**Simulating a query from noisy examples (§5.4.1, pp. 112–113).** Split `X` into `X₁`, the inputs
for which the label matters to `χ` (`χ(x, 0) ≠ χ(x, 1)`), and `X₂`. With `p₁ = D(X₁)`, `D₁` the
conditional of `D` on `X₁`, and probabilities under the noisy oracle, Equation (5.2) reads
`P_χ = p₁ (Pr_{EX_CN(c, D₁)}[χ = 1] − η)/(1 − 2η) + Pr_{EX_CN(c, D)}[χ = 1 ∧ x ∈ X₂]`, every term on
the right being estimable from noisy examples. For hypothesis selection (p. 117), the
probability that `h` disagrees with the noisy label is `γ_h = η + (1 − 2η) error(h)`.
-/

open MeasureTheory ProbabilityTheory

namespace ComputationalLearning

section Noise

variable {X : Type*} [MeasurableSpace X]

/-- The law of one example returned by the **noisy oracle** `EX^η_CN(c, D)`: `x ~ D` and the label
`c(x)` flipped with probability `η`, independently (§5.1, p. 104). -/
noncomputable def noisyExampleLaw (D : Measure X) (c : X → Bool) (η : ℝ) : Measure (X × Bool) :=
  (D.prod (bernoulliMeasure η)).map (fun p : X × Bool ↦ (p.1, if p.2 then !c p.1 else c p.1))

/-- `P_χ = Pr_{x ~ D}[χ(x, c(x)) = 1]`, the value of the statistical query `χ` (§5.3, p. 109). -/
noncomputable def queryProb (D : Measure X) (c : X → Bool) (χ : X × Bool → Bool) : ℝ :=
  (exampleLaw D c {p | χ p = true}).toReal

/-- `X₁`, the inputs on which the label matters to `χ`: `χ(x, 0) ≠ χ(x, 1)` (§5.4.1, p. 112). Its
complement is `X₂`. -/
def labelSensitive (χ : X × Bool → Bool) : Set X :=
  {x | χ (x, false) ≠ χ (x, true)}

end Noise

/-! ### Conjunctions from statistics (§5.2) -/

section Statistics

variable {n : ℕ}

/-- `p₀(z)`: the probability that the literal `z` is set to `0` (does not hold) in a random
instance (p. 107). -/
noncomputable def zeroProb (D : Measure (Cube (Fin n))) (l : Fin n × Bool) : ℝ :=
  (D {a | a l.1 ≠ l.2}).toReal

/-- `p₀₁(z)`: the probability that `z` is set to `0` and the instance is a positive example of the
target (p. 107). -/
noncomputable def zeroPosProb (D : Measure (Cube (Fin n))) (c : Cube (Fin n) → Bool)
    (l : Fin n × Bool) : ℝ :=
  (D {a | a l.1 ≠ l.2 ∧ c a = true}).toReal

/-- The conjunction of all **significant** (`p₀(z) ≥ ε/8n`) literals that are **not harmful**
(`p₀₁(z) < ε/8n`) (p. 107). -/
noncomputable def statisticsConj (D : Measure (Cube (Fin n))) (c : Cube (Fin n) → Bool) (ε : ℝ) :
    Conjunction (Fin n) :=
  Finset.univ.filter (fun l : Fin n × Bool ↦
    ε / (8 * n) ≤ zeroProb D l ∧ zeroPosProb D c l < ε / (8 * n))

end Statistics

end ComputationalLearning


