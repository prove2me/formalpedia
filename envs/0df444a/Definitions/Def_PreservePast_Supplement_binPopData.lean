-- Prove2me | Definitions.Def_PreservePast_Supplement_binPopData
-- name    : PreservePast_Supplement_binPopData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:31:35.074456+00:00
-- url     : https://prove2.me/theorems/611eb9da-723b-49e0-abf6-63354a1cda5f
-- title:
--   The binary population model: population, training data, test law, success, full-sample optimum, and the singleton information and entropy
-- statement:
--   In the **binary population model** the population $P$ has $n$ independent classes; independently for every class-coordinate it fixes a uniformly chosen sign with probability $\rho$. A labelled observation chooses a uniform class, uses its fixed signs, and draws independent uniform signs elsewhere. Given $P$, the training sample consists of $n$ independent observations, and the test pair is a fresh observation. The learner (a retained-state protocol) retains $M$ and predicts the fresh label from its feature and public coins.
--
--   This defines the learner's **success** ($1-$ population error), the **full-sample optimum** $1-L^\ast$, the informations $I(X_S;M\mid P,R)$ and $I(X;M\mid P,R)$ in bits ($X_S$ the singleton list `singList`, $X$ the whole sample), and the conditional entropy $H(X_S\mid P)$ in bits.
--
--   **Formalization Note** The cube $\{-1,1\}^d$ is `Fin d → Bool`. The latent variable is (which class-coordinates are fixed, a sign for every class-coordinate, the labels, the fresh signs of the observations); the population $P$ is the pair (fixed pattern, signs of the fixed coordinates). Conditional entropy is the finite sum $\sum p(a,b)\log_2(p(b)/p(a,b))$.
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb55cb5da782f256c3a4d1c95195bee48a2f4d0b2ed1e22bccd96d00fa), §K.2, p.57 (PDF p.59); §K.1, p.56 (PDF p.58)

import Mathlib
import Definitions.Def_PreservePast_Supplement_StateProtocol
import Definitions.Def_PreservePast_Supplement_singList

open MeasureTheory ProbabilityTheory
open scoped Classical

namespace PreservePast.Supplement

/-- The law on `Bool` giving mass `p` to `true` and `1 − p` to `false` (used for `0 ≤ p ≤ 1`). -/
noncomputable def bernMeasure (p : ℝ) : Measure Bool :=
  Real.toNNReal p • Measure.dirac true + Real.toNNReal (1 - p) • Measure.dirac false

instance (p : ℝ) : IsFiniteMeasure (bernMeasure p) := by
  unfold bernMeasure; infer_instance

/-- The latent variable `(fixed, sign, A, U)` of the binary population model: for every
class-coordinate `(j, c)` whether it is fixed and the uniformly chosen sign; the `n` training
labels `A_i ∈ [n]`; and the fresh signs `U_i ∈ {−1,1}^d` of the `n` observations. The cube
`{−1,1}^d` is `Fin d → Bool`. -/
abbrev BinPopLatent (n d : ℕ) : Type :=
  (Fin n → Fin d → Bool) × (Fin n → Fin d → Bool) × (Fin n → Fin n) × (Fin n → Fin d → Bool)

/-- The law of the latent variable: every class-coordinate is fixed independently with
probability `ρ`; all signs are independent and uniform; the labels are independent and uniform
on `[n]`. -/
noncomputable def binPopLaw (n d : ℕ) [NeZero n] (ρ : ℝ) : Measure (BinPopLatent n d) :=
  (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => bernMeasure ρ).prod
    ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => bernMeasure (1 / 2)).prod
      ((Measure.pi fun _ : Fin n => (PMF.uniformOfFintype (Fin n)).toMeasure).prod
        (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => bernMeasure (1 / 2))))

instance (n d : ℕ) [NeZero n] (ρ : ℝ) : IsFiniteMeasure (binPopLaw n d ρ) := by
  unfold binPopLaw; infer_instance

/-- **The population `P`** of the binary model: for every class-coordinate, whether it is fixed
and, if so, its sign (`(false, false)` for a free coordinate). -/
def binPopView {n d : ℕ} (l : BinPopLatent n d) : Fin n → Fin d → Bool × Bool :=
  fun j c => (l.1 j c, l.1 j c && l.2.1 j c)

/-- **The labelled training data of the binary population model.** P. Xu, *Information Required
to Preserve Past Learning*, STOC 2027 submission (held version, PDF sha256 48013ceb…d00fa), §K.2,
p.57 (PDF p.59): "the population P has n independent classes. Independently for every
class-coordinate, it fixes a uniformly chosen sign with probability ρ. A labeled observation
chooses a uniform class, uses its fixed signs, and draws independent uniform signs elsewhere.
Given P, training consists of n independent observations." -/
def binPopData {n d : ℕ} (l : BinPopLatent n d) : Fin n → Fin n × (Fin d → Bool) :=
  fun i => (l.2.2.1 i, fun c => if l.1 (l.2.2.1 i) c then l.2.1 (l.2.2.1 i) c else l.2.2.2 i c)

/-- The **test law** given the latent variable: a fresh labelled observation of the same
population (uniform class `a`; its fixed signs; independent uniform signs elsewhere). The joint
law of (feature, label). -/
noncomputable def binPopTest {n d : ℕ} (l : BinPopLatent n d) : Measure ((Fin d → Bool) × Fin n) :=
  ∑ a : Fin n, ((n : ENNReal))⁻¹ •
    (Measure.pi fun c : Fin d =>
      if l.1 a c then Measure.dirac (l.2.1 a c) else bernMeasure (1 / 2)).map (fun z => (z, a))

/-- The **success** `1 − error` of a learner in the binary population model (§K.2: "The learner
retains M and predicts a fresh label from its feature and public coins R ⊥ (P, X). Error averages
over the population, sample, query, and learner randomness"). -/
noncomputable def binPopSuccess {n d : ℕ} [NeZero n]
    (π : StateProtocol (Fin n → Fin n × (Fin d → Bool)) (Fin d → Bool) (Fin n)) (ρ : ℝ) : ℝ :=
  π.success (binPopLaw n d ρ) binPopData binPopTest

/-- The **full-sample optimum** `1 − L*` (§K.2: "L* is the full-sample optimum"). -/
noncomputable def binPopOptimum (n d : ℕ) [NeZero n] (ρ : ℝ) : ℝ :=
  fullDataOptimum (Out := Fin n) (binPopLaw n d ρ) binPopData binPopTest

/-- `I(X_S; M | P, R)` in bits, `X_S` the singleton list `singList` (§K.1, p.56). -/
noncomputable def binPopSingInfo {n d : ℕ} [NeZero n]
    (π : StateProtocol (Fin n → Fin n × (Fin d → Bool)) (Fin d → Bool) (Fin n)) (ρ : ℝ) : ENNReal :=
  π.info (binPopLaw n d ρ) binPopData (fun l => singList (binPopData l)) binPopView

/-- `I(X; M | P, R)` in bits, `X` the whole training sample. -/
noncomputable def binPopFullInfo {n d : ℕ} [NeZero n]
    (π : StateProtocol (Fin n → Fin n × (Fin d → Bool)) (Fin d → Bool) (Fin n)) (ρ : ℝ) : ENNReal :=
  π.info (binPopLaw n d ρ) binPopData binPopData binPopView

/-- **Conditional entropy in bits** `H(f | g)` of two finite-valued functions of a variable with
law `ν`: `Σ_{a,b} p(a,b) log₂(p(b)/p(a,b))`, with the convention `0 log 0 = 0` (a term with
`p(a,b) = 0` is `0` in Lean). -/
noncomputable def condEntropyBitsOf {Λ A B : Type} [MeasurableSpace Λ] [Fintype A] [Fintype B]
    (ν : Measure Λ) (f : Λ → A) (g : Λ → B) : ℝ :=
  ∑ b : B, ∑ a : A, (ν {l | f l = a ∧ g l = b}).toReal *
    Real.logb 2 ((ν {l | g l = b}).toReal / (ν {l | f l = a ∧ g l = b}).toReal)

/-- `H(X_S | P)` in bits in the binary population model (193). -/
noncomputable def binPopSingEntropy (n d : ℕ) [NeZero n] (ρ : ℝ) : ℝ :=
  condEntropyBitsOf (binPopLaw n d ρ) (fun l => singList (binPopData l)) binPopView

end PreservePast.Supplement


