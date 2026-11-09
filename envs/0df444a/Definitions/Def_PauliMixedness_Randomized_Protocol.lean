-- Prove2me | Definitions.Def_PauliMixedness_Randomized_Protocol
-- name    : PauliMixedness_Randomized_Protocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:50:29.746531+00:00
-- url     : https://prove2.me/theorems/b5e933b3-9d86-45ea-b459-26c088e4dfda
-- title:
--   Nonadaptive Pauli schedule and outcome-only decision kernel
-- statement:
--   Fix $N$ and a copy count $n\ge0$. A protocol consists of a probability distribution $q$ on entire schedules $s=(P_1,\ldots,P_n)\in(\{X,Y,Z\}^N)^n$ and a function $a(s,x_1,\ldots,x_n)\in[0,1]$ giving the probability of declaring Maximally-Mixed. Neither datum accepts an unknown state as input. Define
--
--   $$\operatorname{Acc}_A(\rho)=\sum_s q(s)\sum_{x_1,\ldots,x_n}\left(\prod_{j=1}^n r_{\rho,P_j}(x_j)\right)a(s,x_1,\ldots,x_n).$$
--
--   This averages both shared schedule randomness and classical decision coins. Conditional on the schedule, every outcome comes from a fresh independent copy. Each measurement is the full product Pauli basis measurement. At $n=0$, empty products equal one and the decision is a state-independent coin. This is the source protocol class needed for the existential mixedness theorem; it carries no correctness fields. Algorithm 1 is solver guidance and is not defined here.
-- source:
--   Abhilash Dharmavarapu, Jayadev Acharya, Nengkun Yu, Yuhan Liu, STOC 2027 submission #231 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/231.pdf, §1.1 p.2 and Theorem 1.1 p.3

import Definitions.Def_PauliMixedness_Randomized_QuantumModel

noncomputable section
open scoped BigOperators

namespace PauliMixedness.Randomized

/-- §1.1 p.2: an entire schedule drawn before seeing the state or outcomes.
A finite distribution represents arbitrary shared seed randomness. -/
abbrev Schedule (N n : ℕ) := Fin n → Setting N

/-- §1.1: genuine nonadaptive sampling and outcome-only randomized decision data.
The kernel value is the chance of declaring Maximally-Mixed. In particular the
kernel cannot query the state, its coefficients, its influence or its law. -/
structure PauliProtocol (N n : ℕ) where
  scheduleLaw : PMF (Schedule N n)
  accept : Schedule N n → (Fin n → Cube N) → Set.Icc (0 : ℝ) 1

/-- Product Born law conditional on a schedule, averaged over the seed and
classical decision coins. Every schedule entry consumes one fresh copy. -/
def acceptProbability {N n : ℕ} (A : PauliProtocol N n) (ρ : Operator N) : ℝ :=
  ∑ s : Schedule N n, mass A.scheduleLaw s *
    ∑ x : Fin n → Cube N, (∏ j : Fin n, outcomeMass ρ (s j) (x j)) *
      (A.accept s x : ℝ)

end PauliMixedness.Randomized


