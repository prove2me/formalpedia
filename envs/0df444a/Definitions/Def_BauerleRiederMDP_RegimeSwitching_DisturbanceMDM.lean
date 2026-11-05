-- Prove2me | Definitions.Def_BauerleRiederMDP_RegimeSwitching_DisturbanceMDM
-- name    : BauerleRiederMDP_RegimeSwitching_DisturbanceMDM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:22:58.733534+00:00
-- url     : https://prove2.me/theorems/8a7b672e-fd15-48a2-82eb-14d1d52fd067
-- title:
--   Markov Decision Model with disturbances $(E,A,D_n,Z,T_n,Q^Z_n,r_n)$
-- statement:
--   A (non-stationary) **Markov Decision Model with disturbances** consists of
--
--   1. a state space $E$ and an action space $A$ (measurable spaces);
--   2. for each time $n$ and state $x$ a set $D_n(x)\subseteq A$ of admissible actions;
--   3. a disturbance space $Z$ and a transition function $T_n:E\times A\times Z\to E$: if in state $x$ the action $a$ is taken and the disturbance $z$ occurs, the next state is $T_n(x,a,z)$;
--   4. a stochastic kernel $Q^Z_n(\cdot\mid x,a)$, the law of the disturbance $Z_{n+1}$;
--   5. one-stage rewards $r_n(x,a)$.
--
--   The terminal reward $g_N$ and the horizon $N$ are supplied when the value function is formed. This is Definition 2.1.1 in the equivalent form of Theorem 2.1.3, the form in which the book sets up all its financial models.
--
--   **Formalization Note** $T_n$ and $Q^Z_n$ are given on all of $E\times A$, $T_n$ is jointly measurable and $Q^Z_n$ is a Markov kernel. The book's requirement that $D_n$ be a measurable set containing the graph of a measurable map is a property of each concrete model and is not part of this structure.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Definition 2.1.1, p.14 (PDF p.29); Theorem 2.1.3, p.15 (PDF p.30)

import Mathlib
open MeasureTheory ProbabilityTheory

namespace BauerleRiederMDP.RegimeSwitching

/-- A (non-stationary) **Markov Decision Model with disturbances** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), Definition 2.1.1,
p.14, PDF p.29, in the equivalent form of Theorem 2.1.3, p.15, PDF p.30): the data
`(E, A, D_n, Z, T_n, Q^Z_n, r_n)` with state space `E`, action space `A`, admissible actions
`D_n(x) ⊆ A`, disturbance space `Z`, transition function `T_n(x, a, z)` (the next state when in
state `x` action `a` is taken and the disturbance `z` occurs), the law `Q^Z_n(· | x, a)` of the
disturbance `Z_{n+1}`, and the one-stage reward `r_n(x, a)`. The terminal reward `g_N` is not a
field: it is passed to `valueFunction`, together with the horizon `N`.

**Formalization Note.** Time is indexed by `ℕ`; only `n < N` matters for an `N`-stage problem.
`T_n` and `Q^Z_n` are given on all of `E × A` (the book needs them only on `D_n`), `T_n` is
jointly measurable and `Q^Z_n` is a Markov kernel. The book's requirements that `D_n` be a
measurable subset of `E × A` containing the graph of a measurable map are not fields: they are
properties of each concrete model and are not used to define the value functions. -/
structure DisturbanceMDM (E A Z : Type*) [MeasurableSpace E] [MeasurableSpace A]
    [MeasurableSpace Z] where
  /-- `D n x = D_n(x)`, the admissible actions in state `x` at time `n` -/
  D : ℕ → E → Set A
  /-- `T n (x, a) z = T_n(x, a, z)`, the transition function -/
  T : ℕ → E × A → Z → E
  measurable_T : ∀ n, Measurable (fun p : (E × A) × Z => T n p.1 p.2)
  /-- `QZ n (x, a) = Q^Z_n(· | x, a)`, the law of the disturbance `Z_{n+1}` -/
  QZ : ℕ → Kernel (E × A) Z
  isMarkovKernel_QZ : ∀ n, IsMarkovKernel (QZ n)
  /-- `r n (x, a) = r_n(x, a)`, the one-stage reward -/
  r : ℕ → E × A → ℝ

end BauerleRiederMDP.RegimeSwitching


