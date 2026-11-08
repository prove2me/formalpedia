-- Prove2me | Definitions.Def_DPVerify_RandAlg
-- name    : DPVerify_RandAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:52:25.943182+00:00
-- url     : https://prove2.me/theorems/61bc6e93-761c-4fac-85a4-9214a598d5ca
-- title:
--   Randomized algorithm $\mathcal A:\mathcal X^m\to\mathcal Y$ with explicit coins and its output law
-- statement:
--   A **randomized algorithm** $\mathcal A:\mathcal X^m\to\mathcal Y$ takes a sample $S=(S_1,\dots,S_m)\in\mathcal X^m$ and internal coins $r$ drawn from a probability space $(\Omega,P)$, and outputs $\mathcal A(S,r)\in\mathcal Y$. Its **output law** on the sample $S$ is the distribution of $\mathcal A(S,r)$ for $r\sim P$:
--
--   $$
--   \mathcal A(S)\;:=\;\mathrm{Law}_{r\sim P}\bigl(\mathcal A(S,r)\bigr).
--   $$
--
--   The coins are explicit because replicability (Definition 2.5) compares two runs $\mathcal A(S,r)$ and $\mathcal A(S',r)$ that share the same internal randomness $r$. Max-information, one-way perfect generalization and differential privacy depend only on the output law.
--
--   **Formalization Note** $\mathcal X$ and $\mathcal Y$ are arbitrary measurable spaces, and the map $(S,r)\mapsto\mathcal A(S,r)$ is jointly measurable, so that every probability built from the algorithm is defined.
-- source:
--   Du, Dwork, Tankala, Zhang, Differentially Private Verification of Distribution Properties, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), §2, Definitions 2.3–2.5, p.5 (PDF p.8)

import Mathlib

set_option autoImplicit false

open MeasureTheory

namespace DPVerify

/-- A randomized algorithm `A : X^m → Y` with explicit internal coins (Du, Dwork, Tankala, Zhang, *Differentially Private Verification of Distribution Properties*, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), §2, Definitions 2.3–2.5,
p.5 = PDF p.8). The coins live in a probability space `(Ω, P)`, and `run S ω` is the output on the
sample `S ∈ X^m` with coins `ω`.

**Formalization Note** The coins are explicit because replicability (Definition 2.5) compares two
runs `A(S, r)`, `A(S′, r)` with the *same* internal randomness `r`. The map `(S, ω) ↦ run S ω` is
jointly measurable, which makes every probability below well defined; it restricts no algorithm
that has a law at all. Max-information and one-way perfect generalization depend only on the
output law `law A S`. -/
structure RandAlg (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y] (m : ℕ) where
  /-- the type of internal coins -/
  Ω : Type
  /-- the σ-algebra of the coins -/
  [mΩ : MeasurableSpace Ω]
  /-- the law of the coins -/
  P : Measure Ω
  [isProb : IsProbabilityMeasure P]
  /-- the output on sample `S` with coins `ω` -/
  run : (Fin m → X) → Ω → Y
  /-- joint measurability in the sample and the coins -/
  measurable_run : Measurable (Function.uncurry run)

attribute [instance] RandAlg.mΩ RandAlg.isProb

namespace RandAlg

variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {m : ℕ}

/-- The output law of `A` on the sample `S`: the law of `A(S, ω)` for `ω ∼ P`. -/
noncomputable def law (A : RandAlg X Y m) (S : Fin m → X) : Measure Y :=
  A.P.map (A.run S)

end RandAlg

end DPVerify


