-- Prove2me | Definitions.Def_DSICHardRev_Supplement_RandMechanism
-- name    : DSICHardRev_Supplement_RandMechanism
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:10:04.38417+00:00
-- url     : https://prove2.me/theorems/0c8757d4-ee1c-4344-8f8c-45dea9170c76
-- title:
--   Universally DSIC mechanisms as distributions over deterministic mechanisms
-- statement:
--   A **randomized mechanism** is a probability distribution $\mu$ over deterministic mechanisms (the base mission's communication protocols with strategy prescriptions and payments).
--
--   1. $\mu$ is **IR, NNT and universally DSIC** on a domain $\mathcal D$ (Definitions 2.8, 2.9, 2.12) if every deterministic mechanism in the support of $\mu$ is individually rational, has no negative transfers, and is dominant-strategy incentive compatible on $\mathcal D$ (prescribed play is optimal against every strategy profile of the others).
--   2. Its **expected welfare** on a profile $v$ is $\sum_{M}\mu(M)\cdot\sum_i v_i(S_i^{M}(v))$, where $S^{M}(v)$ is the allocation of $M$ under prescribed play.
--   3. It attains a **$\rho$-approximation** on $\mathcal D$ (Definition 2.2) if on every profile from $\mathcal D$ the expected welfare is at least $\rho$ times the optimal welfare $\max_{T}\sum_i v_i(T_i)$.
--   4. Its communication is the worst case over the support of the communication of the deterministic mechanisms.
--
--   This is the model of Theorems 1.5 and 1.7.
--
--   **Formalization Note** The distribution is a Mathlib `PMF`, so its support is countable and the expected welfare is a convergent series for every profile of non-negative monotone valuations. IR and NNT are required of every support element because the paper's IR and NNT "guarantee" their properties on every outcome. Statements quantify over the support for the communication instead of taking a supremum.
-- source:
--   Qiu, The Hardness of Dominant Strategy Mechanism Design, Revisited, arXiv:2610.06773 (version of 27 Oct 2026, sha256 a9f98f35…), §2.2 p.9: Definitions 2.7, 2.8, 2.9, 2.11, 2.12 and the convention on randomized deviations; Definition 2.2, pp.7–8

import Mathlib
import Definitions.Def_DSICHardRev_Protocol

namespace DSICHardRev

namespace Supplement

/-!
# Universally DSIC mechanisms: distributions over deterministic mechanisms

F. V. Qiu, *The Hardness of Dominant Strategy Mechanism Design, Revisited*, arXiv:2610.06773
(version of 27 Oct 2026, sha256 a9f98f35…), §2.2, p.9: Definitions 2.7 (mechanism, communication =
worst-case transcript length), 2.8 (IR), 2.9 (NNT), 2.11 (DSIC), 2.12 (universally DSIC), and
Definition 2.2 (approximation ratio, in expectation), pp.7–8.

**Formalization Note.**
* A randomized mechanism `RandMechanism N ι` is a probability distribution (`PMF`, hence with
  countable support) over the published deterministic mechanisms `Mechanism N ι`.
* `IsIRNNTUnivDSIC μ D` ("IR, NNT, universally DSIC on `D`"): every mechanism in the support of `μ`
  is IR, NNT and DSIC on `D` (the published `IsIR`, `IsNNT`, `IsDSIC`; DSIC is against **all**
  strategy profiles). IR and NNT "guarantee" their property on every outcome (Definitions 2.8,
  2.9, and the p.9 convention that a deviation is profitable as soon as some outcome is better),
  so they hold for every support element; universal DSIC is Definition 2.12 with `μ` as the
  witnessing distribution.
* `expWelfare μ v = ∑' M, μ(M) · welfare(M on v)`. For profiles from the domains used here
  (non-negative monotone valuations) the welfare is bounded by `∑ i, v i univ`, so the series is
  summable and this is the honest expectation.
* `IsApproxRatio μ D ρ`: on every profile from `D`, every allocation `T` satisfies
  `ρ · welfare(T) ≤ expWelfare μ v` (Definition 2.2, ratio `ρ = 1/η ≤ 1` as on p.8).
* The communication of `μ` is the worst case over its support of the published `Mechanism.comm`;
  statements quantify over the support instead of taking a supremum.
-/

/-- A randomized mechanism: a probability distribution over deterministic mechanisms. -/
abbrev RandMechanism (N ι : Type) : Type := PMF (Mechanism N ι)

namespace RandMechanism

variable {N ι : Type} [Fintype N] [DecidableEq N]

/-- Expected welfare of the randomized mechanism under prescribed play on the profile `v`. -/
noncomputable def expWelfare (μ : RandMechanism N ι) (v : N → Finset ι → ℝ) : ℝ :=
  ∑' M : Mechanism N ι, (μ M).toReal * Mechanism.welfare v (M.outcome v).alloc

/-- IR, NNT and universally DSIC on the domain `D` (Definitions 2.8, 2.9, 2.12): every
deterministic mechanism in the support is IR, NNT and DSIC on `D`. -/
def IsIRNNTUnivDSIC (μ : RandMechanism N ι) (D : Set (Finset ι → ℝ)) : Prop :=
  ∀ M ∈ PMF.support μ, M.IsIR D ∧ M.IsNNT D ∧ M.IsDSIC D

/-- The randomized mechanism attains a `ρ`-approximation on `D` (Definition 2.2): on every
profile from `D`, every allocation `T` satisfies `ρ · welfare(T) ≤ E[welfare]`. -/
def IsApproxRatio (μ : RandMechanism N ι) (D : Set (Finset ι → ℝ)) (ρ : ℝ) : Prop :=
  ∀ v : N → Finset ι → ℝ, (∀ j, v j ∈ D) →
    ∀ T : N → Finset ι, (Pairwise fun a b => Disjoint (T a) (T b)) →
      ρ * Mechanism.welfare v T ≤ expWelfare μ v

end RandMechanism

end Supplement

end DSICHardRev


