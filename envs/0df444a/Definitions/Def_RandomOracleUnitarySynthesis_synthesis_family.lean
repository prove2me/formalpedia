-- Prove2me | Definitions.Def_RandomOracleUnitarySynthesis_synthesis_family
-- name    : RandomOracleUnitarySynthesis_synthesis_family
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:56:16.082042+00:00
-- url     : https://prove2.me/theorems/d25a3153-986f-4be5-a849-3e48e30cf7fd
-- title:
--   Channel-valued synthesis couplings and admissible asymptotic families
-- statement:
--   A random-oracle synthesis promise consists of a probability measure $\gamma$ on pairs of channels, with marginals equal to the uniform-oracle channel law and the Haar-unitary channel law, such that
--
--   $$\mathbb E_\gamma D_\diamond(\Phi_1,\Phi_2)\le\varepsilon.$$
--
--   The distance is integrated as a nonnegative Lebesgue integral. All channel laws use their ordinary Borel structures. No coupling independence, deterministic assignment of target unitaries, or almost-sure error bound is required.
--
--   A family has arbitrary natural functions $m(n),m_0(n),k(n)$ and a circuit of the corresponding sizes at every $n$. Admissibility requires $k(n)\ge1$, $\varepsilon(n)<1$, and the synthesis promise eventually; nonnegativity of the error is already part of the promise. The gap regime is $2^{2n}(1-\varepsilon(n))\to+\infty$. An inverse-polynomial gap means $(1-\varepsilon(n))^{-1}\le B(n+1)^d$ eventually. None of these definitions assumes a query lower bound or the existence of a net.
-- source:
--   Andrew Huang, Akshar Ramkumar, John Wright, STOC 2027 submission #157 (October 2026), Definition 3.6 and Theorem 4.1, printed p. 16 (PDF p. 18); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/157.pdf#page=18; PDF SHA256 2f2d7fa67fe2665257ec12cb0d11d7e2a80752cdecc0484b26a311d1223c5d11

import Definitions.Def_RandomOracleUnitarySynthesis_synthesis_circuit

open scoped ENNReal
open MeasureTheory Filter
noncomputable section

namespace RandomOracleUnitarySynthesis

/-! Definition 3.6, printed p.16 (PDF p.18), with Theorem 4.1's asymptotic
quantifiers made explicit. The coupling lives on CHANNEL coordinates themselves, so it
requires no deterministic target assignment and no lifting/disintegration theorem. -/

/-- Exactly the two channel marginals and the expected diamond-error promise.
A nonnegative Lebesgue integral avoids the default value of a nonintegrable Bochner integral.
Both marginals are supported on actual CPTP maps, where the distance lies in [0,1]. -/
def synthesis_IsSynthesis {n m m₀ k : ℕ} (C : synthesis_Circuit n m m₀ k) (ε : ℝ) : Prop :=
  0 ≤ ε ∧ ∃ γ : Measure (synthesis_Channel n × synthesis_Channel n),
    IsProbabilityMeasure γ ∧
    γ.map Prod.fst = (PMF.uniformOfFintype (synthesis_Oracle m₀)).toMeasure.map
      (synthesis_actualChannel C) ∧
    γ.map Prod.snd = (synthesis_haar n).map synthesis_unitaryChannel ∧
    (∫⁻ pair, ENNReal.ofReal (synthesis_diamond pair.1 pair.2) ∂γ) ≤ ENNReal.ofReal ε

/-- The full eventually admissible regime, with arbitrary m(n) and oracle length.
Every circuit's structural inequalities are carried by its type, not assumed conclusions. -/
def synthesis_Admissible (m m₀ k : ℕ → ℕ)
    (C : (n : ℕ) → synthesis_Circuit n (m n) (m₀ n) (k n)) (ε : ℕ → ℝ) : Prop :=
  ∀ᶠ n in atTop, 1 ≤ k n ∧ ε n < 1 ∧ synthesis_IsSynthesis (C n) (ε n)

/-- 1-ε = ω(N⁻²), i.e. N²(1-ε) tends to positive infinity. -/
def synthesis_GapRegime (ε : ℕ → ℝ) : Prop :=
  Tendsto (fun n : ℕ => ((2 : ℝ)^n)^2 * (1-ε n)) atTop atTop

/-- An arbitrary inverse-polynomial gap, with real nonnegative degree d. -/
def synthesis_PolynomialGap (ε : ℕ → ℝ) (B d : ℝ) : Prop :=
  ∀ᶠ n in atTop, (1-ε n)⁻¹ ≤ B * Real.rpow ((n : ℝ)+1) d

end RandomOracleUnitarySynthesis


