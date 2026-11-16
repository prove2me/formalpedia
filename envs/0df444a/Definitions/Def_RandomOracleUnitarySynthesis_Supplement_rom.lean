-- Prove2me | Definitions.Def_RandomOracleUnitarySynthesis_Supplement_rom
-- name    : RandomOracleUnitarySynthesis_Supplement_rom
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T11:35:18.088083+00:00
-- url     : https://prove2.me/theorems/95064695-2b5f-4758-854f-aae0e3fa385d
-- title:
--   ROM-PRU channel couplings and eventual families
-- statement:
--   For an $n$-qubit base circuit $C$ with $k$ phase-oracle calls and arbitrary ancillas, let $\nu$ be a Borel unitary law and $\Gamma$ a coupling on pairs of channel coordinates. The ROM predicate requires $\nu$ to be a standard non-adaptive $T$-design with error $\delta$, $\Gamma$ to have probability mass one, and
--
--   $$\Gamma_1=\operatorname{Law}_f(\pi\circ\Phi_{W_f}\circ i),\qquad \Gamma_2=\operatorname{Law}_{U\sim\nu}(\Phi_U),\qquad D_\diamond(\Phi_1,\Phi_2)\le\varepsilon\quad\Gamma\text{-almost surely}.$$
--
--   Here $f$ is a uniformly random Boolean function on the base circuit's oracle register. The target need not be a deterministic function of $f$, as permitted in Remark 3.4. The non-adaptive condition is the weaker security model explicitly allowed by Remark 4.3. The eventual-family predicate adds $k\ge1$ and $0\le\varepsilon,\delta<1$ eventually, and does not impose any efficiency or ancilla bound. Query growth and the asymptotic gap condition remain separate hypotheses of the results.
--
--   This interface preserves the distinction between almost-sure implementation error and the base synthesis model's expected error.
-- source:
--   Andrew Huang, Akshar Ramkumar, John Wright, STOC 2027 submission #157 (October 2026), Definition 3.3 and Remark 3.4, printed pp. 14–15 (PDF pp. 16–17); Remark 4.3, printed p. 17 (PDF p. 19); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/157.pdf; published basis; PDF SHA256 2f2d7fa67fe2665257ec12cb0d11d7e2a80752cdecc0484b26a311d1223c5d11

import Definitions.Def_RandomOracleUnitarySynthesis_Supplement_designs
import Definitions.Def_RandomOracleUnitarySynthesis_synthesis_family

open MeasureTheory Filter
noncomputable section

namespace RandomOracleUnitarySynthesis.Supplement

/-- Definition 3.3, with Remarks 3.4 and 4.3 (printed pp.14–15,17 / PDF pp.16–17,19).
The unitary law ν and the CHANNEL coupling Γ remain explicit. The error guarantee
is almost sure, not averaged. The source's permitted generality removes deterministic
target assignment and requires only a standard non-adaptive design. -/
def IsROM {n m m₀ k : ℕ} (C : synthesis_Circuit n m m₀ k)
    (T : ℕ) (δ ε : ℝ) (ν : Measure (synthesis_Unitary n))
    (Γ : Measure (synthesis_Channel n × synthesis_Channel n)) : Prop :=
  StandardDesign ν T δ ∧ IsProbabilityMeasure Γ ∧
  Γ.map Prod.fst = (PMF.uniformOfFintype (synthesis_Oracle m₀)).toMeasure.map
    (synthesis_actualChannel C) ∧
  Γ.map Prod.snd = ν.map synthesis_unitaryChannel ∧
  ∀ᵐ pair ∂Γ, synthesis_diamond pair.1 pair.2 ≤ ε

/-- Theorem 4.2's eventual hypotheses, excluding its separate growth and gap regimes. -/
def ROMAdmissible (m m₀ k T : ℕ → ℕ)
    (C : (n : ℕ) → synthesis_Circuit n (m n) (m₀ n) (k n))
    (δ ε : ℕ → ℝ) (ν : (n : ℕ) → Measure (synthesis_Unitary n))
    (Γ : (n : ℕ) → Measure (synthesis_Channel n × synthesis_Channel n)) : Prop :=
  ∀ᶠ n in atTop, 1 ≤ k n ∧ 0 ≤ ε n ∧ ε n < 1 ∧ 0 ≤ δ n ∧ δ n < 1 ∧
    IsROM (C n) (T n) (δ n) (ε n) (ν n) (Γ n)

end RandomOracleUnitarySynthesis.Supplement


