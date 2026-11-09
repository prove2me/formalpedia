-- Prove2me | Definitions.Def_ZLIPPadding_Padding_FiniteRandomizer
-- name    : ZLIPPadding_Padding_FiniteRandomizer
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:59:28.450482+00:00
-- url     : https://prove2.me/theorems/0d401e57-9ae5-4e4d-a3af-4f1baf79dd68
-- title:
--   Finite Gram randomization and executable dimension-selection hypotheses
-- statement:
--   A randomizer implementation consists of finite code and one natural-coefficient polynomial clock. Its separate implementation hypothesis requires, for every promised $K$ and positive reciprocal precision $m$, all executions to halt with polynomial bit and output bounds, every nonfailure output to satisfy $H=U^TKU$ exactly with $U$ unimodular, and
--   $$d_{\mathrm{TV}}(\mathcal L(\text{finite output}),\mathcal L(\text{ideal output}))\leq 1/m.$$
--   The ideal law lives on all integer matrix pairs, satisfies joint stabilizer invariance and never fails. It is not assumed to be finitely supported. Any real tolerance $\varepsilon>0$ is realized by choosing an integer $m\geq\max(1,\lceil1/\varepsilon\rceil)$.
--
--   A dimension selector likewise consists of one finite deterministic program, one polynomial clock and its represented function $N(n)$. Its implementation hypothesis requires $N\geq n$, a fixed polynomial value bound and the source inequality $n\Gamma(N)^2/N\leq1/4$. Neither interface contains any vector-recovery, basis-recovery or sampling guarantee.
-- source:
--   Shengmao Jiang, STOC 2027 submission #496 (October 2026), printed pp. 28–29, 31–32 (PDF pp. 29–30, 32–33), Theorem 7.1 hypothesis and §7.2 finite implementation condition

import Definitions.Def_ZLIPPadding_Padding_BitMachine

namespace ZLIPPadding.Padding
noncomputable section
open scoped ENNReal

/-- Finite implementation data only. Its guarantees are a separate hypothesis. -/
structure RandomizerCode where
  code : Program
  clock : Polynomial ℕ

def randomFuel (R : RandomizerCode) {n : ℕ} (K : ZMat n) (m : ℕ) : ℕ :=
  R.clock.eval ((encGram K).length + n + m + 1)

def finiteLaw (R : RandomizerCode) {n : ℕ} (K : ZMat n) (m : ℕ) :
    PMF (Option (ZMat n × ZMat n)) :=
  decodedRun (decRandom n) R.code noOracle (randomFuel R K m) (encRequest K m 0)

/-- Reciprocal precision 1/m realizes every positive real tolerance by rounding m upward.
The ideal space contains all integer matrix pairs and is not truncated to finite outputs. -/
def FiniteImplementation (R : RandomizerCode) : Prop :=
  NoQueries R.code ∧ ∀ n (K : ZMat n), ValidGram K → ∀ m : ℕ, 0 < m →
    (∀ c, execute R.code noOracle (randomFuel R K m) (encRequest K m 0) c ≠ 0 →
      TraceBound (randomFuel R K m) c) ∧
    (∀ hu, finiteLaw R K m (some hu) ≠ 0 →
      Unimodular hu.2 ∧ hu.1 = hu.2.transpose * K * hu.2) ∧
    ∃ μ : PMF (ZMat n × ZMat n), IdealRandomization K μ ∧
      TVClose (finiteLaw R K m) (μ.map some) (1 / (m : ℝ))

/-- Uniform executable selector: no supplied hidden basis and no advice depending on n. -/
structure DimensionCode where
  code : Program
  clock : Polynomial ℕ
  dimension : ℕ → ℕ

def DimensionImplementation (Γ : ℕ → ℝ) (D : DimensionCode) : Prop :=
  NoQueries D.code ∧ NoCoins D.code ∧
  (∃ P : Polynomial ℕ, ∀ n, 0 < n → D.dimension n ≤ P.eval n) ∧
  ∀ n, 0 < n →
    n ≤ D.dimension n ∧ 1 ≤ Γ (D.dimension n) ∧
    (n : ℝ) * Γ (D.dimension n)^2 / (D.dimension n : ℝ) ≤ 1/4 ∧
    ∀ c, execute D.code noOracle (D.clock.eval (n+1)) (encNat n) c ≠ 0 →
      TraceBound (D.clock.eval (n+1)) c ∧ c.output = encNat (D.dimension n)

end
end ZLIPPadding.Padding


