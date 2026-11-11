-- Prove2me | Definitions.Def_RandomOracleUnitarySynthesis_synthesis_resampling
-- name    : RandomOracleUnitarySynthesis_synthesis_resampling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:56:11.258868+00:00
-- url     : https://prove2.me/theorems/e3c1608f-3ae7-4b53-9416-6059087bfcb3
-- title:
--   Finite adaptive symmetric resampling and its entropy and energy
-- statement:
--   The input truth table $f$ is uniform. Visit each of its $M_0=2^{m_0}$ inputs once in a fixed order, carrying the current function and the selected set $S$. For $k>0$, put $\tau=r^2/(8k)$. At each input, force its value separately to zero and one. Resample with an independent fair bit precisely when both resulting influences are at most $\tau$, and record that input in $S$. At $k=0$ use threshold zero; every influence is zero and the procedure independently resamples all bits.
--
--   For a finite stochastic kernel $K$ producing $(S,f_S)$, the conditional entropy in bits and the expected squared displacement are
--
--   $$H(f_S\mid f)=\mathbb E_f H(\operatorname{law}(f_S\mid f)),\qquad \mathcal E(K)=\mathbb E_{f,(S,f_S)\sim K(f)}\|A_f-A_{f_S}\|_F^2.$$
--
--   The procedure, the complete path, and each step's energy are computed explicitly. Entropy uses the published base-two Shannon formula. A selected coordinate remains in $S$ when replacement returns its old value. No energy or entropy conclusion is a premise of the procedure.
-- source:
--   Andrew Huang, Akshar Ramkumar, John Wright, STOC 2027 submission #157 (October 2026), proof of Theorem 4.5 and Lemma 4.9, printed pp. 20–23 (PDF pp. 22–25); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/157.pdf; PDF SHA256 2f2d7fa67fe2665257ec12cb0d11d7e2a80752cdecc0484b26a311d1223c5d11

import Definitions.Def_RandomOracleUnitarySynthesis_synthesis_circuit
import Definitions.Def_FuchsVdGraaf_entropy

open scoped Matrix ComplexConjugate
noncomputable section

namespace RandomOracleUnitarySynthesis

open Classical

/-! The finite stochastic procedure from the proof of Theorem 4.5, printed pp.20–23
(PDF pp.22–25). Fair seeds are independent of the initial uniform truth table. -/
abbrev synthesis_Resampler (m₀ : ℕ) :=
  synthesis_Oracle m₀ → PMF (Finset (synthesis_Bits m₀) × synthesis_Oracle m₀)

/-- Fixed visit order, each input visited exactly once. The number of visits is
card {0,1}^m₀ = 2^m₀, not m₀. -/
def synthesis_order (m₀ : ℕ) : Fin (Fintype.card (synthesis_Bits m₀)) ≃ synthesis_Bits m₀ :=
  (Fintype.equivFin _).symm

/-- No division by zero in the zero-query case. Every influence then vanishes. -/
def synthesis_threshold (k : ℕ) (r : ℝ) : ℝ :=
  if k = 0 then 0 else r^2 / (8 * k)

/-- The acceptance gate tests BOTH forced bit values. -/
def synthesis_resampleAllowed {n m m₀ k : ℕ} (C : synthesis_Circuit n m m₀ k)
    (r : ℝ) (f : synthesis_Oracle m₀) (x : synthesis_Bits m₀) : Prop :=
  synthesis_influence C (Function.update f x false) x ≤ synthesis_threshold k r ∧
  synthesis_influence C (Function.update f x true) x ≤ synthesis_threshold k r

/-- The path carries its current function and the complete selected-coordinate set.
Selected coordinates remain in S even if the new fair bit equals the old bit. -/
def synthesis_resamplePath {n m m₀ k : ℕ} (C : synthesis_Circuit n m m₀ k)
    (r : ℝ) (f coins : synthesis_Oracle m₀) : ℕ → synthesis_Oracle m₀ × Finset (synthesis_Bits m₀)
  | 0 => (f, ∅)
  | i+1 =>
    let prev := synthesis_resamplePath C r f coins i
    if hi : i < Fintype.card (synthesis_Bits m₀) then
      let x := synthesis_order m₀ ⟨i,hi⟩
      if synthesis_resampleAllowed C r prev.1 x then
        (Function.update prev.1 x (coins x), insert x prev.2)
      else prev
    else prev

/-- An actual finite stochastic kernel, using independent fair bits at every visited input.
For k=0 all coordinates are resampled and the result is independent of f. -/
def synthesis_resample {n m m₀ k : ℕ} (C : synthesis_Circuit n m m₀ k) (r : ℝ) :
    synthesis_Resampler m₀ :=
  fun f => (PMF.uniformOfFintype (synthesis_Oracle m₀)).map fun coins =>
    let out := synthesis_resamplePath C r f coins (Fintype.card (synthesis_Bits m₀))
    (out.2,out.1)

/-- Expectation under a genuine finite probability mass function; no integral defaults. -/
def synthesis_mean {A : Type} [Fintype A] (p : PMF A) (h : A → ℝ) : ℝ :=
  ∑ a, (p a).toReal * h a

/-- H(f_S | f) in BITS. Conditional on uniform f, the output law of f_S is the
second marginal of K f. Zero masses contribute zero in the published Shannon entropy. -/
def synthesis_conditionalEntropy {m₀ : ℕ} (K : synthesis_Resampler m₀) : ℝ :=
  synthesis_average fun f =>
    FuchsVdGraaf.entropy (fun g => ((K f).map Prod.snd g).toReal)

/-- Expected squared Frobenius displacement under uniform f followed by K f. -/
def synthesis_energy {n m m₀ k : ℕ} (C : synthesis_Circuit n m m₀ k)
    (K : synthesis_Resampler m₀) : ℝ :=
  synthesis_average fun f => synthesis_mean (K f) fun out =>
    QAlgorithms.frobNorm (synthesis_A C f - synthesis_A C out.2)^2

/-- Mean single-step energy of the concrete path, i counts from zero. -/
def synthesis_stepEnergy {n m m₀ k : ℕ} (C : synthesis_Circuit n m m₀ k)
    (r : ℝ) (i : ℕ) : ℝ :=
  synthesis_average fun f => synthesis_average fun coins =>
    QAlgorithms.frobNorm
      (synthesis_A C (synthesis_resamplePath C r f coins (i+1)).1 -
       synthesis_A C (synthesis_resamplePath C r f coins i).1)^2

end RandomOracleUnitarySynthesis


