-- Prove2me | Definitions.Def_HardyLittlewood_series
-- name    : HardyLittlewood_series
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-19T21:31:46.789918+00:00
-- url     : https://prove2.me/theorems/5dc48820-e6da-435c-bd33-cc0784db55af
-- title:
--   Asymptotic equivalence, the singular series, and the first Hardy–Littlewood conjecture
-- statement:
--   The asymptotic layer of the first Hardy–Littlewood conjecture. Two real sequences are asymptotic when their difference is little-o of the second — the classical relation f ~ g when the model sequence is eventually positive and unbounded, degenerating correctly when the model vanishes identically. The singular series constant C_P of a tuple of offsets is 2^k times the product over the primes q ≥ 3 of (1 − w(q; m)/q) / (1 − 1/q)^(k+1), where w(q; m) counts the residues occupied by the offsets modulo q. The first Hardy–Littlewood conjecture for the tuple m states: if m₀ = 0 and the offsets are pairwise distinct, then the counting sequence π_P(n) is asymptotic to C_P times the integral of 1/(log t)^(k+1) from 2 to n.
-- source:
--   Formal Conjectures (2025), HardyLittlewood.lean, definition FirstHardyLittlewoodConjectureFor; Hardy and Littlewood (1923), Acta Math. 44, the singular series and the prime k-tuple conjecture

import Mathlib
import Definitions.Def_HardyLittlewood_constellation
import Definitions.Def_HardyLittlewood_counting

namespace HardyLittlewood

/-- Asymptotic equivalence of two real sequences along the filter atTop:
f ~ g means the difference f n − g n is little-o of g n as n → ∞. When g is
eventually positive and unbounded this is the classical relation f/g → 1;
the formulation through little-o also degenerates correctly when the model
vanishes identically. -/
def AsymptoticTo (f g : ℕ → ℝ) : Prop :=
  Asymptotics.IsLittleO Filter.atTop (fun n => f n - g n) g

/-- The singular series constant C_P of the tuple m: 2^k times the product
over the primes q ≥ 3 of (1 − w(q; m)/q) / (1 − 1/q)^(k+1), where w(q; m)
is the number of residues occupied by the offsets modulo q. -/
noncomputable def singularSeriesConstant {k : ℕ} (m : Fin k.succ → ℕ) : ℝ :=
  2 ^ k * ∏' (q : {q : ℕ // q.Prime ∧ 3 ≤ q}),
    (1 - (numResidues (q : ℕ) m : ℝ) / ((q : ℕ) : ℝ)) /
      (1 - 1 / ((q : ℕ) : ℝ)) ^ k.succ

/-- The first Hardy–Littlewood conjecture for the tuple m: if m₀ = 0 and the
offsets are pairwise distinct, then π_P(n) is asymptotic to C_P times the
integral of 1 / (log t)^(k+1) from 2 to n. -/
def firstHardyLittlewoodFor {k : ℕ} (m : Fin k.succ → ℕ) : Prop :=
  m 0 = 0 → Function.Injective m →
    AsymptoticTo (fun n => (primeTupleCounting m n : ℝ))
      (fun n => singularSeriesConstant m *
        ∫ t in (2:ℝ)..(n:ℝ), 1 / (Real.log t) ^ k.succ)

end HardyLittlewood


