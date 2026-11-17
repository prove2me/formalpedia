-- Prove2me | Definitions.Def_AvoidPlast_Supplement_InIoSizeSAT
-- name    : AvoidPlast_Supplement_InIoSizeSAT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:54:30.488312+00:00
-- url     : https://prove2.me/theorems/586f4432-374e-4b1f-9d44-a0313bb42e8a
-- title:
--   The class $\mathrm{i.o.SIZE}^{\mathrm{SAT}}[s(n)]$
-- statement:
--   $L\in\mathrm{i.o.SIZE}^{\mathrm{SAT}}[s(n)]$ if for infinitely many $n$ some SAT-oracle circuit with at most $s(n)$ gates computes $L$ correctly on every $n$-bit input.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorems 1.3, 5.9, pp.4, 25

import Mathlib
import Definitions.Def_AvoidPlast_Supplement_SatGate
import Definitions.Def_AvoidPlast_Supplement_evalSatCircuit

namespace AvoidPlast.Supplement

open AvoidPlast

/-- `L ∈ i.o.SIZE^SAT[s(n)]` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Theorems 1.3, 5.9, pp.4, 25): for infinitely many `n`
some SAT-oracle circuit with at most `s(n)` gates computes `L` on every `n`-bit input. -/
def InIoSizeSAT (s : ℕ → ℝ) (L : Set (List Bool)) : Prop :=
  ∃ᶠ n : ℕ in Filter.atTop, ∃ gates : List SatGate, (gates.length : ℝ) ≤ s n ∧
    ∀ x : List Bool, x.length = n → (evalSatCircuit gates x = true ↔ x ∈ L)

end AvoidPlast.Supplement


