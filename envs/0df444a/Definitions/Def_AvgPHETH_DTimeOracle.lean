-- Prove2me | Definitions.Def_AvgPHETH_DTimeOracle
-- name    : AvgPHETH_DTimeOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:29:40.9382+00:00
-- url     : https://prove2.me/theorems/342163d5-bb3b-4eed-9fcf-3e7df637617f
-- title:
--   The class $\mathrm{DTIME}^{\mathcal C}[T]$
-- statement:
--   $L\in\mathrm{DTIME}^{\mathcal C}[T]$ if a deterministic machine with one oracle $B\in\mathcal C$ decides $L$, halting within $T(|x|)$ steps on every input $x$.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Theorem 1.2, p.3 (PDF 5); Lemma 6.5, p.29 (PDF 31)

import Mathlib
import Definitions.Def_KarpLiptonOM_OracleTM_HaltsWithin
import Definitions.Def_KarpLiptonOM_tupleEnc
import Definitions.Def_AvgPHETH_acceptsAt
open KarpLiptonOM

namespace AvgPHETH

/-- `L ∈ DTIME^C[T]`: a deterministic machine with one oracle `B ∈ C` decides `L` within `T(|x|)` steps
on every input `x` (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Theorem 1.2, p.3 (PDF 5); Lemma 6.5, p.29 (PDF 31)). -/
def DTimeOracle (C : Set (Set (List Bool))) (T : ℕ → ℕ) (L : Set (List Bool)) : Prop :=
  ∃ B ∈ C, ∃ M : OracleTM, ∀ x : List Bool,
    M.HaltsWithin B (T x.length) (tupleEnc [x]) ∧
      (x ∈ L ↔ acceptsAt M B (T x.length) (tupleEnc [x]))

end AvgPHETH


