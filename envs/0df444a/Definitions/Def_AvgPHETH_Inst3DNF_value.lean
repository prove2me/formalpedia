-- Prove2me | Definitions.Def_AvgPHETH_Inst3DNF_value
-- name    : AvgPHETH_Inst3DNF_value
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:26:34.0462+00:00
-- url     : https://prove2.me/theorems/7c3aee2d-dd41-45f6-bacb-65e148a192c5
-- title:
--   The value $\exists y\,\forall z\,\varphi(y,z)$
-- statement:
--   The truth value of the instance: there is an assignment to $y$ such that for every assignment to $z$ some term of $\varphi$ has all its literals true.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §1.1, p.2 (PDF 4)

import Mathlib
import Definitions.Def_AvgPHETH_Inst3DNF

namespace AvgPHETH

/-- The value of the `Σ₂SAT` instance: `∃y ∀z φ(y, z)` (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §1.1, p.2 (PDF 4)). -/
def Inst3DNF.value (φ : Inst3DNF) : Prop :=
  ∃ y : Fin φ.numY → Bool, ∀ z : Fin φ.numZ → Bool,
    ∃ τ ∈ φ.terms, ∀ lit ∈ τ, Fin.append y z lit.2 = lit.1

end AvgPHETH


