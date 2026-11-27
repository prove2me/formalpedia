-- Prove2me | Definitions.Def_GRH_LogarithmicMoebius
-- name    : GRH_LogarithmicMoebius
-- status  : Definition
-- author  : @scuba8684
-- created : 2026-11-27T06:47:15.441621+00:00
-- url     : https://prove2.me/theorems/5e71befb-4ad9-5ddd-8166-b57721951b7f
-- title:
--   Ordinary and logarithmically weighted Möbius sums in residue classes
-- statement:
--   For positive n up to N in a residue class a, sum the von Mangoldt function, the Möbius function, or the Möbius function weighted by log n. Write L(N) = 1 + log(N+1).
-- source:
--   Unconditional fixed-modulus estimates for the centered Möbius progression sum in https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 .

import Definitions.Def_GRH_AdditiveMoebiusSpectrum
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Log

namespace GRH.LogarithmicMoebius
open Finset
noncomputable section

def scale (N : ℕ) : ℝ := 1 + Real.log ((N : ℝ)+1)

def psi {q : ℕ} (a : ZMod q) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, if (n : ZMod q)=a then ArithmeticFunction.vonMangoldt n else 0

def residue {q : ℕ} (a : ZMod q) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, if (n : ZMod q)=a then (ArithmeticFunction.moebius n : ℝ) else 0

def residueLog {q : ℕ} (a : ZMod q) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, if (n : ZMod q)=a then (ArithmeticFunction.moebius n : ℝ)*Real.log n else 0

end
end GRH.LogarithmicMoebius


