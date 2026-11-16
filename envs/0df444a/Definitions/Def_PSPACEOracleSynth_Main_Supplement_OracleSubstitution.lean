-- Prove2me | Definitions.Def_PSPACEOracleSynth_Main_Supplement_OracleSubstitution
-- name    : PSPACEOracleSynth_Main_Supplement_OracleSubstitution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T14:30:55.903427+00:00
-- url     : https://prove2.me/theorems/5249f82c-bd38-43b7-ad04-6eaf8f964065
-- title:
--   Gate-set refinements of published clean and projective classes
-- statement:
--   This module refines the published polynomial-time clean and projective classes by requiring their witnessing circuits to be over $G=\{H,T,T^\dagger,\mathrm{CNOT}\}$ with coherent bit-oracle gates. It retains the original FPTEAS encoding, time-uniformity, polynomial width, and extension or dilation error $2^{-m}$.
--
--   The Boolean selector distinguishes clean extensions from projective dilations. The refinements express the preservation-of-$G$ clause of Corollary 5.2 without altering the immutable published classes.
-- source:
--   Sichen Wang, Unitary Synthesis with a PSPACE Oracle, STOC 2027 submission #1740 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1740.pdf, Corollary 5.2, p. 30

import Mathlib
import Definitions.Def_PSPACEOracleSynth_Main_Supplement_Classes
import Definitions.Def_PSPACEOracleSynth_Main_Dilation
import Definitions.Def_PSPACEOracleSynth_Main_GateSet
import Definitions.Def_KTUnitary_Synth_unitaryP

open QAlgorithms.Complexity QAdvFew.PoQOracle KTUnitary.Synth
open scoped Matrix
noncomputable section

namespace PSPACEOracleSynth.Main.Supplement

/-! Corollary 5.2, p. 30: refine the existing clean/projective class by requiring
its witnessing circuits to be over the exact gate set G. This does not redefine either class. -/

def timeSynthG (projective : Bool) (A : Oracle) : Set ULang :=
  {U | ∃ (f : Str → ℝ) (C : ℕ → ℕ → UCircuit) (p : Polynomial ℕ), HasFPTEAS f ∧
    TimeUniform (fun nl : ℕ × ℕ => tup [unary nl.1, unary nl.2])
      (fun nl => (C nl.1 nl.2).code) ∧
    ∀ n m, (C n m).Valid f ∧ OverG f (C n m) ∧
      ∃ h : n ≤ (C n m).N, (C n m).N ≤ n + p.eval (n+m) ∧
        ∃ Ub, (if projective then IsDilation h (U n : Matrix (Bits n) (Bits n) ℂ) Ub
          else IsExtension h (U n : Matrix (Bits n) (Bits n) ℂ) Ub) ∧
            opNorm (Ub - (C n m).unitary f (emb A)) ≤ (2 : ℝ)⁻¹ ^ m}

end PSPACEOracleSynth.Main.Supplement


