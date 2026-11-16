-- Prove2me | Definitions.Def_PSPACEOracleSynth_Main_Supplement_Choi
-- name    : PSPACEOracleSynth_Main_Supplement_Choi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T14:27:41.433068+00:00
-- url     : https://prove2.me/theorems/7c21bb22-70b9-4ed4-bbeb-6b5de446db4f
-- title:
--   Canonical Choi isometry and its explicit reflection
-- statement:
--   For a channel $C:A\to B$, the unnormalized, input-first Choi matrix is $J_C=\sum_{u,u'}|u\rangle\langle u'|\otimes C(|u\rangle\langle u'|)$. Its positive square root defines $Y_{v,i;u}=(\sqrt{J_C})_{u,v;i}$, with environment $E$ indexed like $AB$.
--
--   In $BE$, with $B$ first, the input is embedded on the first $n_{\rm in}$ wires and the remaining $2n_{\rm out}$ wires are zero. With a flag first, $Z=|0\rangle\otimes\iota-|1\rangle\otimes Y$ and $W=I-ZZ^\dagger$. One entry machine computes this particular family of reflections in space polynomial in $|x|+r+t$, with error $2^{-t}$ and $O(t+1)$ bits per dyadic component. No computability of the register sizes in polynomial time is assumed.
-- source:
--   Sichen Wang, Unitary Synthesis with a PSPACE Oracle, STOC 2027 submission #1740 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1740.pdf, Section 6.1, pp. 35–36

import Mathlib
import Definitions.Def_PSPACEOracleSynth_Main_Supplement_Classes
import Definitions.Def_PSPACEOracleSynth_Main_Dilation

open QAlgorithms QAlgorithms.Complexity QAdvFew.PoQOracle KTUnitary.Synth
open scoped Matrix ComplexOrder Kronecker

noncomputable section

attribute [local instance] Classical.propDecidable

namespace PSPACEOracleSynth.Main.Supplement

/-! §6.1, pp. 35–36: unnormalized input-first Choi matrix and the particular reflection. -/

noncomputable def choi {a b : ℕ} (C : Map (Bits a) (Bits b)) :
    Op (Bits a × Bits b) := fun p q => C (Matrix.single p.1 q.1 1) p.2 q.2

noncomputable def choiIso {a b : ℕ} (C : Map (Bits a) (Bits b)) :
    Matrix (Bits b × (Bits a × Bits b)) (Bits a) ℂ :=
  fun p u => (cfc Real.sqrt (choi C)) (u,p.1) p.2

/-- Input on the first a wires of B E, then 2b zero wires (B is first). -/
def choiEmbedding (a b : ℕ) : Matrix (Bits b × (Bits a × Bits b)) (Bits a) ℂ :=
  fun p u => if List.ofFn p.1 ++ List.ofFn p.2.1 ++ List.ofFn p.2.2 =
    List.ofFn u ++ List.replicate (2*b) false then 1 else 0

noncomputable def choiZ {a b : ℕ} (C : Map (Bits a) (Bits b)) :
    Matrix (Bool × (Bits b × (Bits a × Bits b))) (Bits a) ℂ :=
  fun p u => if p.1 then -choiIso C p.2 u else choiEmbedding a b p.2 u

/-- W=I−ZZ†, with no factor two in front of ZZ†, p. 35. -/
noncomputable def choiReflection {a b : ℕ} (C : Map (Bits a) (Bits b)) :
    Op (Bool × (Bits b × (Bits a × Bits b))) := 1 - choiZ C * (choiZ C)ᴴ

def reflectionLabel {a b : ℕ} (p : Bool × (Bits b × (Bits a × Bits b))) : Str :=
  [p.1] ++ List.ofFn p.2.1 ++ List.ofFn p.2.2.1 ++ List.ofFn p.2.2.2

/-- A single entry machine for the full explicit W family, not separate machines per x,r. -/
def ReflectionEntriesPSpace (C : Str → ℕ → GeneralCircuit) : Prop :=
  ∃ (M : OTM) (p : Polynomial ℕ) (c : ℕ), ∀ x r, 1 ≤ r →
    ∀ (u v : Bool × (Bits (C x r).output ×
      (Bits (C x r).input × Bits (C x r).output))) (t : ℕ),
    let inp := tup [x, unary r, reflectionLabel u, reflectionLabel v, unary t]
    ∃ T, M.result (fun _ => false) inp T ≠ none ∧
      M.space (fun _ => false) inp T ≤ p.eval (x.length + r + t) ∧
      ∃ re im : Str, M.output (fun _ => false) inp T = tup [re, im] ∧
        re.length ≤ c * (t+1) ∧ im.length ≤ c * (t+1) ∧
        ‖((fixedPoint re : ℂ) + (fixedPoint im : ℂ) * Complex.I) -
          choiReflection ((C x r).channel (fun _ => false) (C x r).input (C x r).output) u v‖ ≤
            (2 : ℝ)⁻¹ ^ t

end PSPACEOracleSynth.Main.Supplement


