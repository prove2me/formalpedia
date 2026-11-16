-- Prove2me | Definitions.Def_PSPACEOracleSynth_Main_Supplement_Injection
-- name    : PSPACEOracleSynth_Main_Supplement_Injection
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T14:28:17.812427+00:00
-- url     : https://prove2.me/theorems/47c0789f-6f2e-4516-b3dc-73d8f2bb06aa
-- title:
--   Boolean phase states and adaptive injection branches
-- statement:
--   For a Boolean function $f$ on $\ell$ bits, $Z_f|u\rangle=(-1)^{f(u)}|u\rangle$ and $|\varphi_f\rangle=2^{-\ell/2}\sum_u(-1)^{f(u)}|u\rangle$. The derivative is $\partial_vf(u)=f(u)\oplus f(u\oplus v)$.
--
--   An injection of $|\varphi_f\rangle$ applies CNOT from each input wire to the corresponding resource wire, then measures the resource. Its branch at outcome $v$ is the operator on the input with entries $\langle w|K_{f,v}|u\rangle=\sum_c\langle w,v|\mathrm{CNOT}|u,c\rangle\varphi_f(c)$, with no scalar or phase removed. The adaptive run multiplies the branches in chronological order, the function after outcome $v$ being $\partial_v$ of the current one.
-- source:
--   Sichen Wang, Unitary Synthesis with a PSPACE Oracle, STOC 2027 submission #1740 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1740.pdf, Section 7.1, pp. 38–39

import Mathlib
import Definitions.Def_PSPACEOracleSynth_Main_Supplement_Quantum
import Definitions.Def_UnitaryQIPPSPACE_Bits

open QAlgorithms QAlgorithms.Complexity
open scoped Matrix

noncomputable section

attribute [local instance] Classical.propDecidable

namespace PSPACEOracleSynth.Main.Supplement

/-! §7.1, pp. 38–39. Kets and normalized conditional actions retain global phase. -/

def derivative {l : ℕ} (v : Bits l) (f : Bits l → Bool) : Bits l → Bool :=
  fun u => xor (f u) (f (fun i => xor (u i) (v i)))

def phase {l : ℕ} (f : Bits l → Bool) : Op (Bits l) :=
  Matrix.diagonal fun u => if f u then -1 else 1

noncomputable def phaseState {l : ℕ} (f : Bits l → Bool) : Bits l → ℂ :=
  fun u => (Real.sqrt ((2 : ℝ)^l))⁻¹ * (if f u then -1 else 1)

/-- The branch of one injection (p. 38): with the resource register C holding |φ_f⟩, apply a CNOT
from each qubit of X onto the corresponding qubit of C and obtain outcome v when measuring C.
Its operator on X has entries ⟨w|K_v|u⟩ = Σ_c ⟨w, v| CNOT |u, c⟩ φ_f(c), where CNOT maps
|u, c⟩ to |u, c ⊕ u⟩. It is subnormalized; no scalar or phase is removed. -/
noncomputable def injection {l : ℕ} (f : Bits l → Bool) (v : Bits l) : Op (Bits l) :=
  fun w u => ∑ c : Bits l,
    (if w = u ∧ (fun i => xor (c i) (u i)) = v then (1 : ℂ) else 0) * phaseState f c

def derivativeAt {l : ℕ} (f : Bits l → Bool) (history : List (Bits l)) : Bits l → Bool :=
  history.foldl (fun g v => derivative v g) f

/-- Chronological adaptive injection product, with ℓ+1 outcomes in Lemma 7.2. -/
def injectionRun {l : ℕ} (f : Bits l → Bool) : List (Bits l) → Op (Bits l)
  | [] => 1
  | v :: vs => injectionRun (derivative v f) vs * injection f v

end PSPACEOracleSynth.Main.Supplement


