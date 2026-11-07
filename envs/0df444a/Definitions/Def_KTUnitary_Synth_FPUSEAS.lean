-- Prove2me | Definitions.Def_KTUnitary_Synth_FPUSEAS
-- name    : KTUnitary_Synth_FPUSEAS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:32:38.637303+00:00
-- url     : https://prove2.me/theorems/488b654e-4f86-40b9-81f0-1d6735dc5bd4
-- title:
--   FPUSEAS relative to a unitary oracle
-- statement:
--   An encoding function $f:\{0,1\}^*\to\mathbb R$ has a **fully polynomial unitary space exponential approximation scheme relative to $\mathcal O$** if there are a space-uniform family $\{C_{n,\varepsilon}\}$ of valid $\mathcal O$-oracle unitary circuits (with FPTEAS gate entries) on $n+\mathrm{poly}(n,\log1/\varepsilon)$ qubits and a designated output register of distinct wires, printed with the circuit, such that, for every $x\in\{0,1\}^n$, measuring the register of $C_{n,\varepsilon}|x\rangle|0^a\rangle$ gives a fixed-point number $\phi$ with $|\phi-f(x)|\le\varepsilon$ with probability at least $2/3$.
--
--   It is item 4 of Theorem 6.17.
--
--   **Formalization Note** $\varepsilon=2^{-\lambda}$; the register is a list of wires, read in order and decoded by `fixedPoint`.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Definition 6.1, p. 24

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_KTUnitary_Synth_HasFPTEAS
import Definitions.Def_KTUnitary_Synth_UCircuit
import Definitions.Def_KTUnitary_Synth_ancPad
import Definitions.Def_KTUnitary_Synth_measProb
import Definitions.Def_KTUnitary_Synth_SpaceUniform

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace KTUnitary.Synth

/-- **FPUSEAS relative to a unitary oracle `𝒪`** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Definition 6.1, p. 24): "An encoding
function `f : {0,1}* → ℝ` has a fully polynomial unitary space exponential approximation scheme …
if there is a family of space-uniform unitary quantum circuits `{C_{n,ε}}` on
`n + a(n, ε) ≤ poly(n, log 1/ε)` qubits such that for every `x ∈ {0,1}^n`, measuring a designated
output register of `C_{n,ε} |x⟩|0^a⟩` produces a fixed-point binary number `ϕ` satisfying
`|ϕ − f(x)| ≤ ε` with probability at least `2/3`. If `𝒪` is a unitary language, we say that `f` has an
FPUSEAS relative to `𝒪` if `{C_{n,ε}}` is instead a family of `𝒪`-oracle circuits."

Here: an encoding `g` with an FPTEAS for the gate entries, a space-uniform family `C n l` of valid
`𝒪`-oracle unitary circuits on `N` qubits with `n ≤ N ≤ n + p(n + l)`, and an output register
`out n l` (a list of wires), such that for every `x ∈ {0,1}^n`, the probability that the measured
register, decoded by `fixedPoint`, is within `2^{−l}` of `f(x)` is at least `2/3`.

**Formalization Note** `ε = 2^{−l}` (footnote 4, p. 14); `x` on the first `n` wires; the register
is read in list order. The output register is part of the family: its distinct wires are printed with
the circuit. A register chosen outside the description would be non-uniform advice: a free `out n l`
could read any number off constant wires. -/
def FPUSEAS (O : ULang) (f : Str → ℝ) : Prop :=
  ∃ (g : Str → ℝ) (C : ℕ → ℕ → UCircuit) (out : (n l : ℕ) → List (Fin (C n l).N))
    (p : Polynomial ℕ), HasFPTEAS g ∧
    SpaceUniform (fun nl : ℕ × ℕ => tup [unary nl.1, unary nl.2])
      (fun nl => tup [(C nl.1 nl.2).code, tup ((out nl.1 nl.2).map fun q => Nat.bits q)])
      (fun nl => (C nl.1 nl.2).gateCodes) ∧
    ∀ n l : ℕ, (C n l).Valid g ∧ (out n l).Nodup ∧ ∃ h : n ≤ (C n l).N, (C n l).N ≤ n + p.eval (n + l) ∧
      ∀ x : Bits n, (2 / 3 : ℝ) ≤
        measProb (((C n l).unitary g O).mulVec (ancPad h (Pi.single x 1)))
          (fun z => |((fixedPoint ((out n l).map z) : ℚ) : ℝ) - f (List.ofFn x)| ≤ (2 : ℝ)⁻¹ ^ l)

end KTUnitary.Synth


