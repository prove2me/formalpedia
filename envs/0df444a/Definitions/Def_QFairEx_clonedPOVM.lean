-- Prove2me | Definitions.Def_QFairEx_clonedPOVM
-- name    : QFairEx_clonedPOVM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:23:39.943549+00:00
-- url     : https://prove2.me/theorems/f87a5a71-04ea-4342-9c0c-997fc89cbd38
-- title:
--   Guessing a BB84 basis from two copies (Algorithm 4.6) as a measurement
-- statement:
--   **Algorithm 4.6** ($A_{\mathrm{cloned}}$) receives two qubits: it samples $d\in\{0,1\}$ uniformly, measures both qubits in the computational basis if $d=0$ and in the Hadamard basis if $d=1$, obtaining $y_1,y_2$, and outputs $\theta^*=d$ if $y_1=y_2$ and $\theta^*=1-d$ otherwise.
--
--   Its outcome $g$ corresponds to the measurement operator
--   $$M_g=\sum_{d,y_1,y_2:\ \theta^*(d,y_1,y_2)=g}\tfrac12\,|b_{d,y_1}b_{d,y_2}\rangle\langle b_{d,y_1}b_{d,y_2}|,$$
--   where $b_{d,y}=H^dX^y|0\rangle$ is the basis-$d$ vector with outcome $y$. On a two-qubit state $\rho$, the algorithm outputs $g$ with probability $\operatorname{Re}\operatorname{tr}(M_g\rho)$.
--
--   Theorem 4.7 shows that on two copies of a BB84 state it recovers the basis with probability $3/4$.
-- source:
--   Chung, Lee, Raizes, Thyagarajan, Quantum Fair Exchange, STOC 2027 submission (manuscript of 2026-11-02, sha256 0099b883bc58c8a8ab3f2031fadc6e6c71b4ef1289bb55028fbbebcd070a9b6e), Algorithm 4.6, pp.21–22

import Mathlib
import Definitions.Def_QFairEx_SupportedOn
import Definitions.Def_QFairEx_bb84

namespace QFairEx

open Matrix

/-- **Algorithm 4.6 (`A_cloned`) as a measurement**: the POVM element of answer `g`.
Chung, Lee, Raizes, Thyagarajan, *Quantum Fair Exchange*, STOC 2027 submission (manuscript of
2026-11-02, sha256 0099b883…), Algorithm 4.6, pp.21–22: "1. Sample d ← {0, 1} uniformly.
2. Measure both registers in the computational basis if d = 0, and in the Hadamard basis if
d = 1. Let y1, y2 ∈ {0, 1} be the outcomes. 3. If y1 = y2, output θ* := d. Otherwise, output
θ* := 1 − d."

`clonedPOVM g = ∑_{d, y₁, y₂ : θ*(d,y₁,y₂) = g} ½ |b_{d,y₁} b_{d,y₂}⟩⟨b_{d,y₁} b_{d,y₂}|` on two
qubits (basis `Fin 2 × Fin 2`), where `b_{d,y} = H^d X^y |0⟩` is the basis-`d` vector with
outcome `y` (`d = 0`: `|y⟩`; `d = 1`: `|±⟩`) and `θ*(d, y₁, y₂) = d` if `y₁ = y₂`, `1 − d`
otherwise. The probability that Algorithm 4.6 outputs `g` on a two-qubit state `ρ` is
`Re tr(clonedPOVM g · ρ)`. -/
noncomputable def clonedPOVM (g : Bool) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ∑ d : Bool, ∑ y1 : Bool, ∑ y2 : Bool,
    if (if y1 = y2 then d else !d) = g then
      (1 / 2 : ℂ) • pureDensity (fun a : Fin 2 × Fin 2 => bb84 d y1 a.1 * bb84 d y2 a.2)
    else 0

end QFairEx


