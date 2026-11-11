-- Prove2me | Definitions.Def_QNatProofs_al
-- name    : QNatProofs_al
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:59:32.541967+00:00
-- url     : https://prove2.me/theorems/19e3e9b6-2388-400c-b637-ae7d27d344f7
-- title:
--   The state amplitude list $\mathrm{al}_T(\psi)$
-- statement:
--   Let $|\psi\rangle=\sum_{x\in\{0,1\}^n}\alpha_x|x\rangle$ be an $n$-qubit state. For each $x$ write $\alpha_x = r_x e^{i2\pi\theta_x}$ with $r_x\in[0,1]$ and $\theta_x\in[0,1)$. For $T\in\mathbb N$, $\mathrm{al}_T(\psi)$ is "the binary string obtained by writing, for every $x\in\{0,1\}^n$, each of its polar coordinates to within $T$ fractional bits of precision, and concatenating these strings together", so
--   $$
--   \mathrm{al}_T(\psi)\in\big(\{0,1\}^{2T}\big)^{2^n}\cong\{0,1\}^{T2^{n+1}}.
--   $$
--   This is the classical description of a state that natural properties and PRAL distinguishers receive (Definitions 2.2 and 2.3).
--
--   **Formalization Note** The strings $x$ are listed in increasing order of the number they write, most significant bit first. For each $x$ the $T$ bits of $r_x$ come first, then the $T$ bits of $\theta_x$, each most significant bit first. A coordinate is written to $T$ bits by truncation: $\lfloor 2^T r_x\rfloor$, capped at $2^T-1$ so that $r_x=1$ (possible only for a basis state) is written $1\cdots1$, as the printed length $2T$ per amplitude requires; and $\lfloor 2^T\theta_x\rfloor$ with $\theta_x=\arg(\alpha_x)/(2\pi) \bmod 1$ and $\theta_x=0$ when $\alpha_x=0$.
-- source:
--   Li, Parham, Natural proofs for quantum state preparation lower bounds, arXiv:2610.06826 (held copy sha256 b604fa11…), Definition 2.1, p.8

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_PPADSIS_SubexpSIS_Encoding

set_option autoImplicit false

namespace QNatProofs

open QAlgorithms

/-- The `T` fractional bits of the magnitude `r ∈ [0, 1]`: the integer `⌊2^T r⌋`, capped at
`2^T − 1`, so that the code of `r = 1` is `1⋯1`. -/
noncomputable def magCode (T : ℕ) (r : ℝ) : ℕ :=
  min ⌊(2 : ℝ) ^ T * r⌋₊ (2 ^ T - 1)

/-- The phase coordinate `θ ∈ [0, 1)` of a complex number `α = |α| e^{i2πθ}`:
`θ = arg(α)/(2π) mod 1`, with `θ = 0` for `α = 0` (Mathlib's `arg 0 = 0`). -/
noncomputable def phaseCoord (α : ℂ) : ℝ :=
  Int.fract (Complex.arg α / (2 * Real.pi))

/-- The `T` fractional bits of the phase `θ ∈ [0, 1)`: the integer `⌊2^T θ⌋ < 2^T`. -/
noncomputable def phaseCode (T : ℕ) (θ : ℝ) : ℕ :=
  ⌊(2 : ℝ) ^ T * θ⌋₊

/-- **The state amplitude list `al_T(ψ)`** (Li, Parham, arXiv:2610.06826 (held copy sha256
b604fa11…), Definition 2.1, p.8): "For each `x`, let `r_x ∈ [0,1]` and `θ_x ∈ [0,1)` denote its polar
coordinates, so `α_x = r_x e^{i2πθ_x}`. For `T ∈ ℕ`, let `al_T(ψ)` denote the binary string obtained
by writing, for every `x ∈ {0,1}ⁿ`, each of its polar coordinates to within `T` fractional bits of
precision, and concatenating these strings together. Thus
`al_T(ψ) ∈ ({0,1}^{2T})^{2ⁿ} ≅ {0,1}^{T 2^{n+1}}`."

**Formalization Note** The basis strings `x` are listed in increasing order of the number they
write (most significant bit first, `QAlgorithms.bitsToNat`); for each `x` the `T` bits of `r_x`
come first, then the `T` bits of `θ_x`, each most significant bit first. A coordinate is written
to `T` fractional bits by truncation (`⌊2^T r⌋`); the magnitude `r_x = 1` (possible only for a basis
state) is written `1⋯1`, as the printed length `2T` per amplitude requires; `θ_x = 0` when
`α_x = 0`. -/
noncomputable def al (T : ℕ) {n : ℕ} (ψ : EuclideanSpace ℂ (Qubits n)) : List Bool :=
  (List.finRange (2 ^ n)).flatMap fun j =>
    let α := ψ ((bitsEquivFin n).symm j)
    PPADSIS.SubexpSIS.bitsBE T (magCode T ‖α‖) ++
      PPADSIS.SubexpSIS.bitsBE T (phaseCode T (phaseCoord α))

end QNatProofs


