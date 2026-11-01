-- Prove2me | Definitions.Def_WildeQIT_Schumacher_IsCompressionCode
-- name    : WildeQIT_Schumacher_IsCompressionCode
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:37:26.848181+00:00
-- url     : https://prove2.me/theorems/75926c66-9ede-4eb6-af06-47d1dba8a551
-- title:
--   $(n, R, \varepsilon)$ quantum compression code
-- statement:
--   A quantum compression protocol $C = (W,\mathcal E,\mathcal D)$ of block length $n$ is an $(n, R, \varepsilon)$ quantum compression code for the source $\rho$ when
--
--   1. the compressed system has size at most $2^{nR}$: $\dim\mathcal H_W \le 2^{nR}$ (the rate is $R = \frac1n\log\dim\mathcal H_W$, eq. (18.4));
--   2. its error (18.5) is at most $\varepsilon$.
--
--   **Formalization Note** The book's $\dim\mathcal H_W = 2^{nR}$ is read as $\dim\mathcal H_W \le 2^{nR}$, since a dimension is an integer and $2^{nR}$ generally is not. This changes no achievable rate: a code with a smaller $W$ embeds isometrically into a system of dimension $\lfloor 2^{nR}\rfloor$ with the same error. Logarithms are base 2.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §18.1, eqs. (18.4)–(18.5), p. 523

import Definitions.Def_WildeQIT_Schumacher_compressionError
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §18.1, eqs. (18.4)–(18.5),
p. 523.
-/

namespace WildeQIT.Schumacher

/-- **`(n, R, ε)` quantum compression code** (Wilde, arXiv:1106.1445v8, §18.1, p. 523). A
compression protocol `C` of block length `n` for the source `ρ` is an `(n, R, ε)` code when the
compressed system `W` has size at most `2^{nR}` (rate `R = (1/n) log dim(ℋ_W)`, eq. (18.4)) and
the protocol has error at most `ε` in the sense of (18.5):
`½ ‖(ϕ^ρ_{RA})^{⊗n} − (D ∘ E)((ϕ^ρ_{RA})^{⊗n})‖₁ ≤ ε`.

**Formalization Note.** The book's `dim(ℋ_W) = 2^{nR}` is read as `dim(ℋ_W) ≤ 2^{nR}`, since a
dimension is an integer and `2^{nR}` generally is not. This changes no achievable rate: a code
with a smaller `W` embeds isometrically into one with `dim(ℋ_W) = ⌊2^{nR}⌋` and the same error.
Logarithms are base 2. -/
def IsCompressionCode {a : Type} [Fintype a] [DecidableEq a] {n : ℕ} (ρ : Matrix a a ℂ)
    (R ε : ℝ) (C : CompressionCode a n) : Prop :=
  (C.d : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R) ∧ compressionError ρ C ≤ ε

end WildeQIT.Schumacher


