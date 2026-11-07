-- Prove2me | Definitions.Def_KTUnitary_Synth_phaseEnc
-- name    : KTUnitary_Synth_phaseEnc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:29:12.68088+00:00
-- url     : https://prove2.me/theorems/25aed658-39e9-483f-8b41-6a03194bb678
-- title:
--   Phase encoding $f\mathrm{Phase}$
-- statement:
--   For $f:\{0,1\}^*\to\mathbb R$, the unitary language $f\mathrm{Phase}=\{R_{f,n}\}$ with
--   $$R_{f,n}|x\rangle=e^{i f(x)}|x\rangle\qquad(x\in\{0,1\}^n).$$
--   $\mathcal U\mathrm{EntryPhase}$ is item 2 of Theorem 6.17.
--
--   **Formalization Note** The paper takes $f$ with values in $[-\pi/2,\pi/2]$ "merely to ensure the encoding is unique"; the definition accepts any real $f$. The diagonal matrix is unitary (proved in the verification file).
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Definition 6.6, p. 25

import Mathlib
import Definitions.Def_KTUnitary_Synth_ULang

open QAlgorithms.Complexity

namespace KTUnitary.Synth

/-- **Phase encoding `fPhase`** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Definition 6.6, p. 25): "Let `f : {0,1}* → [−π/2, π/2]`. The
phase encoding of `f` is the unitary language `fPhase = {R_{f,n}}` defined by
`R_{f,n} |x⟩ = e^{i f(x)} |x⟩`, for every `x ∈ {0,1}^n`."

Here `R_{f,n}` is the diagonal matrix with entry `e^{i f(x)}` at the basis state `x` (read as the
string `x₀ x₁ ⋯ x_{n−1}`).

**Formalization Note** The definition takes any real-valued `f`: "The restriction to `[−π/2, π/2]`
is merely to ensure the encoding is unique" (p. 25). The diagonal matrix is unitary, so
`ULang.ofMatrices` returns it. -/
noncomputable def phaseEnc (f : Str → ℝ) : ULang :=
  ULang.ofMatrices fun _ => Matrix.diagonal fun x => Complex.exp ((f (List.ofFn x) : ℂ) * Complex.I)

end KTUnitary.Synth


