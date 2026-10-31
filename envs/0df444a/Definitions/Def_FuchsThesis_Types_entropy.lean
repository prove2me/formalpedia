-- Prove2me | Definitions.Def_FuchsThesis_Types_entropy
-- name    : FuchsThesis_Types_entropy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:20:55.451139+00:00
-- url     : https://prove2.me/theorems/a320aea0-3d03-4f96-b0d5-b8ea74d74f29
-- title:
--   Shannon entropy $H(p)$ in nats
-- statement:
--   For a function $p$ on a finite set $\mathcal B$, the **Shannon entropy** is
--
--   $$
--   H(p)=-\sum_{b\in\mathcal B}p(b)\ln p(b),
--   $$
--
--   with the natural logarithm and with $0\ln 0=0$. It is the exponential rate at which the number of strings with frequencies $p$ grows with $n$.
--
--   **Formalization Note** The term $-x\ln x$ is Mathlib's `Real.negMulLog`, which is $0$ at $x=0$. The definition applies to any real function; the theorems use it on frequency distributions and probability distributions only.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eq. (2.92), p.27

import Mathlib

set_option autoImplicit false

namespace FuchsThesis.Types

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, (2.92), p.27 (PDF 36): the Shannon entropy
`H(p) = -∑_b p(b) ln p(b)`, in nats.

**Formalization Note.** `Real.negMulLog x = -x * Real.log x`, so a term with `p b = 0` contributes
`0`, the usual `0 ln 0 = 0` of (2.92). Defined for any real function on a finite type; the theorems
apply it to frequency distributions and probability distributions only. -/
noncomputable def entropy {β : Type*} [Fintype β] (p : β → ℝ) : ℝ :=
  ∑ b, Real.negMulLog (p b)

end FuchsThesis.Types


