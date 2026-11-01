-- Prove2me | Definitions.Def_WildeQIT_Covering_obfuscationError
-- name    : WildeQIT_Covering_obfuscationError
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:36:13.855777+00:00
-- url     : https://prove2.me/theorems/ade164b9-de8d-43ec-8fbd-b48d7b94dad6
-- title:
--   Obfuscation error $\mathrm{oe}(\mathcal C)=\|\sigma(\mathcal C)-\sigma\|_1$
-- statement:
--   For an ensemble $\{p_X(x),\sigma_x\}_{x\in\mathcal X}$ with expected density operator $\sigma$, and a code $\mathcal C=\{c_m\}_{m\in\mathcal M}$ with fake expected density operator $\sigma(\mathcal C)$, the **obfuscation error** of the code is the trace norm
--
--   $$\mathrm{oe}(\mathcal C)=\bigl\|\sigma(\mathcal C)-\sigma\bigr\|_1 .$$
--
--   It measures how well the fake ensemble imitates the true ensemble: a small obfuscation error means no measurement distinguishes the two expected states well.
--
--   **Formalization Note** $\|\cdot\|_1$ is the published `WildeQIT.traceNorm`, $\operatorname{Tr}\sqrt{M^\dagger M}$, without the factor $\tfrac12$, as in (17.10). The set version $\mathrm{oe}(S)$ is the case $\mathcal M=S$, $c_s=s$.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Definition 17.2.3 (Obfuscation Error), eq. (17.10), p. 507

import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_WildeQIT_Packing_expectedState
import Definitions.Def_WildeQIT_Covering_fakeState

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Definition 17.2.3
(Obfuscation Error), eq. (17.10), p. 507, and its code version (17.76), p. 514.
-/

open Matrix

namespace WildeQIT.Covering

/-- **Obfuscation error** (Wilde, arXiv:1106.1445v8, Definition 17.2.3, eq. (17.10), p. 507, and
eq. (17.76), p. 514). For an ensemble `{p_X(x), σ_x}` and a fake ensemble given by codewords
`c : M → 𝒳`, `oe(C) = ‖σ(C) − σ‖₁`, the trace norm of the difference between the fake expected
density operator `σ(C)` and the expected density operator `σ`.

**Formalization Note.** `‖·‖₁` is the published `WildeQIT.traceNorm`, unhalved, as in (17.10).
The set version `oe(S)` of Definition 17.2.3 is the instance `M = S`, `c = Subtype.val`. -/
noncomputable def obfuscationError {𝒳 n M : Type} [Fintype 𝒳] [Fintype n] [DecidableEq n]
    [Fintype M] (p : FinDist 𝒳) (σ : 𝒳 → Matrix n n ℂ) (c : M → 𝒳) : ℝ :=
  traceNorm (fakeState σ c - WildeQIT.Packing.expectedState p σ)

end WildeQIT.Covering


