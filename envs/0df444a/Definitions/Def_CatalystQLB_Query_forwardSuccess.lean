-- Prove2me | Definitions.Def_CatalystQLB_Query_forwardSuccess
-- name    : CatalystQLB_Query_forwardSuccess
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:21:47.572822+00:00
-- url     : https://prove2.me/theorems/99924114-f4aa-44ef-bba0-10b6a0f64008
-- title:
--   Average success probability of an oracle circuit on problem $\mathcal P$
-- statement:
--   Problem $\mathcal P$ of Lemma 8: given $|x,0^\lambda\rangle\langle x,0^\lambda|_{IO}\otimes\eta$, produce $|x,f(g(x))\rangle$ on the IO register, with the catalyst left in any state. For an oracle circuit $C$ with unitary $U=U_{f,g}$ and a catalyst operator $\eta$, the average success probability is
--   $$\mathrm{succ}(C,\eta)=\mathbb E_{f,g,x}\,\mathrm{tr}\Big[\big(|x,f(g(x))\rangle\langle x,f(g(x))|\otimes I_C\big)\,U\big(|x,0^\lambda\rangle\langle x,0^\lambda|\otimes\eta\big)U^\dagger\Big].$$
--   Nothing is required of the final catalyst, and the catalyst need not be restored.
--
--   This is the quantity Lemma 8 bounds, for $\eta=\eta_{\ell,p}$.
--
--   **Formalization Note** The real part of the trace is taken; for a density matrix $\eta$ the trace is real and lies in $[0,1]$.
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), Lemma 8 and its preamble, p.12 (PDF 15); Eq. (41), p.44 (PDF 47)

import Mathlib
import Definitions.Def_CatalystQLB_Query_OracleCircuit
import Definitions.Def_CatalystQLB_Query_expectFGX

open scoped Matrix

namespace CatalystQLB.Query

open QAlgorithms

/-- The average success probability of the circuit `C` on problem `P` of Lemma 8
(Arora, Chakraborty, Cojocaru, Saminathan, Singh, *Computational Work Extraction: The Complexity of Catalysts*, arXiv:2609.40323 (version of 2026-11-03), Lemma 8 and its preamble, p.12 (PDF 15): "Given `|x, 0^λ⟩⟨x, 0^λ|_IO ⊗ η_{ℓ,p}` produce
`|x, f(g(x))⟩⟨x, f(g(x))|_IO ⊗ |ψ⟩⟨ψ|_catalyst` where `|ψ⟩` is arbitrary"):
`E_{f,g,x} tr[(|x, f(g(x))⟩⟨x, f(g(x))| ⊗ I_C) U (|x, 0^n⟩⟨x, 0^n| ⊗ η) U†]`, `U = eval C f g`.

**Formalization Note** The IO register is `Q ⊗ R`; `0 : Qubits n` is the all-`false` string
`0^n`. The final catalyst is unconstrained (the projector is `I_C` on `C`), and no restoration
of the catalyst is required. The real part of the trace is taken; for a density matrix `η` the
trace is real and lies in `[0, 1]`. `η` is any matrix on `C`; the paper takes `η = η_{ℓ,p}`. -/
noncomputable def forwardSuccess {n ℓ : ℕ} (C : OracleCircuit n ℓ)
    (η : Matrix (Qubits ℓ) (Qubits ℓ) ℂ) : ℝ :=
  expectFGX n fun f g x =>
    (Matrix.trace
      (Matrix.kronecker (Matrix.single (x, f (g x)) (x, f (g x)) (1 : ℂ))
          (1 : Matrix (Qubits ℓ) (Qubits ℓ) ℂ) * C.eval f g *
        Matrix.kronecker (Matrix.single (x, (0 : Qubits n)) (x, (0 : Qubits n)) (1 : ℂ)) η *
        (C.eval f g)ᴴ)).re

end CatalystQLB.Query


