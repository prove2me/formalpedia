-- Prove2me | Definitions.Def_CatalystQLB_Query_decisionAdvantage
-- name    : CatalystQLB_Query_decisionAdvantage
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:22:07.438031+00:00
-- url     : https://prove2.me/theorems/b61362fb-a1c3-4f6c-bf9a-ea2413b0acc3
-- title:
--   Distinguishing advantage $\mathrm{succ}_{\mathrm{dec}}(\gamma)$ between $(x,f(g(x)))$ and $(x,r)$
-- statement:
--   For an oracle circuit with unitary $U=U_{f,g}$, a measurement operator $\Pi^{\mathrm{dec}}$ on all $2\lambda+\ell$ qubits, fixed independently of $f,g,x,r$, and an operator $\gamma$ on the catalyst register,
--   $$\mathrm{succ}_{\mathrm{dec}}(\gamma)=\Big|\,\mathbb E_{f,g,x}\,\mathrm{tr}\big[\Pi^{\mathrm{dec}}U(|x,f(g(x))\rangle\langle x,f(g(x))|\otimes\gamma)U^\dagger\big]-\mathbb E_{f,g,x,r}\,\mathrm{tr}\big[\Pi^{\mathrm{dec}}U(|x,r\rangle\langle x,r|\otimes\gamma)U^\dagger\big]\Big|,$$
--   where $r\in\{0,1\}^\lambda$ is uniform and independent. It is the advantage with which the circuit followed by the test $\Pi^{\mathrm{dec}}$ tells $(x,f(g(x)))$ from $(x,r)$: the decision variant of problem $\mathcal P$.
--
--   **Formalization Note** Real parts of the traces; the average over $r$ is a sum divided by $2^\lambda$. The theorems take $\Pi^{\mathrm{dec}}$ to be a projector (Hermitian and idempotent); Lemma 82's $\Pi^{\mathrm{dec}}\otimes I_C$ is a special case.
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), Lemma 121, Eq. (102), p.75 (PDF 78); Eq. (103), p.76 (PDF 79); Eq. (52), p.49 (PDF 52)

import Mathlib
import Definitions.Def_CatalystQLB_Query_OracleCircuit
import Definitions.Def_CatalystQLB_Query_expectFGX

open scoped Matrix

namespace CatalystQLB.Query

open QAlgorithms

/-- The distinguishing advantage of the circuit `C` followed by the measurement `Pdec`,
between `(x, f(g(x)))` and `(x, r)` with catalyst operator `γ` (Arora, Chakraborty, Cojocaru, Saminathan, Singh, *Computational Work Extraction: The Complexity of Catalysts*, arXiv:2609.40323 (version of 2026-11-03), Eq. (102), Lemma 121,
p.75 (PDF 78), and Eq. (103), p.76 (PDF 79)):
`succ_dec(γ) := | E_{f,g,x} tr[Π^dec U (|x, f(g(x))⟩⟨x, f(g(x))| ⊗ γ) U†]
  − E_{f,g,x,r} tr[Π^dec U (|x, r⟩⟨x, r| ⊗ γ) U†] |`, `U = eval C f g`, `r` uniform and
independent. For `γ = |0^ℓ⟩⟨0^ℓ|` this is Eq. (52).

**Formalization Note** `Pdec` is a matrix on all `2n + ℓ` qubits, fixed before the averages
(oracle independent); the theorems take it to be a projector. Lemma 82's `Π^dec ⊗ I_C` is a
special case. The average over `r` is the plain sum over `Qubits n` divided by `2^n`. Real
parts of the traces. -/
noncomputable def decisionAdvantage {n ℓ : ℕ} (C : OracleCircuit n ℓ)
    (Pdec : Matrix (Idx n ℓ) (Idx n ℓ) ℂ) (γ : Matrix (Qubits ℓ) (Qubits ℓ) ℂ) : ℝ :=
  |expectFGX n (fun f g x =>
      (Matrix.trace (Pdec * C.eval f g *
        Matrix.kronecker (Matrix.single (x, f (g x)) (x, f (g x)) (1 : ℂ)) γ *
        (C.eval f g)ᴴ)).re) -
    expectFGX n (fun f g x => ((2 : ℝ) ^ n)⁻¹ * ∑ r : Qubits n,
      (Matrix.trace (Pdec * C.eval f g *
        Matrix.kronecker (Matrix.single (x, r) (x, r) (1 : ℂ)) γ *
        (C.eval f g)ᴴ)).re)|

end CatalystQLB.Query


