-- Prove2me | Definitions.Def_RennerKoenig_withReg
-- name    : RennerKoenig_withReg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:45:44.806739+00:00
-- url     : https://prove2.me/theorems/cc67d84f-e911-4c27-950d-f1558b0e22ca
-- title:
--   The random state $\{X\}\otimes\rho$
-- statement:
--   For a random variable $X$ with range $\alpha$ and a random state $\rho$ on $H$, the random state $\{X\}\otimes\rho$ on $\ell^2(\alpha,H)$ is
--
--   $$
--   \omega\mapsto|X(\omega)\rangle\langle X(\omega)|\otimes\rho(\omega).
--   $$
--
--   It represents the classical value $X$ held alongside the quantum system.
--
--   **Formalization Note** The same object serves for the paper's $\rho\otimes\{X\}$: the register is always the outer factor.
-- source:
--   Renner–König, Universally Composable Privacy Amplification Against Quantum Adversaries, arXiv:quant-ph/0403133v2, §2.2, pp.3-4

import Mathlib
import Definitions.Def_RennerKoenig_block

namespace RennerKoenig

/-- **`{X} ⊗ ρ`**: the random state `ω ↦ |X(ω)⟩⟨X(ω)| ⊗ ρ(ω)`. Renner–König, *Universally Composable Privacy Amplification Against Quantum Adversaries*,
arXiv:quant-ph/0403133v2, §2.2, pp.3-4.

**Formalization Note** The register is the outer factor also where the page writes `ρ ⊗ {X}`; the
page itself swaps the two (proof of Lemma 4.3, p.8). -/
noncomputable def withReg {Ω α : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (X : Ω → α) (ρ : Ω → H →L[ℂ] H) :
    Ω → Reg α H →L[ℂ] Reg α H :=
  fun ω => block (X ω) (ρ ω)

end RennerKoenig


