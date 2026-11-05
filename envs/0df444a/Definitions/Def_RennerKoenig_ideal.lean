-- Prove2me | Definitions.Def_RennerKoenig_ideal
-- name    : RennerKoenig_ideal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:45:53.381038+00:00
-- url     : https://prove2.me/theorems/ef219c5c-70b8-4ac9-9feb-e81a64ef1522
-- title:
--   The ideal state $[\{U\}]\otimes T$
-- statement:
--   For $U$ uniform on a finite set $\alpha$ and an operator $T$ on $H$,
--
--   $$
--   [\{U\}]\otimes T=\frac1{|\alpha|}\sum_{x\in\alpha}|x\rangle\langle x|\otimes T.
--   $$
--
--   With $T=[\rho]$ this describes a perfect key, uniform and independent of the adversary.
--
--   **Formalization Note** $U$ enters only through $[\{U\}]$, so no random variable is introduced.
-- source:
--   Renner–König, Universally Composable Privacy Amplification Against Quantum Adversaries, arXiv:quant-ph/0403133v2, Definition 2.3, p.6

import Mathlib
import Definitions.Def_RennerKoenig_block

namespace RennerKoenig

/-- **`[{U}] ⊗ T`** for `U` uniform on `α`: `|α|⁻¹ ∑ₓ |x⟩⟨x| ⊗ T`. Renner–König, *Universally Composable Privacy Amplification Against Quantum Adversaries*,
arXiv:quant-ph/0403133v2, Definition 2.3, p.6.

**Formalization Note** `U` enters only through `[{U}] = |α|⁻¹ ∑ₓ |x⟩⟨x|`, so no random variable
`U` is introduced. -/
noncomputable def ideal (α : Type*) [Fintype α] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H) :
    Reg α H →L[ℂ] Reg α H :=
  ((Fintype.card α : ℂ)⁻¹) • ∑ x : α, block x T

end RennerKoenig


