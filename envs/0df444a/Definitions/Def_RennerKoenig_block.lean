-- Prove2me | Definitions.Def_RennerKoenig_block
-- name    : RennerKoenig_block
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:44:40.501201+00:00
-- url     : https://prove2.me/theorems/eec936c4-6594-4101-b9a5-80219621bc60
-- title:
--   The operator $|x\rangle\langle x|\otimes T$
-- statement:
--   For $x\in\alpha$ and a bounded operator $T$ on $H$, the operator $|x\rangle\langle x|\otimes T$ on $\ell^2(\alpha,H)$ acts as $T$ on the $x$-th summand and as $0$ on all the others.
--
--   **Formalization Note** It is $J_x T J_x^\dagger$, where $J_x:H\to\ell^2(\alpha,H)$ is the isometric inclusion of the $x$-th summand.
-- source:
--   Renner–König, Universally Composable Privacy Amplification Against Quantum Adversaries, arXiv:quant-ph/0403133v2, §2.2, p.4

import Mathlib
import Definitions.Def_RennerKoenig_Reg

namespace RennerKoenig

open scoped Classical in
/-- **`|x⟩⟨x| ⊗ T`** on `ℓ²(α, H)`: the operator acting as `T` on the `x`-th summand and as `0`
on the others. Renner–König, *Universally Composable Privacy Amplification Against Quantum Adversaries*,
arXiv:quant-ph/0403133v2, §2.2, p.4.

**Formalization Note** `J ∘ T ∘ J†`, with `J` the isometric inclusion of the `x`-th summand. -/
noncomputable def block {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {α : Type*} (x : α) (T : H →L[ℂ] H) : Reg α H →L[ℂ] Reg α H :=
  (lp.singleContinuousLinearMap ℂ (fun _ : α => H) 2 x) ∘L T ∘L
    (ContinuousLinearMap.adjoint (lp.singleContinuousLinearMap ℂ (fun _ : α => H) 2 x))

end RennerKoenig


