-- Prove2me | Definitions.Def_GaussTesting_testCoh
-- name    : GaussTesting_testCoh
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:59:14.358207+00:00
-- url     : https://prove2.me/theorems/04d41450-435e-4244-a210-37094e53f213
-- title:
--   The coherent-state test $\Pi_{\mathrm{test},\mathrm{Coh}}=U_{BS}^\dagger(I\otimes|0^n\rangle\langle0^n|)U_{BS}$
-- statement:
--   The coherent-state tester applies the balanced beam splitter $U_{BS}=\exp\big(\frac\pi4\sum_i(a_i^\dagger\otimes a_i-a_i\otimes a_i^\dagger)\big)$ to two copies and accepts iff the second register is in the vacuum; its accepting projector is $\Pi_{\mathrm{test},\mathrm{Coh}}=U_{BS}^\dagger(I\otimes|0^n\rangle\langle0^n|)U_{BS}$. Since $U_{BS}^\dagger(I\otimes a_j)U_{BS}=(I\otimes a_j-a_j\otimes I)/\sqrt2$, its range is
--
--   $$
--   \{f\in\mathcal H^{\otimes2}:\ (a_j\otimes I-I\otimes a_j)f=0\ \text{for } j=1,\dots,n\},
--   $$
--
--   which contains $|\alpha\rangle|\alpha\rangle$ for every coherent state.
--
--   **Formalization Note** The range is used as the definition (with the annihilators applied to coefficient functions). This also avoids the sign difference between (8.1) on p.72 and p.8, which does not affect the test.
-- source:
--   Iyer, O'Gorman, Parekh, Thompson, Zhao, Optimal testing of fermionic and bosonic Gaussian states, arXiv:2609.39113 (sha256 6683e57b…), §8, eq. (8.1), p.72; proof of Proposition 8.2, p.72

import Definitions.Def_GaussTesting_quadrature
import Definitions.Def_GaussTesting_Ell2

namespace GaussTesting

/-- The coherent-state test subspace: the two-copy vectors whose second output port after the 50:50 beam
splitter `U_BS` is in the vacuum, i.e. `range(U_BS†(I ⊗ |0ⁿ⟩⟨0ⁿ|)U_BS) = {f : (aⱼ ⊗ I − I ⊗ aⱼ) f = 0 ∀ j}`;
its projector is `Π_test,Coh`.

Source: Iyer, O'Gorman, Parekh, Thompson, Zhao, *Optimal testing of fermionic and bosonic Gaussian states*, arXiv:2609.39113 (sha256 6683e57b…), §8, eq. (8.1) and p.72 ("Our property testing algorithm thus simply applies
`U_BS` to `|α⟩|α⟩` and checks that the second register is in the vacuum state"), proof of
Proposition 8.2, p.72 (`Π_test,Coh = U_BS†(I ⊗ |0ⁿ⟩⟨0ⁿ|)U_BS`).

**Formalization Note.**
* With `U_BS = exp(π/4 ∑ᵢ (aᵢ† ⊗ aᵢ − aᵢ ⊗ aᵢ†))`, `U_BS† (I ⊗ aⱼ) U_BS = (I ⊗ aⱼ − aⱼ ⊗ I)/√2`, so
  "second register in the vacuum after `U_BS`" is "annihilated by every `aⱼ ⊗ I − I ⊗ aⱼ`". This
  avoids the sign difference between (8.1), p.72 and p.8 (either sign accepts `|α⟩|α⟩`).
* The equations are imposed on coefficient functions (`lower`); the set is a closed subspace and
  span/closure only package it. -/
noncomputable def testCoh (n : ℕ) : ClosedSubmodule ℂ (Ell2 (Fin 2 → Fin n → ℕ)) :=
  (Submodule.span ℂ {f : Ell2 (Fin 2 → Fin n → ℕ) | ∀ (j : Fin n) (x : Fin 2 → Fin n → ℕ),
      onReg 0 (lower j) (fun y => f y) x - onReg 1 (lower j) (fun y => f y) x = 0}).closure

end GaussTesting


