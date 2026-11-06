-- Prove2me | Definitions.Def_TIESharp_IsMachineEquivariant
-- name    : TIESharp_IsMachineEquivariant
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:36:43.850541+00:00
-- url     : https://prove2.me/theorems/0568050d-c2ec-405b-bd71-62292de7afe7
-- title:
--   Invariance of a family under machine relabeling
-- statement:
--   A family is **invariant under machine relabeling** if for every machine permutation $\sigma$, relabeling the rows of the bids, $(\sigma b)_i=b_{\sigma^{-1}(i)}$, relabels the assignment law and the payments:
--   $$y^m_{\sigma\circ A}(\sigma b)=y^m_A(b),\qquad p^m_{\sigma(i)}(\sigma b)=p^m_i(b),$$
--   at every job count and every nonnegative profile. This is the machine symmetry of the replacement family in Lemma 4.2.
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), Lemma 4.2, p.14; Step 6, p.16

import Mathlib
import Definitions.Def_TIESharp_Nonneg
import Definitions.Def_TIESharp_Family

set_option autoImplicit false

namespace TIESharp

/-- A family is **invariant under machine relabeling** (Li, *Sharp Bounds for
Truthful-in-Expectation Scheduling*, arXiv:2611.05134, Lemma 4.2, p.14, and Step 6, p.16:
"Relabel the input rows, output assignments, and potentials by a machine permutation"). For a
machine permutation `σ`, relabeling the rows of the bid profile, `(σ • b)_{i} = b_{σ⁻¹(i)}`,
relabels the assignment law, `y(σ • b)_{σ ∘ A} = y(b)_A`, and the payments,
`p_{σ(i)}(σ • b) = p_i(b)`.

**Formalization Note.** Imposed at every job count `m` and every nonnegative profile. -/
def IsMachineEquivariant {n : ℕ} (F : Family n) : Prop :=
  ∀ (m : ℕ) (b : Fin n → Fin m → ℝ) (σ : Equiv.Perm (Fin n)), Nonneg b →
    (∀ A : Fin m → Fin n, F.alloc m (fun i => b (σ.symm i)) (σ ∘ A) = F.alloc m b A) ∧
    ∀ i, F.pay m (fun i' => b (σ.symm i')) (σ i) = F.pay m b i

end TIESharp


