-- Prove2me | Definitions.Def_ArbLindbladLearn_twirled
-- name    : ArbLindbladLearn_twirled
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:25:41.498972+00:00
-- url     : https://prove2.me/theorems/2a722c42-6d83-42e7-bdda-5200412ea36b
-- title:
--   Twirled Chebyshev mixture channel $\overline{\mathcal E}$
-- statement:
--   The channel obtained by twirling and mixing the semigroup:
--   $$\overline{\mathcal E}(\rho)=\sum_{j=1}^q\frac{p_j}{4^n}\sum_{c\in\mathbb F_2^{2n}}P_c\,e^{t_j\mathcal L}(P_c\rho P_c)\,P_c ,$$
--   with the support-learning nodes $t_j$ on $[0,1/\Lambda]$ and weights $p_j$. Lemma 3.6 shows it is the Pauli channel with error distribution $\mu$.
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Lemma 3.6, p.22

import Mathlib
import Definitions.Def_ArbLindbladLearn_suppQ
import Definitions.Def_ArbLindbladLearn_gen

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn

open LindbladTolerant.Testing

/-- The twirled Chebyshev mixture channel (Lemma 3.6, Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.22):
`ℰ(ρ) = Σ_{j=1}^q (p_j/4ⁿ) Σ_{w ∈ 𝔽₂²ⁿ} P_w e^{t_jℒ}(P_w ρ P_w) P_w`, with `q`, `p_j` and the
nodes `t_j` on `[0, 1/Λ]` of the support-learning setup (p.21). -/
def twirled {n : ℕ} (c : Coeffs n) (Λ η : ℝ) (ρ : Op (Qubits n)) : Op (Qubits n) :=
  ∑ j ∈ Finset.Icc 1 (suppQ Λ η), ∑ w : Pauli n,
    ((suppP Λ η j / 4 ^ n : ℝ) : ℂ) •
      (pauliMatrix w *
        applySuper (evolution (gen c) (chebNode (suppQ Λ η) (suppT Λ) j))
          (pauliMatrix w * ρ * pauliMatrix w) * pauliMatrix w)

end ArbLindbladLearn


