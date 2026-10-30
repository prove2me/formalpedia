-- Prove2me | Definitions.Def_WinterExtrinsic_povmPow
-- name    : WinterExtrinsic_povmPow
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:18:05.889199+00:00
-- url     : https://prove2.me/theorems/b4b7856f-46e0-458e-900a-efa2a99757a6
-- title:
--   Tensor power $a^{\otimes l}$ of a POVM
-- statement:
--   Let $a = (a_1, \dots, a_m)$ be a POVM on $\mathbb C^d$ and $l \in \mathbb N$. Its **$l$-fold tensor power** is the measurement on $(\mathbb C^d)^{\otimes l}$ with outcome set $[m]^l$ given by
--
--   $$a^{\otimes l} = \big(a_{j_1} \otimes \cdots \otimes a_{j_l}\big)_{j^l \in [m]^l}, \qquad a_{j^l} := a_{j_1} \otimes \cdots \otimes a_{j_l}.$$
--
--   It describes the measurement $a$ applied independently to each of $l$ systems. Winter's theorem decomposes $a^{\otimes l}$, approximately, into a mixture of measurements with far fewer outcomes.
--
--   **Formalization Note** Words $j^l$ are functions `Fin l → Fin m`; operators on $(\mathbb C^d)^{\otimes l}$ are matrices indexed by `Fin l → Fin d`, and the Kronecker product of the factors is `wordTensor` (entry $(x,y)$ is $\prod_k (a_{j_k})_{x_k y_k}$). At $l = 0$ the space is $\mathbb C$ and the single outcome is $1$.
-- source:
--   Winter, "Extrinsic" and "intrinsic" data in quantum measurements, arXiv:quant-ph/0109050v3, §I, p.2 ("a⊗l = (aj1 ⊗ · · · ⊗ ajl) jl∈{1,...,m}l")

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43

namespace WinterExtrinsic

open QAlgorithms.Papers.Independent.Renew46.P43 (wordTensor)

/-- The `l`-fold tensor power `a^{⊗l} = (a_{j_1} ⊗ ⋯ ⊗ a_{j_l})_{j^l ∈ [m]^l}` of a POVM
`a = (a_1, …, a_m)` on `ℂ^d`: a POVM on `(ℂ^d)^{⊗l}` with outcome set `[m]^l`.

Winter, *"Extrinsic" and "intrinsic" data in quantum measurements*, arXiv:quant-ph/0109050v3,
§I, p.2 ("a^{⊗l} = (a_{j_1} ⊗ ⋯ ⊗ a_{j_l})_{j^l ∈ {1,…,m}^l}").

**Formalization Note.** Words `j^l` are functions `Fin l → Fin m`; `(ℂ^d)^{⊗l}` has basis
`Fin l → Fin d`, and the Kronecker product of the `l` factors is `wordTensor` (entry `(x, y)` is
`∏_k (a_{j_k})_{x_k y_k}`). At `l = 0` the space is `ℂ` and the single outcome is `1`. -/
noncomputable def povmPow {d m : ℕ} (a : Fin m → Matrix (Fin d) (Fin d) ℂ) (l : ℕ)
    (w : Fin l → Fin m) : Matrix (Fin l → Fin d) (Fin l → Fin d) ℂ :=
  wordTensor (fun k => a (w k))

end WinterExtrinsic


