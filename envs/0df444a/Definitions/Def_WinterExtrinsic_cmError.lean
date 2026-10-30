-- Prove2me | Definitions.Def_WinterExtrinsic_cmError
-- name    : WinterExtrinsic_cmError
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:19:16.881583+00:00
-- url     : https://prove2.me/theorems/ef67e468-ec6f-46f7-97fb-3afb0e3a00ca
-- title:
--   Error of condition (CM)
-- statement:
--   Let $\rho$ be a state on $\mathbb C^d$, $a$ an $m$-outcome POVM, $l \in \mathbb N$, and $A = (A_{j^l})_{j^l \in [m]^l}$ a family of operators on $(\mathbb C^d)^{\otimes l}$. The **(CM) error** of $A$ as an approximation of $a^{\otimes l}$ on the source $\rho^{\otimes l}$ is
--
--   $$\sum_{j^l \in [m]^l} \frac12 \Big\| \sqrt{\rho^{\otimes l}}\,\big(A_{j^l} - a_{j^l}\big)\,\sqrt{\rho^{\otimes l}} \Big\|_1 ,$$
--
--   where $\|\cdot\|_1$ is the trace norm and $\sqrt{\rho^{\otimes l}}$ the positive square root of $\rho^{\otimes l}$. Condition (CM) with parameter $\epsilon$ asks that this quantity be at most $\epsilon$. It implies that, for every source ensemble with average $\rho^{\otimes l}$, the joint distribution of source letter and outcome under $A$ is $\epsilon$-close in total variation to that under $a^{\otimes l}$ (condition (CP)).
--
--   **Formalization Note** $\rho^{\otimes l}$ is `wordTensor (fun _ => ρ)` on the basis `Fin l → Fin d`; its square root is `cfc Real.sqrt`. `QAlgorithms.traceNorm` is the unhalved trace norm $\mathrm{Tr}\sqrt{M^\dagger M}$, so the factor $\tfrac12$ is written explicitly.
-- source:
--   Winter, "Extrinsic" and "intrinsic" data in quantum measurements, arXiv:quant-ph/0109050v3, §I, condition (CM), p.3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_WinterExtrinsic_povmPow

namespace WinterExtrinsic

open QAlgorithms.Papers.Independent.Renew46.P43 (wordTensor)

/-- The left-hand side of condition (CM): for a state `ρ`, a POVM `a` and a measurement
`A = (A_{j^l})_{j^l ∈ [m]^l}` on `(ℂ^d)^{⊗l}`,
`Σ_{j^l} ½ ‖√(ρ^{⊗l}) (A_{j^l} − a_{j^l}) √(ρ^{⊗l})‖₁`.

Winter, *"Extrinsic" and "intrinsic" data in quantum measurements*, arXiv:quant-ph/0109050v3,
§I, p.3, condition (CM): "Σ_{j^l} ½ ‖√ρ^{⊗l} (A_{j^l} − a_{j^l}) √ρ^{⊗l}‖₁ ≤ ε".

**Formalization Note.** `ρ^{⊗l}` is `wordTensor (fun _ => ρ)` on the basis `Fin l → Fin d`, and
its square root is `cfc Real.sqrt`, the positive square root. `QAlgorithms.traceNorm M` is
`Tr √(M†M)`, the unhalved trace norm, so the paper's factor `½` is written explicitly. -/
noncomputable def cmError {d m : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ)
    (a : Fin m → Matrix (Fin d) (Fin d) ℂ) (l : ℕ)
    (A : (Fin l → Fin m) → Matrix (Fin l → Fin d) (Fin l → Fin d) ℂ) : ℝ :=
  ∑ w, (1 / 2 : ℝ) * QAlgorithms.traceNorm
    (cfc Real.sqrt (wordTensor (fun _ : Fin l => ρ)) * (A w - povmPow a l w) *
      cfc Real.sqrt (wordTensor (fun _ : Fin l => ρ)))

end WinterExtrinsic


