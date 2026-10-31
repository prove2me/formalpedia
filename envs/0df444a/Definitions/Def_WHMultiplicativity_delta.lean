-- Prove2me | Definitions.Def_WHMultiplicativity_delta
-- name    : WHMultiplicativity_delta
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:25:31.336972+00:00
-- url     : https://prove2.me/theorems/2be232f6-2e73-4801-b097-3ead7d01dbfc
-- title:
--   $\Delta(p,\Phi) = \log\|S\otimes S(|\Phi\rangle\langle\Phi|)\|_p - 2\log\nu_p(S)$ (eq. 12)
-- statement:
--   Let $S$ be the Werner–Holevo channel on the $d\times d$ matrices, $S(\rho) = \frac{1}{d-1}\big(\operatorname{tr}(\rho)\mathbb 1 - \rho^T\big)$, and $S\otimes S$ its tensor square on $\mathbb C^d\otimes\mathbb C^d$. For a vector $\Phi \in \mathbb C^d\otimes\mathbb C^d$ and $p\in[1,\infty]$, define
--
--   $$
--   \Delta(p,\Phi) = \log \big\|S\otimes S(|\Phi\rangle\langle\Phi|)\big\|_p - 2\log \nu_p(S).
--   $$
--
--   If the multiplicativity conjecture $\nu_p(S\otimes S) = \nu_p(S)^2$ were true, $\Delta(p,\Phi) \le 0$ would hold for every unit vector $\Phi$; a single $\Phi$ with $\Delta(p,\Phi) > 0$ disproves it at that $p$.
--
--   **Formalization Note** $S\otimes S$ is `QAlgorithms.piSuperop (fun _ : Fin 2 => wernerHolevo d)`, the tensor product of superoperators through matrix units; $|\Phi\rangle\langle\Phi|$ is `pureState Φ`. The paper leaves the base of $\log$ open; the natural logarithm is used, which changes no sign or zero of $\Delta$.
-- source:
--   Werner and Holevo, Counterexample to an additivity conjecture for output purity of quantum channels, arXiv:quant-ph/0203003v1, eq. (12), p.2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_WHAdditivity_Renyi_Model
import Definitions.Def_WHMultiplicativity_schattenNorm
import Definitions.Def_WHMultiplicativity_maxOutputNorm

open scoped ENNReal

namespace WHMultiplicativity

/-- Werner and Holevo, arXiv:quant-ph/0203003v1, eq. (12), p.2: for a vector `Φ ∈ ℂ^d ⊗ ℂ^d`,
`Δ(p, Φ) = log ‖S ⊗ S(|Φ⟩⟨Φ|)‖_p − 2 log ν_p(S)`, where `S = wernerHolevo d` is the channel (6)
and `S ⊗ S` is its tensor square.

**Formalization Note.** `S ⊗ S` is `QAlgorithms.piSuperop (fun _ : Fin 2 => S)`, the tensor
product of superoperators on `ℂ^d ⊗ ℂ^d` (index `Fin 2 → Fin d`), defined on every matrix through
matrix units; `|Φ⟩⟨Φ|` is `WHAdditivity.Renyi.pureState Φ`. The base of `log` is not fixed by the
paper; the natural logarithm `Real.log` is used (the sign of `Δ` does not depend on the base).
`Real.log` is `0` at `0`, so `Δ` is the paper's quantity whenever both norms are positive, which
holds for every unit vector `Φ` and `p ≥ 1`. The paper uses `d = 3`. -/
noncomputable def delta (d : ℕ) (p : ℝ≥0∞) (Φ : (Fin 2 → Fin d) → ℂ) : ℝ :=
  Real.log (schattenNorm p
      (QAlgorithms.piSuperop (fun _ : Fin 2 => WHAdditivity.Renyi.wernerHolevo d)
        (WHAdditivity.Renyi.pureState Φ)))
    - 2 * Real.log (maxOutputNorm p (WHAdditivity.Renyi.wernerHolevo d))

end WHMultiplicativity


