-- Prove2me | Definitions.Def_WinterExtrinsic_holevoInfo
-- name    : WinterExtrinsic_holevoInfo
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:19:23.820982+00:00
-- url     : https://prove2.me/theorems/8fc4e210-316b-4e37-953f-2862c53385d8
-- title:
--   Holevo quantity $I(\lambda;\hat\rho)$ of the canonical ensemble
-- statement:
--   Let $\rho$ be a state on $\mathbb C^d$ and $a$ an $m$-outcome POVM, with canonical ensemble $\{\hat\rho_j, \lambda_j\}$. The **Holevo quantity** of this ensemble is
--
--   $$I(\lambda; \hat\rho) = H(\rho) - \sum_{j=1}^m \lambda_j H(\hat\rho_j),$$
--
--   where $H(\sigma) = -\mathrm{Tr}\, \sigma \log_2 \sigma$ is the von Neumann entropy in bits. It is the difference between the entropy of the average state and the conditional entropy $H(\hat\rho \mid \lambda) = \sum_j \lambda_j H(\hat\rho_j)$ (the "entropy defect" or quantum mutual information between the letter $j$ and the state $\hat\rho_j$).
--
--   In Winter's decomposition theorem, $I(\lambda;\hat\rho)$ is the rate of intrinsic data: the number of outcomes each component POVM needs, per copy, on the exponential scale.
--
--   **Formalization Note** Entropies use base-2 logarithms with $0 \log 0 = 0$ (`QAlgorithms.vnEntropy`). A term with $\lambda_j = 0$ vanishes.
-- source:
--   Winter, "Extrinsic" and "intrinsic" data in quantum measurements, arXiv:quant-ph/0109050v3, §II, p.3 ("I(λ; ˆρ) = H(ρ) − Σj λjH(ˆρj)") and p.4 (H(ρ) = −Tr ρ log ρ); logs to base 2, p.2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_WinterExtrinsic_canonState

namespace WinterExtrinsic

open QAlgorithms

/-- The Holevo quantity of the canonical ensemble,
`I(λ; ρ̂) = H(ρ) − Σ_j λ_j H(ρ̂_j)`, in bits.

Winter, *"Extrinsic" and "intrinsic" data in quantum measurements*, arXiv:quant-ph/0109050v3,
§II, p.3 ("The characteristic constant in the exponent is I(λ; ρ̂) = H(ρ) − Σ_j λ_j H(ρ̂_j)"),
with the von Neumann entropy `H(ρ) = −Tr ρ log ρ` (p.4) and logs to base 2 (p.2).

**Formalization Note.** `vnEntropy` is `QAlgorithms.vnEntropy`, `−Tr(ρ log₂ ρ)` with
`0 log 0 = 0` (bits, as the paper's convention on p.2). A term with `λ_j = 0` vanishes, which is
the paper's convention; the junk value `ρ̂_j = 0` there plays no role. -/
noncomputable def holevoInfo {d m : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ)
    (a : Fin m → Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  vnEntropy ρ - ∑ j, canonWeight ρ a j * vnEntropy (canonState ρ a j)

end WinterExtrinsic


