-- Prove2me | Definitions.Def_ScutaruFid_fidelity
-- name    : ScutaruFid_fidelity
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:57:14.477631+00:00
-- url     : https://prove2.me/theorems/d5ec5329-ff37-47d4-8808-c2477649dfcc
-- title:
--   Uhlmann fidelity $F(\rho_1,\rho_2)=[\operatorname{trace}(\sqrt{\rho_1}\rho_2\sqrt{\rho_1})^{1/2}]^2$
-- statement:
--   For bounded operators $\rho_1,\rho_2$ on a complex Hilbert space $H$, **Uhlmann's transition probability** (fidelity) is
--
--   $$
--   F(\rho_1,\rho_2)=\Big[\operatorname{trace}\big(\sqrt{\rho_1}\,\rho_2\,\sqrt{\rho_1}\big)^{1/2}\Big]^2 ,
--   $$
--
--   where $\sqrt{\cdot}$ is the positive square root and the trace is $\sum_i\langle b_i,\cdot\,b_i\rangle$ in a Hilbert basis $(b_i)$. For density operators it satisfies the axioms F1–F4 of the paper; it is the quantity the paper computes in closed form for Gaussian states.
--
--   **Formalization Note** `fidelity b ρ₁ ρ₂` is $(\operatorname{Re}\operatorname{trace}\sqrt{\sqrt{\rho_1}\rho_2\sqrt{\rho_1}})^2$ with the published basis trace `operatorTrace b` (a series; its junk value is $0$ when it does not converge). The trace of the positive operator $\sqrt{\sqrt{\rho_1}\rho_2\sqrt{\rho_1}}$ is real, so the real part loses nothing. It is defined on any complex Hilbert space; the mission's states live on $L^2(\mathbb R)$.
-- source:
--   Scutaru, Fidelity for displaced squeezed thermal states and the oscillator semigroup, arXiv:quant-ph/9708013v1, eq. (1), p.1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13
import Definitions.Def_ScutaruFid_opSqrt

open QAlgorithms.Papers.Independent.Dependency50.P13

namespace ScutaruFid

/-- **Uhlmann's transition probability (fidelity)**, eq. (1). Scutaru, arXiv:quant-ph/9708013v1,
eq. (1), p.1: "Uhlmann's transition probability for mixed states [4]
F(ρ1, ρ2) = [trace(√ρ1 ρ2 √ρ1)^{1/2}]²".

`fidelity b ρ σ = (Re trace √(√ρ σ √ρ))²`, where `√·` is the positive square root of a positive
operator and the trace is `∑ᵢ ⟨bᵢ, T bᵢ⟩` in the Hilbert basis `b`.

**Formalization Note** `√·` is `opSqrt`, Mathlib's `CFC.sqrt` (continuous functional calculus)
on the C*-algebra `H →L[ℂ] H`; on a positive operator it is the unique positive square root. The trace
is the published `Dependency50.P13.operatorTrace`, a `tsum` (junk value `0` when the series does
not converge). The trace of the positive operator `√(√ρ σ √ρ)` is real, so taking the real part
loses nothing. Defined on an arbitrary complex Hilbert space `H` (unitary invariance, F4, is
stated there); the mission's states live on `H = L²(ℝ)`. -/
noncomputable def fidelity {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {ι : Type*} (b : HilbertBasis ι ℂ H) (ρ σ : H →L[ℂ] H) : ℝ :=
  ((operatorTrace b (opSqrt (opSqrt ρ * σ * opSqrt ρ))).re) ^ 2

end ScutaruFid


