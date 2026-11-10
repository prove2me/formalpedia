-- Prove2me | Definitions.Def_KnownFidelity_Rank_rhoMix
-- name    : KnownFidelity_Rank_rhoMix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:48:02.173216+00:00
-- url     : https://prove2.me/theorems/ef962e3d-5ffd-4e31-ad43-f3530de08d2a
-- title:
--   The mixture $\rho_{p,\tau}=(1-p)|f\rangle\langle f|+p\,\Phi(\tau)$, Eq. (19)
-- statement:
--   For $0<p\le 1/2$ and a state $\tau$ on $\mathbb C^j$,
--
--   $$\rho_{p,\tau}=(1-p)\,|f\rangle\langle f|+p\,\Phi(\tau),$$
--
--   a state on $\mathbb C^d$ of rank at most $j+1$. Its fidelity with $\sigma$ is computed in Lemma 4.2.
--
--   **Formalization Note** The range of $p$ is a hypothesis of the statements that use $\rho_{p,\tau}$.
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, §4.1, Eq. (19), p. 8 (PDF p. 10)

import Mathlib
import Definitions.Def_KnownFidelity_Rank_PhiMap

namespace KnownFidelity.Rank

/-- **The mixture `ρ_{p,τ} = (1 − p)|f⟩⟨f| + p Φ(τ)` of §4.1, Eq. (19).**
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, §4.1, Eq. (19), printed p. 8 (PDF p. 10): "For 0 < p ≤ 1/2, define
ρ_{p,τ} = (1 − p)|f⟩⟨f| + pΦ(τ). (19) This state has rank at most j + 1."

**Formalization Note.** `|f⟩ = U e_f` and `Φ = PhiMap U lam J f ℓ`; the range `0 < p ≤ 1/2` is a
hypothesis of the statements that use it. -/
noncomputable def rhoMix {d j : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) (lam : Fin d → ℝ)
    (J : Fin j ↪ Fin d) (f : Fin d) (ℓ p : ℝ) (τ : Matrix (Fin j) (Fin j) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  let fv : Fin d → ℂ := fun a => U a f
  ((1 - p : ℝ) : ℂ) • Matrix.vecMulVec fv (star fv) + ((p : ℝ) : ℂ) • PhiMap U lam J f ℓ τ

end KnownFidelity.Rank


