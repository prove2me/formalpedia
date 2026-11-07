-- Prove2me | Definitions.Def_GeoQAC_var
-- name    : GeoQAC_var
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:28:58.903625+00:00
-- url     : https://prove2.me/theorems/7eae361e-c04d-48f9-868e-df36076a4167
-- title:
--   Variance $\mathrm{Var}_\rho(H)$
-- statement:
--   For a state $\rho$ and a Hermitian observable $H$,
--   $$
--   \mathrm{Var}_\rho(H) = \mathrm{Tr}(\rho H^2) - \big(\mathrm{Tr}(\rho H)\big)^2 .
--   $$
--   A unit vector $|\psi\rangle$ (one with $\sum_x|\psi_x|^2=1$) represents the pure state $\psi=|\psi\rangle\langle\psi|$, and $\mathrm{Var}_\psi$ is the variance in that state.
--
--   **Formalization Note** For a state and a Hermitian observable both traces are real; the definition takes real parts and assumes nothing. The density matrix $|\psi\rangle\langle\psi|$ is the published `ObliviousRSP.pureState` and the unit-vector predicate the published `DHRUniq.IsUnitVec`; every theorem using a pure state assumes a unit vector.
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), §3.2, p.14; §2.2, p.9

import Mathlib

namespace GeoQAC

/-!
# Variance of an observable

Dong, Ou, Yao, arXiv:2604.07178 (version of 2026-11-03), §3.2, p.14: "For a state ρ and a
Hermitian observable H, define Var_ρ(H) = Tr(ρH²) − (Tr(ρH))²." §2.2, p.9: a unit vector `|ψ⟩`
represents the pure state `ψ = |ψ⟩⟨ψ|`.

**Formalization Note.** The traces are real for a state `ρ` and a Hermitian `H`; the definition
takes real parts and assumes nothing. Pure states are the published `ObliviousRSP.pureState ψ`
(`|ψ⟩⟨ψ|` for any vector); every theorem using it assumes `ψ` is a unit vector (the published `DHRUniq.IsUnitVec`).
-/

variable {ι : Type} [Fintype ι]

/-- `Var_ρ(H) = Tr(ρH²) − (Tr(ρH))²` (p.14), with real parts taken. -/
noncomputable def var (ρ H : Matrix ι ι ℂ) : ℝ :=
  (ρ * H * H).trace.re - ((ρ * H).trace.re) ^ 2

end GeoQAC


