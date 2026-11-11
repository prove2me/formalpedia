-- Prove2me | Definitions.Def_UnitaryQIPPSPACE_IsCP
-- name    : UnitaryQIPPSPACE_IsCP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:27:22.967743+00:00
-- url     : https://prove2.me/theorems/edc5d23f-b217-4ad3-b8e1-a0eed85b3818
-- title:
--   Completely positive, trace non-increasing and trace-preserving maps
-- statement:
--   A linear map $\Phi:\mathcal L(\mathbb C^\alpha)\to\mathcal L(\mathbb C^\beta)$ is **completely positive** if its Choi matrix $J(\Phi)=\sum_{i,j}|i\rangle\langle j|\otimes\Phi(|i\rangle\langle j|)$ is positive semidefinite; **trace non-increasing** if $\operatorname{tr}\Phi(\rho)\le\operatorname{tr}\rho$ for every positive semidefinite $\rho$; **trace preserving** if $\operatorname{tr}\Phi(X)=\operatorname{tr}X$ for every $X$. A quantum channel is a completely positive trace-preserving linear map.
--
--   **Formalization Note** Complete positivity is through the Choi matrix, equivalent (Choi's theorem) to positivity of $\Phi\otimes\mathrm{id}_k$ for every $k$.
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), §2, Quantum information theory; Lemma 3.2, p.9 (PDF p.11)

import Mathlib

open Matrix
open scoped ComplexOrder

namespace UnitaryQIPPSPACE

/-- **Completely positive linear map** (He, Ou, Zhao, *unitaryQIP = unitaryPSPACE*,
arXiv:2611.02819, held version sha256 9e357a00…, §2, p. 9 (PDF p. 11), following [Wat18]): a
linear map `Φ : L(ℂ^α) → L(ℂ^β)` is completely positive iff its Choi matrix
`J(Φ) = ∑_{i,j} |i⟩⟨j| ⊗ Φ(|i⟩⟨j|)` is positive semidefinite (Choi's theorem).

**Formalization Note** Complete positivity is defined through the Choi matrix, entry
`((i, k), (j, l)) = Φ(|i⟩⟨j|)_{k,l}`; by Choi's theorem this is equivalent to positivity of
`Φ ⊗ id_k` for every `k`. -/
def IsCP {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    (Φ : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ) : Prop :=
  (Matrix.of fun (x x' : α × β) => Φ (Matrix.single x.1 x'.1 1) x.2 x'.2).PosSemidef

/-- **Trace non-increasing**: `tr Φ(ρ) ≤ tr ρ` for every positive semidefinite `ρ`. -/
def IsTNI {α β : Type} [Fintype α] [Fintype β] (Φ : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ) : Prop :=
  ∀ ρ : Matrix α α ℂ, ρ.PosSemidef → (Φ ρ).trace.re ≤ ρ.trace.re

/-- **Trace preserving**: `tr Φ(X) = tr X` for every `X`. A **quantum channel** is "a completely
positive, trace-preserving linear map" (p. 9). -/
def IsTP {α β : Type} [Fintype α] [Fintype β] (Φ : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ) : Prop :=
  ∀ X : Matrix α α ℂ, (Φ X).trace = X.trace

end UnitaryQIPPSPACE


