-- Prove2me | Definitions.Def_QPSpinProfile_prodStatesOn
-- name    : QPSpinProfile_prodStatesOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T03:26:09.070661+00:00
-- url     : https://prove2.me/theorems/5f9a2f6b-b1f6-4a8a-a834-8cd12bdd206b
-- title:
--   Pure product states $\mathrm{prod}_n$ and fully separable states
-- statement:
--   On a finite set $S$ of qubits, a **pure product state** is
--   $$
--   \bigotimes_{s\in S}|\psi_s\rangle\langle\psi_s|,\qquad |\psi_s\rangle\in\mathbb C^2,\ \|\psi_s\|_2=1 ,
--   $$
--   the projector onto the product vector with coordinates $\Psi(x)=\prod_s\psi_s(x_s)$. For $S=[n]$ this is the class $\mathrm{prod}_n$ of the paper. A **fully separable** state on $S$ is a convex mixture of pure product states on $S$, i.e. an element of their convex hull.
--
--   Product states are the universal benchmark class of the mission: Corollary 2.4 shows they approximate the local profile of every state after conditioning.
--
--   **Formalization Note** In finite dimension, mixtures of products of mixed one-qubit states are exactly the convex hull of pure product states, so "fully separable" is encoded as membership in `convexHull ℝ (prodStatesOn S)`.
-- source:
--   Al-Ghattas, Gamarnik, Kiani, Beyond light cones: State preparation complexity in quantum spin glasses, arXiv:2610.02166 (held version, sha256 a0a1ec89…), §1.2, p.4 (PDF p.7); fully separable: §2.1.3, p.17 (PDF p.20)

import Mathlib
import Definitions.Def_QPSpinProfile_PauliString

namespace QPSpinProfile

open Matrix

/-- The pure product states on a finite set `S` of qubits (arXiv:2610.02166, held version sha256
a0a1ec89…, §1.2, p.4, PDF p.7): `⊗_{s ∈ S} |ψ_s⟩⟨ψ_s|` with unit vectors `ψ_s ∈ ℂ²`. The
product vector has coordinates `Ψ(x) = ∏_s ψ_s(x_s)` and the state is `|Ψ⟩⟨Ψ|`.
A *fully separable* state on `S` is an element of `convexHull ℝ (prodStatesOn S)`. -/
def prodStatesOn (S : Type) [Fintype S] : Set (Matrix (S → Fin 2) (S → Fin 2) ℂ) :=
  {ρ | ∃ ψ : S → Fin 2 → ℂ, (∀ s, ∑ a, ‖ψ s a‖ ^ 2 = 1) ∧
    ρ = Matrix.vecMulVec (fun x => ∏ s, ψ s (x s)) (star fun x => ∏ s, ψ s (x s))}

/-- `prod_n`, the class of pure product states on `n` qubits (arXiv:2610.02166, §1.2, p.4,
PDF p.7). -/
def prodStates (n : ℕ) : Set (Matrix (Qubits n) (Qubits n) ℂ) := prodStatesOn (Fin n)

end QPSpinProfile


