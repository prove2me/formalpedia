-- Prove2me | Definitions.Def_TeschlQM_Weyl_IsSingularWeylSequence
-- name    : TeschlQM_Weyl_IsSingularWeylSequence
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T22:52:24.655859+00:00
-- url     : https://prove2.me/theorems/11362127-52e5-41e2-a482-8a7e0196b125
-- title:
--   Singular Weyl sequence (Lemma 6.17)
-- statement:
--   Let $A$ be a linear operator in a complex Hilbert space $\mathfrak H$ and $z \in \mathbb C$. A sequence $\psi_n \in \mathfrak D(A)$ is a **singular Weyl sequence** for $A$ at $z$ if $\|\psi_n\| = 1$ for all $n$, $\psi_n$ converges weakly to $0$, and
--   $$\|(A - z)\psi_n\| \to 0 .$$
--   Weak convergence to zero means $\langle \varphi, \psi_n\rangle \to 0$ for every $\varphi \in \mathfrak H$.
--
--   Singular Weyl sequences are the approximate eigenvectors that characterize the essential spectrum (Weyl criterion).
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 145, Lemma 6.17

import Mathlib

namespace TeschlQM.Weyl

open Filter Topology
open scoped InnerProductSpace

/-- Teschl, Lemma 6.17, p. 145: `ψ : ℕ → 𝔇(A)` is a **singular Weyl sequence** for `A` at the point
`z`: `‖ψₙ‖ = 1`, `ψₙ` converges weakly to `0` (`⟨φ, ψₙ⟩ → 0` for every `φ ∈ ℌ`), and
`‖(A - z)ψₙ‖ → 0`. -/
def IsSingularWeylSequence {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (z : ℂ) (ψ : ℕ → A.domain) : Prop :=
  (∀ n, ‖(ψ n : H)‖ = 1) ∧
    (∀ φ : H, Tendsto (fun n => ⟪φ, (ψ n : H)⟫_ℂ) atTop (𝓝 0)) ∧
    Tendsto (fun n => ‖A (ψ n) - z • (ψ n : H)‖) atTop (𝓝 0)

end TeschlQM.Weyl


