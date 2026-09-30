-- Prove2me | Definitions.Def_RamadgeWonham_Quotient_Recognizer
-- name    : RamadgeWonham_Quotient_Recognizer
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:40:25.227884+00:00
-- url     : https://prove2.me/theorems/8899872f-e297-4894-b74b-f216b0493c63
-- title:
--   Recognizer for a language; the supervisor 𝒮⁰ built on a recognizer (§4, §10)
-- statement:
--   A **recognizer** for a language $L \subseteq \Sigma^*$ is an accessible generator $\mathcal M$ with $L_m(\mathcal M) = L$.
--
--   Given a generator $\hat S^0 = (X^0, \Sigma, \xi^0, x^0_0, \cdot)$, a subset $X^0_m \subseteq X^0$ and a map $\phi^0 : X^0 \to \{0,1\}^{\Sigma_c}$, the **supervisor built on $\hat S^0$** is
--   $$\mathcal S^0 = (S^0, \phi^0), \qquad S^0 = (X^0, \Sigma, \xi^0, x^0_0, X^0_m):$$
--   it keeps the states, transitions and initial state of $\hat S^0$ and replaces its marker set by $X^0_m$.
--
--   This is the construction in the quotient structure theorem, where $\hat S^0$ is a trim recognizer for the closed-loop language of a given supervisor.
-- source:
--   Ramadge and Wonham, Supervisory Control of a Class of Discrete Event Processes, SIAM J. Control Optim. 25(1), 1987, p. 212, §4 (recognizer); pp. 222-223, §10 (Ŝ⁰ and S⁰ in Theorem 10.1)

import Mathlib
import Definitions.Def_RamadgeWonham_Shared_Supervisor

namespace RamadgeWonham.Quotient

variable {α : Type} {Ec : Set α}

/-- A recognizer for a language `L ⊆ Σ*` (§4, p. 212): an accessible generator `ℳ` with
`L_m(ℳ) = L`. -/
def IsRecognizer (M : Shared.Generator α) (L : Set (List α)) : Prop :=
  M.Accessible ∧ M.Lm = L

/-- The supervisor `𝒮⁰ = (S⁰, φ⁰)` built on a recognizer `Ŝ⁰ = (X⁰, Σ, ξ⁰, x⁰₀, ·)` (§10,
pp. 222–223): `S⁰ = (X⁰, Σ, ξ⁰, x⁰₀, X⁰_m)` has the states, transitions and initial state of `Ŝ⁰`
and the marker set `X⁰_m`, and `φ⁰ : X⁰ → {0,1}^{Σ_c}` is its state feedback map. -/
def ofRecognizer (R : Shared.Generator α) (Xm0 : Set R.Q) (φ0 : R.Q → Ec → Bool) : Shared.Supervisor α Ec :=
  ⟨{ Q := R.Q, δ := R.δ, q0 := R.q0, Qm := Xm0 }, φ0⟩

end RamadgeWonham.Quotient


