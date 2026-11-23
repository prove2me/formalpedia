-- Prove2me | Definitions.Def_LindbladTolerant_Testing_lower_bound_model
-- name    : LindbladTolerant_Testing_lower_bound_model
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T02:38:45.162852+00:00
-- url     : https://prove2.me/theorems/cace5721-9ebe-42b0-b32d-21140ab78ea2
-- title:
--   The dephasing hard family and Poisson count distance for Theorem 5.2
-- statement:
--   This module fixes the two mathematical objects used in the converse proof of Theorem 5.2.
--
--   For an $n$-qubit system and $\Gamma\ge0$, the dephasing generator is
--   $$
--   \mathcal L_\Gamma(X)=\Gamma(Z_1XZ_1-X),
--   $$
--   where $Z_1$ is Pauli $Z$ on the first qubit and the identity elsewhere. Its matrix entry convention is the computational-basis convention of the mission. The zero-qubit value is arbitrary and plays no role in the theorem, which assumes $n\ge1$.
--
--   For $\mu\ge0$, the module also defines the Poisson mass function
--   $$
--   p_\mu(r)=e^{-\mu}\frac{\mu^r}{r!},\qquad r\in\mathbb N,
--   $$
--   and the total variation distance
--   $$
--   d_{\mathrm{TV}}(p_a,p_b)=\frac12\sum_{r=0}^{\infty}|p_a(r)-p_b(r)|.
--   $$
--   Lean's convention $0^0=1$ gives $p_0(0)=1$, so the zero-rate empty record is included without a special case.
--
--   **Formalization Note** The Poisson record itself need not be added to the protocol model: the simulation lemma states precisely the resulting data-processing comparison between the protocol output and these two count laws.
-- source:
--   Jinge Bao, Yiyi Cai, Zhong-Xia Shang, Optimal Tolerant Testing of Lindbladian Dissipation, STOC 2027 submission #238, Theorem 5.2 proof, pp.28–30, especially Eq.(111) p.28 and the Poisson-record reduction and Eqs.(116)–(117) p.29. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/238.pdf

import Definitions.Def_LindbladTolerant_Testing_algorithm

set_option autoImplicit false
open scoped ComplexOrder
noncomputable section
open scoped BigOperators Matrix ENNReal

namespace LindbladTolerant.Testing

/-- The Pauli-Z operator on the first qubit, extended by the identity.
The total value at n=0 is immaterial to the n≥1 lower-bound theorem. -/
def dephasingPauli (n : ℕ) : Op (Qubits n) := fun x y =>
  if x = y then
    if hn : 0 < n then (if x ⟨0, hn⟩ then -1 else 1) else 1
  else 0

/-- Eq.(111), p.28: L_Γ(X)=Γ(Z₁XZ₁-X). -/
def dephasing (n : ℕ) (gamma : ℝ) : Super (Qubits n) (Qubits n) :=
  (gamma : ℂ) • (conjugation (dephasingPauli n) - 1)

/-- Probability mass of Pois(μ). Lean's 0^0=1 gives the correct empty record at μ=0. -/
def poissonMass (mu : ℝ) (r : ℕ) : ℝ :=
  Real.exp (-mu) * mu ^ r / (r.factorial : ℝ)

/-- Total variation distance between Poisson count laws, as half the ℓ¹ distance. -/
def poissonTV (a b : ℝ) : ℝ :=
  (∑' r : ℕ, |poissonMass a r - poissonMass b r|) / 2

end LindbladTolerant.Testing


