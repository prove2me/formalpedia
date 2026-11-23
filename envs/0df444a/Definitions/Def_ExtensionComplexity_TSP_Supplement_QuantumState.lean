-- Prove2me | Definitions.Def_ExtensionComplexity_TSP_Supplement_QuantumState
-- name    : ExtensionComplexity_TSP_Supplement_QuantumState
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:32:21.570146+00:00
-- url     : https://prove2.me/theorems/9f5cf6b8-0a1c-427c-b070-9aacb92859a2
-- title:
--   Real quantum states and pure states (§4)
-- statement:
--   An $r$-dimensional quantum state is a real symmetric positive semidefinite matrix $\rho$ with trace one. A state is pure when it is the outer product of a Euclidean unit vector with itself:
--
--   $$
--   \rho\succeq0,\qquad\operatorname{Tr}(\rho)=1,\qquad
--   \operatorname{Pure}(\rho)\iff\exists\varphi\in\mathbb R^r,\ \sum_k\varphi_k^2=1\ \text{and}\ \rho_{kl}=\varphi_k\varphi_l.
--   $$
--
--   These states are the messages sent by Alice in the one-way protocol model. The field is real as required by footnote 7; purity uses the Euclidean sum of squares, not the sup norm on a function space. Dimension zero has no trace-one state.
-- source:
--   Fiorini, Massar, Pokutta, Tiwary, de Wolf, Exponential lower bounds for polytopes in combinatorial optimization, J. ACM 62(2) (2015), Art. 17, DOI 10.1145/2716307, pp. 17:16–17:17, §4 and footnote 7

import Mathlib

namespace ExtensionComplexity.TSP.Supplement

/-- Section 4, pp. 17:16–17:17, including the real-entries convention of footnote 7. -/
structure QuantumState (r : ℕ) where
  density : Matrix (Fin r) (Fin r) ℝ
  positive : density.PosSemidef
  trace_one : density.trace = 1

/-- A pure state is the outer product of a real Euclidean unit vector with itself.
The sum of squares specifies the Euclidean norm, rather than the sup norm on functions. -/
def QuantumState.IsPure {r : ℕ} (ρ : QuantumState r) : Prop :=
  ∃ φ : Fin r → ℝ, (∑ k, φ k ^ 2) = 1 ∧
    ρ.density = fun k l => φ k * φ l

end ExtensionComplexity.TSP.Supplement


