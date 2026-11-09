-- Prove2me | Definitions.Def_QMatVecLB_ConvexOpt_QueryCircuit
-- name    : QMatVecLB_ConvexOpt_QueryCircuit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:59:13.401199+00:00
-- url     : https://prove2.me/theorems/577a7e2f-7b17-4229-84e6-8e975fa19c1c
-- title:
--   Finite quantum query circuits and Born probabilities
-- statement:
--   A finite query circuit consists of arbitrary input-independent complex unitary gates, an actual normalized initial vector and a basis-output map. It can run with any unitary oracle tensored with the workspace identity; the diagonal phase version is used in this paper. The final state and each event probability are computed from the circuit. Tensor products and pure-state trace distance use the complex Euclidean inner product. This is reusable finite-dimensional query-circuit vocabulary, with no success condition supplied as data.
-- source:
--   Andrew M. Childs, Quantum lower bounds for convex optimization and real matrix-vector query problems, STOC 2027 submission #252 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/252.pdf, definitions in Sections 2–3, 5–6; anchor PDF p. 5 (printed p. 4).

import Mathlib

noncomputable section

namespace QMatVecLB.ConvexOpt
open scoped BigOperators

/-- Finite computational-basis Hilbert space. -/
abbrev Ket (Q : Type*) [Fintype Q] := EuclideanSpace ℂ Q

/-- Input-independent gates for exactly t uses of a diagonal oracle. -/
structure QueryCircuit (Q W : Type*) [Fintype Q] [Fintype W] (t : ℕ) where
  gates : Fin (t + 1) → (Ket (Q × W) ≃ₗᵢ[ℂ] Ket (Q × W))

/-- The oracle acts on the query register and leaves the workspace untouched. -/
def applyPhase {Q W : Type*} [Fintype Q] [Fintype W]
    (phase : Q → ℂ) (ψ : Ket (Q × W)) : Ket (Q × W) :=
  WithLp.toLp 2 (fun qw => phase qw.1 * ψ qw)

/-- An arbitrary unitary oracle tensored with the workspace identity. -/
def applyOracle {Q W : Type*} [Fintype Q] [Fintype W]
    (O : Ket Q ≃ₗᵢ[ℂ] Ket Q) (ψ : Ket (Q × W)) : Ket (Q × W) :=
  WithLp.toLp 2 (fun qw => O (WithLp.toLp 2 (fun q => ψ (q, qw.2))) qw.1)

/-- The same circuit can run with any unitary on its query space. -/
def QueryCircuit.evolveOracle {Q W : Type*} [Fintype Q] [Fintype W] {t : ℕ}
    (C : QueryCircuit Q W t) (O : Ket Q ≃ₗᵢ[ℂ] Ket Q)
    (ψ : Ket (Q × W)) : Ket (Q × W) :=
  (List.finRange t).foldl (fun v j => C.gates ⟨j.val + 1, by omega⟩ (applyOracle O v))
    (C.gates ⟨0, by omega⟩ ψ)

/-- V_t O ... V_1 O V_0, with a supplied initial vector. -/
def QueryCircuit.evolve {Q W : Type*} [Fintype Q] [Fintype W] {t : ℕ}
    (C : QueryCircuit Q W t) (phase : Q → ℂ) (ψ : Ket (Q × W)) : Ket (Q × W) :=
  (List.finRange t).foldl (fun v j => C.gates ⟨j.val + 1, by omega⟩ (applyPhase phase v))
    (C.gates ⟨0, by omega⟩ ψ)

/-- A finite-workspace query algorithm, including its actual basis-output map. -/
structure QueryAlg (Q W Y : Type*) [Fintype Q] [Fintype W] (t : ℕ) where
  circuit : QueryCircuit Q W t
  initial : Ket (Q × W)
  normalized : ‖initial‖ = 1
  output : Q × W → Y

/-- Born-rule probability computed from the final state, rather than supplied data. -/
def QueryAlg.prob {Q W Y : Type*} [Fintype Q] [Fintype W] {t : ℕ}
    (alg : QueryAlg Q W Y t) (phase : Q → ℂ) (event : Y → Prop) : ℝ := by
  classical
  exact ∑ z, if event (alg.output z) then
    ‖alg.circuit.evolve phase alg.initial z‖ ^ 2 else 0

/-- Tensor product in the computational bases. -/
def tensorKet {Q W : Type*} [Fintype Q] [Fintype W]
    (φ : Ket Q) (ω : Ket W) : Ket (Q × W) :=
  WithLp.toLp 2 (fun qw => φ qw.1 * ω qw.2)

/-- Trace distance between normalized pure states. -/
def pureDistance {Q : Type*} [Fintype Q] (ψ φ : Ket Q) : ℝ :=
  Real.sqrt (1 - ‖inner ℂ ψ φ‖ ^ 2)

end QMatVecLB.ConvexOpt
end


