-- Prove2me | Definitions.Def_HighDimProb_Isoperimetry_UniformProjection
-- name    : HighDimProb_Isoperimetry_UniformProjection
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-18T05:39:16.099921+00:00
-- url     : https://prove2.me/theorems/6d7c055d-cf20-41f5-b2d2-6f796e3d2e89
-- title:
--   Random orthogonal projection uniformly distributed in the Grassmannian
-- statement:
--   This definition operationally characterizes a **random orthogonal projection onto an
--   $m$-dimensional subspace uniformly distributed in the Grassmannian** $G_{n,m}$ (the space
--   of all $m$-dimensional subspaces of $\mathbb R^n$), written $E \sim \mathrm{Unif}(G_{n,m})$
--   in Vershynin's text. It is the shared hypothesis of Lemma 5.3.2 and the mission's goal,
--   Theorem 5.3.1 (the Johnson-Lindenstrauss Lemma).
--
--   Let $(\Omega, \mathcal F, \mathrm{Prob})$ be a probability space, $n, m \in \mathbb N$, and
--   $P : \Omega \to (\mathbb R^n \to \mathbb R^n)$ a random continuous linear map. $P$ is a
--   **uniformly-distributed random orthogonal projection of rank $m$** when, almost surely:
--
--   1. $P_\omega$ is idempotent ($P_\omega \circ P_\omega = P_\omega$) — a projection;
--   2. $P_\omega$ is self-adjoint — the projection is orthogonal, not merely along some
--      complementary subspace;
--   3. the range of $P_\omega$ has dimension $m$;
--
--   and, for every orthogonal transformation $U$ of $\mathbb R^n$, the conjugated map
--   $\omega \mapsto U \circ P_\omega \circ U^{-1}$ has the same law as $P$.
--
--   Conjugating an orthogonal projection by $U$ is exactly the orthogonal projection onto the
--   image of its range under $U$; so property 4 says the law of the random subspace
--   $\mathrm{range}(P)$ is rotation invariant, which is precisely how Vershynin defines a
--   uniformly-distributed random element of $G_{n,m}$.
--
--   **Formalization Note** Mathlib has no measure-theoretic construction of the Grassmannian or
--   of Haar measure on the orthogonal group to build a canonical uniform subspace/projection
--   from; `Mathlib.RingTheory.Grassmannian` is the scheme-theoretic (algebraic-geometry)
--   Grassmannian and is a different object entirely. Following the book's own operational
--   definition (rotation invariance, quoted above), this definition states rotation invariance
--   of the *projection's* law directly, working with the projection $P : \mathbb R^n \to
--   \mathbb R^n$ (a `ContinuousLinearMap`, for which Mathlib readily supplies idempotence,
--   self-adjointness, and rank) rather than constructing a type of random `m`-dimensional
--   subspaces. `≃ₗᵢ[ℝ]` is the type of real linear isometric equivalences of $\mathbb R^n$ with
--   itself, i.e. the orthogonal group $O(n)$.
--
--   **Moderator's note.** `P` is required to be a measurable map into the operator space, so that its law is a genuine probability measure and the rotation-invariance clause is not vacuous (Mathlib's pushforward of a non-measurable map is the zero measure).
-- source:
--   Vershynin, High-Dimensional Probability (2018), §5.2.6, p. 116 (PDF p. 124), and §5.3, p. 118 (PDF p. 126)

import Mathlib

open MeasureTheory

namespace HighDimProb.Isoperimetry

/-- `P` is a random orthogonal projection in `ℝⁿ` onto an `m`-dimensional subspace uniformly
distributed in the Grassmannian `G_{n,m}`. Vershynin, *High-Dimensional Probability* (2018),
§5.2.6/§5.3, defines a random `m`-dimensional subspace `E ∼ Unif(G_{n,m})` operationally by
rotation invariance of its distribution (`P` is a measurable random operator, so its law is
a genuine probability measure on the operator space): `P {E ∈ 𝓔} = P {U(E) ∈ 𝓔}` for every orthogonal
matrix `U` and every fixed set `𝓔 ⊂ G_{n,m}`. This definition states the same property for the
orthogonal projection `P` onto `E` directly (as the book's own statements, e.g. Theorem 5.3.1
and Lemma 5.3.2, are phrased in terms of `P` rather than `E` itself): `P ω` is, for almost
every `ω`, an orthogonal projection (idempotent and self-adjoint) of rank `m`, and the law of
`P` is invariant under conjugation `p ↦ U ∘ p ∘ U⁻¹` by every orthogonal transformation `U` —
exactly the transformation a projection onto `E` undergoes when `E` is replaced by `U(E)`. -/
def IsUniformProjection {Ω : Type} [MeasurableSpace Ω] (Prob : Measure Ω) {n : ℕ} (m : ℕ)
    (P : Ω → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) : Prop :=
  Measurable P ∧
  (∀ᵐ ω ∂Prob, IsIdempotentElem (P ω)) ∧
  (∀ᵐ ω ∂Prob, IsSelfAdjoint (P ω)) ∧
  (∀ᵐ ω ∂Prob,
    Module.finrank ℝ (LinearMap.range (P ω : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))) = m) ∧
  (∀ U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
    Measure.map
      (fun ω => (U.toContinuousLinearEquiv : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).comp
        ((P ω).comp (U.symm.toContinuousLinearEquiv : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))))
      Prob
    = Measure.map P Prob)

end HighDimProb.Isoperimetry


