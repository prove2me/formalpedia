-- Prove2me | Definitions.Def_QVolKLS_SampleOp
-- name    : QVolKLS_SampleOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:38:33.429039+00:00
-- url     : https://prove2.me/theorems/dcd7fbfb-bcae-4081-beb0-85e5965d86d7
-- title:
--   Sample-controlled gates, selective phases through $|\pi_v\rangle$, controlled qsample reflections
-- statement:
--   Let $\Omega$ be a finite sample space, $A$ an auxiliary space, and $\{\pi_v\}$ a family of laws on $\Omega$. Lemma 3.4 considers circuits made of three kinds of operations on joint vectors $|\Psi\rangle_{SA}$:
--
--   1. **sample-controlled** unitaries $\sum_x|x\rangle\langle x|_S\otimes V_A(x)$;
--   2. **selective phases** $U_\theta=I+(e^{i\theta}-1)\,|\pi_v\rangle\langle\pi_v|_S\otimes\Pi_A$;
--   3. **controlled qsample reflections** $I_S\otimes(I_A-\Pi_A)+R_{\pi_v}\otimes\Pi_A$,
--
--   where $\Pi_A$ is an orthogonal projection on $A$ (the auxiliary control; $\Pi_A=I$ when uncontrolled). A circuit is a finite list of such operations applied in order; its count $q$ is the number of operations of kinds 2 and 3.
--
--   **Formalization Note** `IsOrthProj` (idempotent and self-adjoint), the inductive `SampleOp`, its action `SampleOp.apply`, `runOps`, `countedOps`. The partial inner product is $\langle\pi_v|_S\Psi=\sum_x\sqrt{\pi_v(x)}\,\psi_x$.
-- source:
--   R. Zhang, Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation, arXiv:2610.04987 (preprint, held version, sha256 eee7a45e7117af08035a8d75fd6f145fa82ddade51ad87a6507911b6a0aa4f80), §3.3, Lemma 3.4 and its proof, pp.27–28

import Definitions.Def_QVolKLS_fourthMomentNorm

set_option autoImplicit false

namespace QVolKLS

open scoped ComplexConjugate

/-!
# Sample-controlled gates, selective phases and controlled qsample reflections

R. Zhang, *Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation*,
arXiv:2610.04987 (held version, sha256 eee7a45e…), §3.3, Lemma 3.4, pp.27–28: "Suppose each gate is
sample-controlled or a selective phase through `|π_v⟩_S`, possibly controlled by an auxiliary
projector. The sample register S is not exchanged with another sample register." The proof gives
the three operations: `V = Σ_x |x⟩⟨x|_S ⊗ V_A(x)`, `U_θ = I + (e^{iθ} − 1)|π_v⟩⟨π_v|_S ⊗ Π_A`, and
the controlled reflection `I_S ⊗ (I_A − Π_A) + R_{π_v} ⊗ Π_A`.

**Formalization Note.**
* Joint vectors are `Ω → H` (see `fourthMomentNorm`, `opApply`), `Ω` the finite sample space and `H` any complex inner
  product space (the auxiliary registers). `Π_A` is an orthogonal projection on `H` (idempotent and
  self-adjoint; `Π_A = I` is the uncontrolled case). A sample-controlled unitary is a family of
  unitaries `V_A(x)` of `H` (`H ≃ₗᵢ[ℂ] H`), one per sample label.
* The laws are indexed by `Fin k` (`k = 1` for one law, `k = 2` for a pair). The partial inner
  product is `⟨π_v|_S Ψ = Σ_x √π_v(x) ψ_x`.
* A circuit is a list of operations, applied head first (`runOps`); `countedOps` is the number of
  selective phases and controlled reflections in it.
-/

/-- An orthogonal projection on `H`: idempotent and self-adjoint. -/
def IsOrthProj {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (P : H →L[ℂ] H) : Prop :=
  (∀ u, P (P u) = P u) ∧ ∀ u v, inner ℂ (P u) v = inner ℂ u (P v)

/-- Zhang, Lemma 3.4, pp.27–28: the three kinds of operations on `S ⊗ A`. -/
inductive SampleOp (Ω : Type*) (k : ℕ) (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] where
  /-- A sample-controlled unitary `Σ_x |x⟩⟨x|_S ⊗ V_A(x)`. -/
  | sampleControlled (V : Ω → H ≃ₗᵢ[ℂ] H)
  /-- A selective phase `I + (e^{iθ} − 1)|π_v⟩⟨π_v|_S ⊗ Π_A` through the law `v`. -/
  | selectivePhase (v : Fin k) (θ : ℝ) (P : H →L[ℂ] H) (hP : IsOrthProj P)
  /-- A controlled qsample reflection `I_S ⊗ (I_A − Π_A) + R_{π_v} ⊗ Π_A`. -/
  | ctrlRefl (v : Fin k) (P : H →L[ℂ] H) (hP : IsOrthProj P)

namespace SampleOp

variable {Ω : Type*} [Fintype Ω] {k : ℕ} {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]

/-- The partial inner product `⟨π_v|_S Ψ = Σ_x √π_v(x) ψ_x ∈ H`. -/
noncomputable def overlap (π : Ω → ℝ) (Ψ : Ω → H) : H :=
  ∑ x, ((Real.sqrt (π x) : ℝ) : ℂ) • Ψ x

/-- The action of an operation on a joint vector, given the laws `πs`. -/
noncomputable def apply (πs : Fin k → Ω → ℝ) : SampleOp Ω k H → (Ω → H) → (Ω → H)
  | sampleControlled V, Ψ => fun x => V x (Ψ x)
  | selectivePhase v θ P _, Ψ => fun y =>
      Ψ y + (Complex.exp (θ * Complex.I) - 1) •
        (((Real.sqrt (πs v y) : ℝ) : ℂ) • P (overlap (πs v) Ψ))
  | ctrlRefl v P _, Ψ => fun y =>
      (Ψ y - P (Ψ y)) +
        P ((2 * ((Real.sqrt (πs v y) : ℝ) : ℂ)) • overlap (πs v) Ψ - Ψ y)

/-- Whether an operation is counted (a selective phase or a controlled reflection). -/
def isCounted : SampleOp Ω k H → Bool
  | sampleControlled _ => false
  | selectivePhase _ _ _ _ => true
  | ctrlRefl _ _ _ => true

end SampleOp

/-- The joint vector after applying the list of operations `ops` (head first) to `Ψ₀`. -/
noncomputable def runOps {Ω : Type*} [Fintype Ω] {k : ℕ} {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (πs : Fin k → Ω → ℝ) (ops : List (SampleOp Ω k H)) (Ψ₀ : Ω → H) :
    Ω → H :=
  ops.foldl (fun Ψ op => op.apply πs Ψ) Ψ₀

/-- The number of selective phases and controlled reflections in `ops`. -/
def countedOps {Ω : Type*} {k : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ops : List (SampleOp Ω k H)) : ℕ :=
  ops.countP SampleOp.isCounted

end QVolKLS


