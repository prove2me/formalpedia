-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P98
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P98
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T08:53:03.712156+00:00
-- url     : https://prove2.me/theorems/fda40d8e-4d10-47df-9e39-bbd5ca160f6a
-- title:
--   Definitions for Semidefinite programs for completely bounded norms
-- statement:
--   The objects the formalized statements of *Semidefinite programs for completely bounded norms* (arXiv:0901.4709) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `PrimalIndex`: PDF p.7: index set for X direct-sum (Y tensor Z).
--   - `DualIndex`: PDF p.7: index set for C direct-sum Z; the scalar block survives r=0.
--   - `realTracePairing`: PDF p.3: real Hilbert--Schmidt pairing, conjugate-linear first.
--   - `unitTensor`: PDF p.4: I_Y tensor Z, with Y first.
--   - `watrousChoiMatrix`: PDF p.4: unnormalized, output-first Choi representation.
--   - `stinespringPairRepresents`: PDF p.4, equation (1): equality on ALL operators, with arbitrary complex-linear Phi.
--   - `superAdjoint`: PDF p.3: Hilbert--Schmidt adjoint in matrix-unit coordinates.
--   - `stabilizedTraceNorm`: PDF p.4: stabilized induced trace norm, with no factor 1/2. The frozen idTensorSuperop places the n-dimensional reference first, an equivalent tensor ordering. The trace-norm ball is nonempty and compact and its linear image is bounded.
--   - `cbSpectral`: PDF p.4: completely bounded spectral norm, using its adjoint identity.
--   - `primalInputCorner`: PDF p.7: the primal input block.
--   - `primalOutputCorner`: PDF p.7: the primal output/environment block.
--   - `environmentBlock`: PDF p.7: the environment block of a dual operator.
--   - `stinespringSdpMap`: PDF p.7: the ACTUAL block map Psi; off-diagonal input blocks are ignored. This is a concrete complex-linear function, rather than arbitrary SDP data.
--   - `blockAdjoint`: PDF p.7: the explicit Hilbert--Schmidt adjoint of Psi.
--   - `stinespringSdpObjective`: PDF p.7: fixed objective C = diag(0, BB*).
--   - `stinespringSdpBound`: PDF p.7: fixed bound D = diag(1,0).
--   - `BlockPrimalFeasible`: PDF pp.7--8: full-block positivity and D - Psi(P) positive semidefinite.
--   - `BlockDualFeasible`: PDF pp.7--8: full-block positivity and Psi*(S) - C positive semidefinite.
--   - `blockPrimalValue`: PDF pp.5,7: primal supremum in EReal; empty feasible set has value minus infinity.
--   - `blockDualValue`: PDF pp.5,7: dual infimum in EReal; empty feasible set has value plus infinity.
--   - `channelPrimalValues`: PDF p.11: actual channel-distance primal objectives, 0 <= W <= I_Y tensor rho.
--   - `channelDualValues`: PDF p.11: ||Tr_Y Z||_infinity with Z >= 0 and Z >= J(Phi).
--   - `stinespringProducts`: PDF p.12, Theorem 5: products over ALL Stinespring pairs and all positive-dimensional finite environments; no minimality condition.
--   - `fidelityPrimalValues`: PDF pp.13--14: fidelity primal values for arbitrary unnormalized u,v.
--   - `fidelityDualValues`: PDF p.13: the PSD dual of the fidelity primal.
--   - `fidelityPDValues`: PDF p.14, last display: constrained PD dual values; no PD minimum is asserted.
--   - `fidelityProductValues`: PDF p.15: Alberti's product objective for the two actual marginals.
-- source:
--   Semidefinite programs for completely bounded norms, arXiv:0901.4709v2, https://arxiv.org/abs/0901.4709v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Measurement

/-!
Watrous, Semidefinite programs for completely bounded norms, arXiv:0901.4709v2.
Page references are PDF pages. All new definitions belong to this paper.
Matrix and complex-linear-map types are Mathlib types, without local aliases.
Distinct real-pairing, two-operator Stinespring, and SDP-corner names avoid
confusion with unrelated accepted declarations; see ASSESSMENT.json.
Only the minimal Stinespring environment in Section 3 may have dimension zero.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakenext100.P98

/-- PDF p.7: index set for X direct-sum (Y tensor Z). -/
abbrev PrimalIndex (n m r : ℕ) := Fin n ⊕ (Fin m × Fin r)

/-- PDF p.7: index set for C direct-sum Z; the scalar block survives r=0. -/
abbrev DualIndex (r : ℕ) := Fin 1 ⊕ Fin r

/-- PDF p.3: real Hilbert--Schmidt pairing, conjugate-linear first. -/
def realTracePairing {I : Type*} [Fintype I] (A B : (Matrix I I ℂ)) : ℝ :=
  (Aᴴ * B).trace.re

/-- PDF p.4: I_Y tensor Z, with Y first. -/
def unitTensor (m : ℕ) {r : ℕ} (Z : (Matrix (Fin r) (Fin r) ℂ)) : (Matrix (Fin m × Fin r) (Fin m × Fin r) ℂ) :=
  Matrix.kronecker (1 : (Matrix (Fin m) (Fin m) ℂ)) Z

/-- PDF p.4: unnormalized, output-first Choi representation. -/
def watrousChoiMatrix {n m : ℕ} (Phi : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)) : (Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :=
  fun a b => Phi (Matrix.single a.2 b.2 1) a.1 b.1

/-- PDF p.4, equation (1): equality on ALL operators, with arbitrary complex-linear Phi. -/
def stinespringPairRepresents {n m r : ℕ} (Phi : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)) (A B : (Matrix (Fin m × Fin r) (Fin n) ℂ)) : Prop :=
  ∀ X : (Matrix (Fin n) (Fin n) ℂ), Phi X = traceRight (A * X * Bᴴ)

/-- PDF p.3: Hilbert--Schmidt adjoint in matrix-unit coordinates. -/
def superAdjoint {n m : ℕ} (Phi : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)) : (Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) where
  toFun Y i j := ∑ a : Fin m, ∑ b : Fin m,
    star (Phi (Matrix.single i j 1) a b) * Y a b
  map_add' Y Z := by
    ext i j
    change (∑ a : Fin m, ∑ b : Fin m,
      star (Phi (Matrix.single i j 1) a b) * (Y a b + Z a b)) =
        (∑ a : Fin m, ∑ b : Fin m, star (Phi (Matrix.single i j 1) a b) * Y a b) +
        (∑ a : Fin m, ∑ b : Fin m, star (Phi (Matrix.single i j 1) a b) * Z a b)
    simp only [mul_add, Finset.sum_add_distrib]
  map_smul' c Y := by
    ext i j
    change (∑ a : Fin m, ∑ b : Fin m,
      star (Phi (Matrix.single i j 1) a b) * (c * Y a b)) =
        c * (∑ a : Fin m, ∑ b : Fin m, star (Phi (Matrix.single i j 1) a b) * Y a b)
    simp only [Finset.mul_sum, mul_left_comm, mul_assoc]

/-- PDF p.4: stabilized induced trace norm, with no factor 1/2. The frozen
idTensorSuperop places the n-dimensional reference first, an equivalent tensor
ordering. The trace-norm ball is nonempty and compact and its linear image is bounded. -/
def stabilizedTraceNorm {n m : ℕ} (Phi : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)) : ℝ :=
  sSup {v : ℝ | ∃ X : (Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ),
    traceNorm X ≤ 1 ∧ v = traceNorm (idTensorSuperop (R := Fin n) Phi X)}

/-- PDF p.4: completely bounded spectral norm, using its adjoint identity. -/
def cbSpectral {n m : ℕ} (Phi : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)) : ℝ :=
  stabilizedTraceNorm (superAdjoint Phi)

/-- PDF p.7: the primal input block. -/
def primalInputCorner {n m r : ℕ} (P : (Matrix (PrimalIndex n m r) (PrimalIndex n m r) ℂ)) : (Matrix (Fin n) (Fin n) ℂ) :=
  fun i j => P (Sum.inl i) (Sum.inl j)

/-- PDF p.7: the primal output/environment block. -/
def primalOutputCorner {n m r : ℕ} (P : (Matrix (PrimalIndex n m r) (PrimalIndex n m r) ℂ)) : (Matrix (Fin m × Fin r) (Fin m × Fin r) ℂ) :=
  fun i j => P (Sum.inr i) (Sum.inr j)

/-- PDF p.7: the environment block of a dual operator. -/
def environmentBlock {r : ℕ} (S : (Matrix (DualIndex r) (DualIndex r) ℂ)) : (Matrix (Fin r) (Fin r) ℂ) :=
  fun i j => S (Sum.inr i) (Sum.inr j)

/-- PDF p.7: the ACTUAL block map Psi; off-diagonal input blocks are ignored.
This is a concrete complex-linear function, rather than arbitrary SDP data. -/
def stinespringSdpMap {n m r : ℕ} (A : (Matrix (Fin m × Fin r) (Fin n) ℂ))
    (P : (Matrix (PrimalIndex n m r) (PrimalIndex n m r) ℂ)) : (Matrix (DualIndex r) (DualIndex r) ℂ) :=
  Matrix.fromBlocks (fun _ _ : Fin 1 => (primalInputCorner P).trace) 0 0
    (traceLeft (primalOutputCorner P - A * primalInputCorner P * Aᴴ))

/-- PDF p.7: the explicit Hilbert--Schmidt adjoint of Psi. -/
def blockAdjoint {n m r : ℕ} (A : (Matrix (Fin m × Fin r) (Fin n) ℂ))
    (S : (Matrix (DualIndex r) (DualIndex r) ℂ)) : (Matrix (PrimalIndex n m r) (PrimalIndex n m r) ℂ) :=
  Matrix.fromBlocks
    (S (Sum.inl 0) (Sum.inl 0) • (1 : (Matrix (Fin n) (Fin n) ℂ)) -
      Aᴴ * unitTensor m (environmentBlock S) * A)
    0 0 (unitTensor m (environmentBlock S))

/-- PDF p.7: fixed objective C = diag(0, BB*). -/
def stinespringSdpObjective {n m r : ℕ} (B : (Matrix (Fin m × Fin r) (Fin n) ℂ)) : (Matrix (PrimalIndex n m r) (PrimalIndex n m r) ℂ) :=
  Matrix.fromBlocks 0 0 0 (B * Bᴴ)

/-- PDF p.7: fixed bound D = diag(1,0). -/
def stinespringSdpBound (r : ℕ) : (Matrix (DualIndex r) (DualIndex r) ℂ) :=
  Matrix.fromBlocks (1 : (Matrix (Fin 1) (Fin 1) ℂ)) 0 0 0

/-- PDF pp.7--8: full-block positivity and D - Psi(P) positive semidefinite. -/
def BlockPrimalFeasible {n m r : ℕ} (A : (Matrix (Fin m × Fin r) (Fin n) ℂ))
    (P : (Matrix (PrimalIndex n m r) (PrimalIndex n m r) ℂ)) : Prop :=
  P.PosSemidef ∧ (stinespringSdpBound r - stinespringSdpMap A P).PosSemidef

/-- PDF pp.7--8: full-block positivity and Psi*(S) - C positive semidefinite. -/
def BlockDualFeasible {n m r : ℕ} (A B : (Matrix (Fin m × Fin r) (Fin n) ℂ))
    (S : (Matrix (DualIndex r) (DualIndex r) ℂ)) : Prop :=
  S.PosSemidef ∧ (blockAdjoint A S - stinespringSdpObjective B).PosSemidef

/-- PDF pp.5,7: primal supremum in EReal; empty feasible set has value minus infinity. -/
def blockPrimalValue {n m r : ℕ} (A B : (Matrix (Fin m × Fin r) (Fin n) ℂ)) : EReal :=
  sSup {v : EReal | ∃ P : (Matrix (PrimalIndex n m r) (PrimalIndex n m r) ℂ),
    BlockPrimalFeasible A P ∧ v = (realTracePairing (stinespringSdpObjective B) P : EReal)}

/-- PDF pp.5,7: dual infimum in EReal; empty feasible set has value plus infinity. -/
def blockDualValue {n m r : ℕ} (A B : (Matrix (Fin m × Fin r) (Fin n) ℂ)) : EReal :=
  sInf {v : EReal | ∃ S : (Matrix (DualIndex r) (DualIndex r) ℂ),
    BlockDualFeasible A B S ∧ v = (realTracePairing (stinespringSdpBound r) S : EReal)}

/-- PDF p.11: actual channel-distance primal objectives, 0 <= W <= I_Y tensor rho. -/
def channelPrimalValues {n m : ℕ} (Phi : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)) : Set ℝ :=
  {v | ∃ (rho : (Matrix (Fin n) (Fin n) ℂ)) (W : (Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)),
    IsDensityMatrix rho ∧ W.PosSemidef ∧ (unitTensor m rho - W).PosSemidef ∧
    v = realTracePairing (watrousChoiMatrix Phi) W}

/-- PDF p.11: ||Tr_Y Z||_infinity with Z >= 0 and Z >= J(Phi). -/
def channelDualValues {n m : ℕ} (Phi : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)) : Set ℝ :=
  {v | ∃ Z : (Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ),
    Z.PosSemidef ∧ (Z - watrousChoiMatrix Phi).PosSemidef ∧ v = specNorm (traceLeft Z)}

/-- PDF p.12, Theorem 5: products over ALL Stinespring pairs and all
positive-dimensional finite environments; no minimality condition. -/
def stinespringProducts {n m : ℕ} (Phi : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)) : Set ℝ :=
  {v | ∃ (r : ℕ), 0 < r ∧ ∃ A B : (Matrix (Fin m × Fin r) (Fin n) ℂ),
    stinespringPairRepresents Phi A B ∧ v = specNorm A * specNorm B}

/-- PDF pp.13--14: fidelity primal values for arbitrary unnormalized u,v. -/
def fidelityPrimalValues {m r : ℕ} (u v : EuclideanSpace ℂ (Fin m × Fin r)) : Set ℝ :=
  {a | ∃ W : (Matrix (Fin m × Fin r) (Fin m × Fin r) ℂ), W.PosSemidef ∧
    (traceLeft (pureDensity u) - traceLeft W).PosSemidef ∧
    a = realTracePairing (pureDensity v) W}

/-- PDF p.13: the PSD dual of the fidelity primal. -/
def fidelityDualValues {m r : ℕ} (u v : EuclideanSpace ℂ (Fin m × Fin r)) : Set ℝ :=
  {a | ∃ Z : (Matrix (Fin r) (Fin r) ℂ), Z.PosSemidef ∧
    (unitTensor m Z - pureDensity v).PosSemidef ∧
    a = realTracePairing (traceLeft (pureDensity u)) Z}

/-- PDF p.14, last display: constrained PD dual values; no PD minimum is asserted. -/
def fidelityPDValues {m r : ℕ} (u v : EuclideanSpace ℂ (Fin m × Fin r)) : Set ℝ :=
  {a | ∃ Z : (Matrix (Fin r) (Fin r) ℂ), Z.PosDef ∧
    realTracePairing (traceLeft (pureDensity v)) Z⁻¹ ≤ 1 ∧
    a = realTracePairing (traceLeft (pureDensity u)) Z}

/-- PDF p.15: Alberti's product objective for the two actual marginals. -/
def fidelityProductValues {m r : ℕ} (u v : EuclideanSpace ℂ (Fin m × Fin r)) : Set ℝ :=
  {a | ∃ Z : (Matrix (Fin r) (Fin r) ℂ), Z.PosDef ∧
    a = realTracePairing (traceLeft (pureDensity u)) Z * realTracePairing (traceLeft (pureDensity v)) Z⁻¹}

/-- Sanity: zero Hilbert--Schmidt pairing, PDF p.3. -/
example {I : Type*} [Fintype I] (A : (Matrix I I ℂ)) : realTracePairing 0 A = 0 := by
  simp [realTracePairing]

/-- Sanity: I_C tensor Z has no extra scalar, PDF p.4. -/
example {r : ℕ} (Z : (Matrix (Fin r) (Fin r) ℂ)) (i j : Fin r) :
    unitTensor 1 Z (0, i) (0, j) = Z i j := by
  simp [unitTensor, Matrix.kronecker, Matrix.one_apply]

/-- Sanity: the zero map has zero Choi matrix, PDF p.4. -/
example {n m : ℕ} : watrousChoiMatrix (0 : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)) = 0 := by
  ext a b
  rfl

/-- Sanity: the zero pair represents zero even in a zero-dimensional environment. -/
example {n m r : ℕ} : stinespringPairRepresents (0 : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ))
    (0 : (Matrix (Fin m × Fin r) (Fin n) ℂ)) (0 : (Matrix (Fin m × Fin r) (Fin n) ℂ)) := by
  intro X
  ext i j
  simp [traceRight, Matrix.zero_apply]

/-- Sanity: the coordinate adjoint maps zero to zero, PDF p.3. -/
example {n m : ℕ} : superAdjoint (0 : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)) = 0 := by
  ext Y i j
  change (∑ a : Fin m, ∑ b : Fin m, star (0 : ℂ) * Y a b) = 0
  simp

/-- Sanity: Psi's scalar entry is Tr X, PDF p.7. -/
example {n m r : ℕ} (A : (Matrix (Fin m × Fin r) (Fin n) ℂ)) (P : (Matrix (PrimalIndex n m r) (PrimalIndex n m r) ℂ)) :
    stinespringSdpMap A P (Sum.inl 0) (Sum.inl 0) = (primalInputCorner P).trace := by
  rfl

/-- Sanity: Psi ignores off-diagonal blocks, PDF p.7. -/
example {n m r : ℕ} (A : (Matrix (Fin m × Fin r) (Fin n) ℂ)) (P : (Matrix (PrimalIndex n m r) (PrimalIndex n m r) ℂ)) (i : Fin r) :
    stinespringSdpMap A P (Sum.inl 0) (Sum.inr i) = 0 := by
  rfl

/-- Sanity: the environment block of Psi*, PDF p.7. -/
example {n m r : ℕ} (A : (Matrix (Fin m × Fin r) (Fin n) ℂ)) (S : (Matrix (DualIndex r) (DualIndex r) ℂ))
    (i j : Fin m × Fin r) :
    blockAdjoint A S (Sum.inr i) (Sum.inr j) = unitTensor m (environmentBlock S) i j := by
  rfl

/-- Sanity: the actual objective's lower block is BB*, PDF p.7. -/
example {n m r : ℕ} (B : (Matrix (Fin m × Fin r) (Fin n) ℂ)) (i j : Fin m × Fin r) :
    stinespringSdpObjective B (Sum.inr i) (Sum.inr j) = (B * Bᴴ) i j := by
  rfl

/-- Sanity: the scalar bound is still one with an empty environment, PDF p.7. -/
example : stinespringSdpBound 0 (Sum.inl 0) (Sum.inl 0) = 1 := by
  rfl

end QAlgorithms.Papers.Independent.Intakenext100.P98


