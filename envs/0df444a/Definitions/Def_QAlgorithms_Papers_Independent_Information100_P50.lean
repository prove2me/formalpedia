-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50
-- name    : QAlgorithms_Papers_Independent_Information100_P50
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T11:50:58.727097+00:00
-- url     : https://prove2.me/theorems/6b1d8138-3501-43a8-8fa0-a2d07bd2ddbd
-- title:
--   Definitions for Quantitative upper bounds for certain quantum channel divergences
-- statement:
--   The objects the formalized statements of *Quantitative upper bounds for certain quantum channel divergences* (arXiv:2610.16270) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `M`
--   - `Lin`
--   - `cpOrder`: CP order, source PDF p.3; no trace preservation is imposed.
--   - `coefficientMap`: A coordinate tensor gives a complex-linear map; used for the source's Kraus sums.
--   - `arnFamily`: Source PDF p.3: the full ARN coefficient family, including nonpositive Hermitian T.
--   - `krausMap`: Source PDF pp.3–4: the CP map with Kraus family V. Empty V gives the zero map.
--   - `choiMatrix`: Unnormalized Choi matrix, output factor first; source PDF p.3.
--   - `krausColumnMatrix`: Columns vec(V_k), indexed by output × input; source PDF p.3.
--   - `stinespringOperator`: The source Stinespring matrix S_(y,k),x=V_k(y,x), PDF p.4.
--   - `complementaryMap`: Complement obtained by tracing out Y, source PDF p.4.
--   - `hilbertSchmidtAdjoint`: Hilbert–Schmidt adjoint, in coordinates, source PDF pp.4–5.
--   - `amplify`: Amplification with the reference factor first; the simultaneous swap of both output factors does not alter norms, traces, or means. Source PDF pp.9–10,25.
--   - `schattenNorm`: Induced Schatten p norm; p=top means operator norm. Source PDF p.25.
--   - `inducedNorm`: Full induced norm on all complex matrices, source PDF p.25.
--   - `cbNorm`: Completely bounded p→p norm: supremum over every finite ancilla, source PDF pp.25,28.
--   - `cbTraceNorm`: Completely bounded trace norm, without a factor 1/2; source PDF pp.4,12.
--   - `hermitianAbsoluteValue`: Hermitian absolute value, source PDF p.12.
--   - `loewner`: Loewner comparison, source PDF p.5.
--   - `OperatorMonotone`: All-size operator monotonicity on the positive half line, source PDF p.6.
--   - `OperatorConvex`: All-size operator convexity on the positive half line, source PDF p.20.
--   - `atZero`: Endpoint limits are computed, rather than unrelated supplied scalars. Source PDF p.7.
--   - `atInfinity`: Recession slope, source PDF p.7; for bounded generators existence is a hypothesis.
--   - `Connection`: Connections encoded by the exact representing-function classification (Theorem 2.11, PDF pp.6–7): nonnegative all-size operator monotone functions. Values at nonpositive arguments are immaterial to this representation. No normalization is imposed.
--   - `Mean`: A Kubo–Ando mean is a normalized connection, source Definition 2.12, PDF p.7.
--   - `perspective`: Perspective for positive definite arguments: B^(1/2) f(B^(-1/2) A B^(-1/2)) B^(1/2). Source PDF pp.6,20.
--   - `regularizedPerspective`: Simultaneous positive regularization; source PDF pp.6–7,20. The limits exist on PSD pairs for the representing functions and bounded generators used below.
--   - `connectionOp`: A sigma B has the opposite argument order to the divergence perspective, PDF p.6.
--   - `geometricMean`: Geometric mean including singular inputs, source PDF p.7.
--   - `meanPerspective`: Scalar effect perspective of a mean, including both endpoints, source PDF p.7.
--   - `intrinsicKraus`: Kraus rank is allowed to be zero; this is a choice among all independent Kraus representations, not extra data constrained by a target conclusion. Source PDF pp.3,7.
--   - `arnDerivative`: ARN coefficient computed by W^+=(W*W)^(-1)W*, source proof of Lemma 2.1, PDF p.3.
--   - `cpMeanBy`: Intrinsic Kraus mean from Section 2.5, PDF p.7. Its Choi identity is not assumed.
--   - `cpMean`: Mean of CP maps, source PDF p.7.
--   - `cpGeometricMean`: Geometric mean of CP maps, source PDF pp.7–9.
--   - `geometricFidelity`: UNSQUARED geometric channel fidelity, infimum over the same bipartite density input. Reference factor first; source PDF pp.9–10.
--   - `renyiQ`: Geometric Renyi quasi-entropy for 0<alpha<1, source PDF p.17.
--   - `BoundedGenerator`: The admissible bounded generators of Lemma 5.12, source PDF pp.20–21. The endpoints are finite real limits; f itself need not be nonnegative.
--   - `stateDivergence`: State divergence, independently defined by regularization, source Definition 5.8, p.20.
--   - `channelDivergence`: Channel divergence, supremum over common density inputs, Definition 5.9, PDF p.20. Real-valued for bounded generators on CP maps; negative values are permitted.
--   - `convexPerspective`: Convex effect perspective, source PDF pp.21–22; endpoint order differs from g_sigma.
--   - `affineRemainder`: Affine remainder h in Lemma 5.12, source PDF p.21.
--   - `modulusValues`: All finite matrix sizes participate in the modulus, source Theorem 4.5, PDF p.14.
--   - `operatorModulus`: The source's dimension-independent operator modulus, for delta≥0 and continuous g on [0,1]. Its defining set is nonempty and bounded, as explicitly recorded in Lemma 4.7.
--   - `gHash`: Source PDF pp.13–14.
--   - `hAlpha`: Source PDF p.18; endpoints are zero for 0<alpha<1.
--   - `replacementMap`: Replacement channel, source PDF p.11.
--   - `replacementAverage`: Equal splitting of the sum of two replacement channels, source PDF p.11.
--   - `maxEigenvalue`: Maximum eigenvalue, source PDF pp.22–23; uses require a nonempty input space.
--   - `matrixRange`: Matrix range as a linear subspace, source Theorem 5.6, PDF p.19.
--   - `IsUINorm`: An arbitrary unitarily invariant norm, with its norm axioms explicit, source PDF p.25.
--   - `hellingerGenerator`: Named generator examples, source Definition 5.10, PDF p.20.
--   - `alphaGenerator`: Hellinger generator of order alpha, source Definition 5.10(2), PDF p.20.
--   - `lcGenerator`: Vincze–Le Cam generator, source Definition 5.10(3), PDF p.20.
--   - `jsGenerator`: Jensen–Shannon generator, source Definition 5.10(4), PDF p.20.
-- source:
--   Quantitative upper bounds for certain quantum channel divergences, arXiv:2610.16270v1, https://arxiv.org/abs/2610.16270v1

import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_Hamiltonian

/-!
Statements from Morgan Jones, arXiv:2610.16270v1 (October 2026).
All new definitions are local to this paper. Matrix means use the representing-function
classification of Theorem 2.11 and simultaneous positive regularization. Channel means
use the intrinsic Kraus construction of Section 2.5, independently of the Choi identities.
No theorem conclusion is a field of the data used to state it.
-/

noncomputable section

open scoped Matrix ComplexConjugate ENNReal Topology ComplexOrder Kronecker
open Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P50

abbrev M (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

abbrev Lin (dx dy : ℕ) := M dx →ₗ[ℂ] M dy

/-- CP order, source PDF p.3; no trace preservation is imposed. -/
def cpOrder {dx dy : ℕ} (Phi Psi : Lin dx dy) : Prop :=
  Entanglement.IsCompletelyPositive Phi ∧ Entanglement.IsCompletelyPositive (Psi - Phi)

/-- A coordinate tensor gives a complex-linear map; used for the source's Kraus sums. -/
def coefficientMap {dx dy : ℕ} (C : Fin dy → Fin dy → Fin dx → Fin dx → ℂ) : Lin dx dy where
  toFun X y z := ∑ a, ∑ b, C y z a b * X a b
  map_add' X Y := by
    ext y z
    change (∑ a, ∑ b, C y z a b * (X a b + Y a b)) =
      (∑ a, ∑ b, C y z a b * X a b) + (∑ a, ∑ b, C y z a b * Y a b)
    simp only [mul_add, Finset.sum_add_distrib]
  map_smul' c X := by
    ext y z
    change (∑ a, ∑ b, C y z a b * (c * X a b)) =
      c * (∑ a, ∑ b, C y z a b * X a b)
    simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

/-- Source PDF p.3: the full ARN coefficient family, including nonpositive Hermitian T. -/
def arnFamily {dx dy r : ℕ} (V : Fin r → Matrix (Fin dy) (Fin dx) ℂ) (T : M r) : Lin dx dy :=
  coefficientMap fun y z a b => ∑ k, ∑ l, T k l * V k y a * conj (V l z b)

/-- Source PDF pp.3–4: the CP map with Kraus family V. Empty V gives the zero map. -/
def krausMap {dx dy r : ℕ} (V : Fin r → Matrix (Fin dy) (Fin dx) ℂ) : Lin dx dy :=
  arnFamily V 1

/-- Unnormalized Choi matrix, output factor first; source PDF p.3. -/
def choiMatrix {dx dy : ℕ} (Phi : Lin dx dy) :
    Matrix (Fin dy × Fin dx) (Fin dy × Fin dx) ℂ :=
  fun p q => Phi (Matrix.single p.2 q.2 1) p.1 q.1

/-- Columns vec(V_k), indexed by output × input; source PDF p.3. -/
def krausColumnMatrix {dx dy r : ℕ} (V : Fin r → Matrix (Fin dy) (Fin dx) ℂ) :
    Matrix (Fin dy × Fin dx) (Fin r) ℂ := fun p k => V k p.1 p.2

/-- The source Stinespring matrix S_(y,k),x=V_k(y,x), PDF p.4. -/
def stinespringOperator {dx dy r : ℕ} (V : Fin r → Matrix (Fin dy) (Fin dx) ℂ) :
    Matrix (Fin dy × Fin r) (Fin dx) ℂ := fun p x => V p.2 p.1 x

/-- Complement obtained by tracing out Y, source PDF p.4. -/
def complementaryMap {dx dy r : ℕ} (V : Fin r → Matrix (Fin dy) (Fin dx) ℂ) : Lin dx r :=
  coefficientMap fun k l a b => ∑ y, V k y a * conj (V l y b)

/-- Hilbert–Schmidt adjoint, in coordinates, source PDF pp.4–5. -/
def hilbertSchmidtAdjoint {dx dy : ℕ} (Phi : Lin dx dy) (Y : M dy) : M dx :=
  fun a b => ∑ y, ∑ z, conj (Phi (Matrix.single a b 1) y z) * Y y z

/-- Amplification with the reference factor first; the simultaneous swap of both output
factors does not alter norms, traces, or means. Source PDF pp.9–10,25. -/
def amplify {dx dy : ℕ} (Phi : Lin dx dy) (m : ℕ)
    (X : Matrix (Fin m × Fin dx) (Fin m × Fin dx) ℂ) :
    Matrix (Fin m × Fin dy) (Fin m × Fin dy) ℂ := idTensorSuperop Phi X

/-- Induced Schatten p norm; p=top means operator norm. Source PDF p.25. -/
def schattenNorm {I : Type*} [Fintype I] [DecidableEq I]
    (p : ℝ≥0∞) (A : Matrix I I ℂ) : ℝ :=
  if p = ⊤ then specNorm A
  else Real.rpow ((cfc (fun t : ℝ => Real.rpow t (p.toReal / 2)) (Aᴴ * A)).trace.re)
    (1 / p.toReal)

/-- Full induced norm on all complex matrices, source PDF p.25. -/
def inducedNorm {dx dy : ℕ} (p : ℝ≥0∞) (Phi : Lin dx dy) : ℝ :=
  sSup {v : ℝ | ∃ X : M dx, schattenNorm p X ≤ 1 ∧ v = schattenNorm p (Phi X)}

/-- Completely bounded p→p norm: supremum over every finite ancilla, source PDF pp.25,28. -/
def cbNorm {dx dy : ℕ} (p : ℝ≥0∞) (Phi : Lin dx dy) : ℝ :=
  sSup {v : ℝ | ∃ (m : ℕ) (X : Matrix (Fin m × Fin dx) (Fin m × Fin dx) ℂ),
    schattenNorm p X ≤ 1 ∧ v = schattenNorm p (amplify Phi m X)}

/-- Completely bounded trace norm, without a factor 1/2; source PDF pp.4,12. -/
def cbTraceNorm {dx dy : ℕ} (Phi : Lin dx dy) : ℝ := cbNorm 1 Phi

/-- Hermitian absolute value, source PDF p.12. -/
def hermitianAbsoluteValue {n : ℕ} (A : M n) : M n := cfc (fun t : ℝ => |t|) A

/-- Loewner comparison, source PDF p.5. -/
def loewner {I : Type*} [Fintype I] (A B : Matrix I I ℂ) : Prop := (B - A).PosSemidef

/-- All-size operator monotonicity on the positive half line, source PDF p.6. -/
def OperatorMonotone (f : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (A B : M n), A.PosDef → B.PosDef → loewner A B → loewner (cfc f A) (cfc f B)

/-- All-size operator convexity on the positive half line, source PDF p.20. -/
def OperatorConvex (f : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (A B : M n), A.PosDef → B.PosDef → ∀ t ∈ Icc (0 : ℝ) 1,
    loewner (cfc f ((t : ℂ) • A + ((1 - t : ℝ) : ℂ) • B))
      ((t : ℂ) • cfc f A + ((1 - t : ℝ) : ℂ) • cfc f B)

/-- Endpoint limits are computed, rather than unrelated supplied scalars. Source PDF p.7. -/
def atZero (f : ℝ → ℝ) : ℝ := limUnder (𝓝[>] (0 : ℝ)) f

/-- Recession slope, source PDF p.7; for bounded generators existence is a hypothesis. -/
def atInfinity (f : ℝ → ℝ) : ℝ := limUnder atTop (fun t : ℝ => f t / t)

/-- Connections encoded by the exact representing-function classification (Theorem 2.11,
PDF pp.6–7): nonnegative all-size operator monotone functions. Values at nonpositive
arguments are immaterial to this representation. No normalization is imposed. -/
structure Connection where
  f : ℝ → ℝ
  nonnegative : ∀ t > 0, 0 ≤ f t
  monotone : OperatorMonotone f

/-- A Kubo–Ando mean is a normalized connection, source Definition 2.12, PDF p.7. -/
structure Mean extends Connection where
  normalized : f 1 = 1

/-- Perspective for positive definite arguments: B^(1/2) f(B^(-1/2) A B^(-1/2)) B^(1/2).
Source PDF pp.6,20. -/
def perspective {I : Type*} [Fintype I] [DecidableEq I]
    (f : ℝ → ℝ) (A B : Matrix I I ℂ) : Matrix I I ℂ :=
  let R := cfc Real.sqrt B
  let Q := cfc (fun t : ℝ => (Real.sqrt t)⁻¹) B
  R * cfc f (Q * A * Q) * R

/-- Simultaneous positive regularization; source PDF pp.6–7,20. The limits exist on PSD
pairs for the representing functions and bounded generators used below. -/
def regularizedPerspective {I : Type*} [Fintype I] [DecidableEq I]
    (f : ℝ → ℝ) (A B : Matrix I I ℂ) : Matrix I I ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) fun e =>
    perspective f (A + (e : ℂ) • 1) (B + (e : ℂ) • 1)

/-- A sigma B has the opposite argument order to the divergence perspective, PDF p.6. -/
def connectionOp {I : Type*} [Fintype I] [DecidableEq I]
    (s : Connection) (A B : Matrix I I ℂ) : Matrix I I ℂ :=
  regularizedPerspective s.f B A

/-- Geometric mean including singular inputs, source PDF p.7. -/
def geometricMean {I : Type*} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) : Matrix I I ℂ := regularizedPerspective Real.sqrt B A

/-- Scalar effect perspective of a mean, including both endpoints, source PDF p.7. -/
def meanPerspective (s : Mean) (t : ℝ) : ℝ :=
  if t = 0 then atInfinity s.f else if t = 1 then atZero s.f else t * s.f ((1 - t) / t)

/-- Kraus rank is allowed to be zero; this is a choice among all independent Kraus
representations, not extra data constrained by a target conclusion. Source PDF pp.3,7. -/
def intrinsicKraus {dx dy : ℕ} (Omega : Lin dx dy) :
    Sigma (fun r : ℕ => Fin r → Matrix (Fin dy) (Fin dx) ℂ) :=
  Classical.epsilon fun K => LinearIndependent ℂ K.2 ∧ krausMap K.2 = Omega

/-- ARN coefficient computed by W^+=(W*W)^(-1)W*, source proof of Lemma 2.1, PDF p.3. -/
def arnDerivative {dx dy r : ℕ} (V : Fin r → Matrix (Fin dy) (Fin dx) ℂ)
    (Phi : Lin dx dy) : M r :=
  let W := krausColumnMatrix V
  let P := (Wᴴ * W)⁻¹ * Wᴴ
  P * choiMatrix Phi * Pᴴ

/-- Intrinsic Kraus mean from Section 2.5, PDF p.7. Its Choi identity is not assumed. -/
def cpMeanBy {dx dy : ℕ} (f : ℝ → ℝ) (Phi Psi : Lin dx dy) : Lin dx dy :=
  let K := intrinsicKraus (Phi + Psi)
  let T := arnDerivative K.2 Phi
  arnFamily K.2 (regularizedPerspective f (1 - T) T)

/-- Mean of CP maps, source PDF p.7. -/
def cpMean {dx dy : ℕ} (s : Mean) (Phi Psi : Lin dx dy) : Lin dx dy := cpMeanBy s.f Phi Psi

/-- Geometric mean of CP maps, source PDF pp.7–9. -/
def cpGeometricMean {dx dy : ℕ} (Phi Psi : Lin dx dy) : Lin dx dy := cpMeanBy Real.sqrt Phi Psi

/-- UNSQUARED geometric channel fidelity, infimum over the same bipartite density input.
Reference factor first; source PDF pp.9–10. -/
def geometricFidelity {dx dy : ℕ} (Phi Psi : Lin dx dy) : ℝ :=
  sInf {v : ℝ | ∃ rho : Matrix (Fin dx × Fin dx) (Fin dx × Fin dx) ℂ,
    IsDensityMatrix rho ∧ v = (geometricMean (amplify Phi dx rho) (amplify Psi dx rho)).trace.re}

/-- Geometric Renyi quasi-entropy for 0<alpha<1, source PDF p.17. -/
def renyiQ {dx dy : ℕ} (alpha : ℝ) (Phi Psi : Lin dx dy) : ℝ :=
  sInf {v : ℝ | ∃ rho : Matrix (Fin dx × Fin dx) (Fin dx × Fin dx) ℂ,
    IsDensityMatrix rho ∧ v = (regularizedPerspective (fun t : ℝ => Real.rpow t alpha)
      (amplify Phi dx rho) (amplify Psi dx rho)).trace.re}

/-- The admissible bounded generators of Lemma 5.12, source PDF pp.20–21.
The endpoints are finite real limits; f itself need not be nonnegative. -/
structure BoundedGenerator where
  f : ℝ → ℝ
  convex : OperatorConvex f
  normalized : f 1 = 0
  finiteZero : ∃ a : ℝ, Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 a)
  finiteInfinity : ∃ a : ℝ, Tendsto (fun t : ℝ => f t / t) atTop (𝓝 a)

/-- State divergence, independently defined by regularization, source Definition 5.8, p.20. -/
def stateDivergence {I : Type*} [Fintype I] [DecidableEq I]
    (f : ℝ → ℝ) (A B : Matrix I I ℂ) : ℝ := (regularizedPerspective f A B).trace.re

/-- Channel divergence, supremum over common density inputs, Definition 5.9, PDF p.20.
Real-valued for bounded generators on CP maps; negative values are permitted. -/
def channelDivergence {dx dy : ℕ} (f : ℝ → ℝ) (Phi Psi : Lin dx dy) : ℝ :=
  sSup {v : ℝ | ∃ rho : Matrix (Fin dx × Fin dx) (Fin dx × Fin dx) ℂ,
    IsDensityMatrix rho ∧ v = stateDivergence f (amplify Phi dx rho) (amplify Psi dx rho)}

/-- Convex effect perspective, source PDF pp.21–22; endpoint order differs from g_sigma. -/
def convexPerspective (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t = 0 then atZero f else if t = 1 then atInfinity f else (1 - t) * f (t / (1 - t))

/-- Affine remainder h in Lemma 5.12, source PDF p.21. -/
def affineRemainder (f : ℝ → ℝ) (t : ℝ) : ℝ := atZero f + atInfinity f * t - f t

/-- All finite matrix sizes participate in the modulus, source Theorem 4.5, PDF p.14. -/
def modulusValues (g : ℝ → ℝ) (delta : ℝ) : Set ℝ :=
  {v | ∃ (n : ℕ) (E F : M n), IsEffect E ∧ IsEffect F ∧ specNorm (E - F) ≤ delta ∧
    v = specNorm (cfc g E - cfc g F)}

/-- The source's dimension-independent operator modulus, for delta≥0 and continuous g on
[0,1]. Its defining set is nonempty and bounded, as explicitly recorded in Lemma 4.7. -/
def operatorModulus (g : ℝ → ℝ) (delta : ℝ) : ℝ := sSup (modulusValues g delta)

/-- Source PDF pp.13–14. -/
def gHash (t : ℝ) : ℝ := Real.sqrt (t * (1 - t))

/-- Source PDF p.18; endpoints are zero for 0<alpha<1. -/
def hAlpha (alpha t : ℝ) : ℝ := Real.rpow t alpha * Real.rpow (1 - t) (1 - alpha)

/-- Replacement channel, source PDF p.11. -/
def replacementMap {dx dy : ℕ} (a : EuclideanSpace ℂ (Fin dy)) : Lin dx dy :=
  coefficientMap fun y z i j => if i = j then a y * conj (a z) else 0

/-- Equal splitting of the sum of two replacement channels, source PDF p.11. -/
def replacementAverage {dx dy : ℕ} (a b : EuclideanSpace ℂ (Fin dy)) : Lin dx dy :=
  (1 / 2 : ℂ) • (replacementMap a + replacementMap b)

/-- Maximum eigenvalue, source PDF pp.22–23; uses require a nonempty input space. -/
def maxEigenvalue {I : Type*} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) : ℝ :=
  -minEigenvalue (-A)

/-- Matrix range as a linear subspace, source Theorem 5.6, PDF p.19. -/
def matrixRange {I : Type*} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) : Submodule ℂ (I → ℂ) :=
  LinearMap.range (Matrix.toLin' A)

/-- An arbitrary unitarily invariant norm, with its norm axioms explicit, source PDF p.25. -/
def IsUINorm {I : Type*} [Fintype I] [DecidableEq I] (N : Matrix I I ℂ → ℝ) : Prop :=
  (∀ A, 0 ≤ N A) ∧ (∀ A, N A = 0 ↔ A = 0) ∧
  (∀ A B, N (A + B) ≤ N A + N B) ∧ (∀ c : ℂ, ∀ A, N (c • A) = ‖c‖ * N A) ∧
  (∀ U V : Matrix.unitaryGroup I ℂ, ∀ A, N ((U : Matrix I I ℂ) * A * (V : Matrix I I ℂ)) = N A)

/-- Named generator examples, source Definition 5.10, PDF p.20. -/
def hellingerGenerator (t : ℝ) : ℝ := (1 - Real.sqrt t) ^ 2

/-- Hellinger generator of order alpha, source Definition 5.10(2), PDF p.20. -/
def alphaGenerator (alpha t : ℝ) : ℝ := (1 - Real.rpow t alpha) / (1 - alpha)

/-- Vincze–Le Cam generator, source Definition 5.10(3), PDF p.20. -/
def lcGenerator (t : ℝ) : ℝ := (t - 1) ^ 2 / (t + 1)

/-- Jensen–Shannon generator, source Definition 5.10(4), PDF p.20. -/
def jsGenerator (t : ℝ) : ℝ := t * Real.log t - (1 + t) * Real.log ((1 + t) / 2)

/-! Sanity checks pinning local definitions; no target theorem is proved here. -/

example {dx dy r : ℕ} (V : Fin r → Matrix (Fin dy) (Fin dx) ℂ) : arnFamily V 0 = 0 := by
  ext X y z
  change (∑ a, ∑ b, (∑ k, ∑ l, (0 : M r) k l * V k y a * conj (V l z b)) * X a b) = 0
  simp

example {dx dy : ℕ} : choiMatrix (0 : Lin dx dy) = 0 := by
  rfl

example {dx dy : ℕ} (V : Fin 0 → Matrix (Fin dy) (Fin dx) ℂ) (T : M 0) :
    arnFamily V T = 0 := by
  ext X y z
  change (∑ a, ∑ b, (∑ k, ∑ l, T k l * V k y a * conj (V l z b)) * X a b) = 0
  simp

example : gHash 0 = 0 ∧ gHash 1 = 0 := by
  simp [gHash]

example (f : ℝ → ℝ) : convexPerspective f 0 = atZero f ∧ convexPerspective f 1 = atInfinity f := by
  simp [convexPerspective]

example (s : Mean) : meanPerspective s 0 = atInfinity s.f ∧ meanPerspective s 1 = atZero s.f := by
  simp [meanPerspective]

example {n : ℕ} : hermitianAbsoluteValue (0 : M n) = 0 := by
  simp [hermitianAbsoluteValue, cfc_zero]

example {I : Type*} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) :
    schattenNorm ⊤ A = specNorm A := by
  simp [schattenNorm]

example {dx dy r : ℕ} (V : Fin r → Matrix (Fin dy) (Fin dx) ℂ)
    (y : Fin dy) (k : Fin r) (x : Fin dx) :
    stinespringOperator V (y, k) x = krausColumnMatrix V (y, x) k := by
  rfl

end QAlgorithms.Papers.Independent.Information100.P50


