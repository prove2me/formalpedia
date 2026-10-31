-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P46
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P46
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T05:56:32.203971+00:00
-- url     : https://prove2.me/theorems/fcd7437b-dca5-4095-b2b8-c9383d19f71d
-- title:
--   Definitions for Gaussian relative entropy of entanglement
-- statement:
--   The objects the formalized statements of *Gaussian relative entropy of entanglement* (arXiv:quant-ph/0402109) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `operatorRelativeEntropy`: PDF p.4, (16): extended Umegaki entropy in nats via finite orthogonal compressions of generalized entropy, including its unequal-trace correction. Infinity on support failure is preserved; no covariance expression defines D.
--   - `densityEntropy`: PDF pp.4–5: independently defined spectral entropy in nats. The continuous weight -x log x vanishes at zero; the nonnegative trace retains infinity.
--   - `ree`: PDF p.4: unrestricted REE; no energy, rank or Gaussian restriction.
--   - `StateBorder`: PDF p.4: boundary inside normalized states in trace norm.
--   - `GroupedPhase`: PDF p.2: grouped coordinates, all q before all p.
--   - `ModeMatrix`: PDF p.2: real covariance/exponential arrays, not density operators.
--   - `groupedCCR`: PDF p.2, (3): grouped canonical form with [q_j,p_k]=i delta_jk.
--   - `IsPhysicalCovariance`: PDF p.2: symmetric covariance with alpha-i Delta/2 nonnegative.
--   - `StrictPhysical`: PDF pp.2–3: finite exponential chart, excluding pure normal modes.
--   - `IsSymplecticMatrix`: PDF p.2, (2)–(3): invertible real symplectic transformation.
--   - `normalDiagonal`: PDF p.2: repeat each normal-mode scalar in both blocks.
--   - `modeEM`: PDF p.2: used only with gamma>1/2, never at a pure mode.
--   - `coth`: PDF p.3: scalar coth, used on positive finite normal parameters.
--   - `CMEM`: PDF pp.2–3, (4),(14): CM and finite EM have a common Williamson chart. Existence from a given covariance is a conclusion, not a premise below.
--   - `HasGaussian`: PDF pp.2,4,6: actual Gaussian density with physical symmetric covariance. The accepted Weyl convention uses doubled covariance, hence 2 • alpha. The explicit symmetry guard avoids the defective frozen moments predicate. Trace class and normalization are provided by State.
--   - `IsGaussianDensity`: PDF p.4, (19): all Gaussian states, including displacements and pure modes.
--   - `gree`: PDF p.4, (19), p.12: extended infimum over all actual separable Gaussian states. It also makes sense for non-Gaussian rho; attainment is separate.
--   - `GaussianBorder`: PDF pp.4–6: separability border relative to physical Gaussian covariances. Every positive covariance neighborhood meets inseparable Gaussian states. Means are fixed because displacements are local; pure covariances are included.
--   - `CenteredGaussianKernel`: PDF p.2, (1),(4): centered Gaussianity on a single complete occupation space. This generic interface also covers matrices before a bipartite regrouping.
--   - `thermalGibbsKernel`: PDF p.2, (1),(4): normalized thermal Gibbs density in the number basis. For positive m its diagonal weights are the normalized exp(-m(k+1/2)) weights. The half-quanta cancel against the reciprocal partition function.
--   - `HasFiniteEM`: PDF pp.2,8, (1),(2): actual finite Gibbs exponential, independently of covariance identities. A bounded metaplectic unitary conjugates the normalized thermal Gibbs density; its action is tested on EVERY bounded Weyl operator. Thus the quadratic exponential is specified spectrally on the completed space, without treating unbounded quadratures as bounded matrices or assuming an entropy formula. The source's EM is S^(-T) diag(m,m) S^(-1).
--   - `GaussianEM`: PDF pp.2–3: the finite covariance chart AND its actual Gibbs meaning. The operator bridge is a conclusion of the conversion theorems, never an additional hypothesis on a supplied Gaussian density. CMEM retains the coordinate relation; this predicate adds its independently specified meaning.
--   - `joinedCoefficients`: PDF p.2: regroup the SAME full bipartite density into one occupation space. No marginal, truncation or new state is chosen.
--   - `Two`: PDF pp.3,8: one oscillator per party, retaining the named A|B cut.
--   - `pairValues`: PDF p.3: two mode values in party order.
--   - `symmetricModeBlock`: PDF pp.3,8: symmetric real two-by-two block [[a,c],[c,b]].
--   - `standardCM`: PDF p.8, (36): ordinary covariance convention, without a factor 1/2.
--   - `symmetricCM`: PDF p.3, (12): half-covariance convention specific to m,kq,kp.
--   - `symmetricSq`: PDF p.3, (13): the symmetric-state block Sq.
--   - `symplecticLift`: PDF p.3: a block symplectic candidate; invertibility is proved in the results.
--   - `symmetricGammas`: PDF p.3, following (14): symplectic eigenvalues, including the pure endpoint.
--   - `emFrom`: PDF p.3, (14): the finite EM constructed from a specified normal chart.
--   - `normalization`: PDF p.4, (17): reciprocal partition function, not the partition function.
--   - `bosonic`: PDF p.5: bosonic entropy in nats, with 0 log 0=0.
--   - `covarianceObjective`: PDF p.4, (18): the finite covariance expression, not the definition of D.
--   - `displacementPenalty`: PDF p.6, (28): the displacement correction with z in the source Weyl convention W(z)=exp(i F^T z). The displaced density mean is -Delta z.
--   - `weylDisplacedDensity`: PDF p.6, (27): the actual W(z) sigma W(z)^* coefficients. The accepted Weyl argument is xi=Delta*z, since W_xi=exp(i xi^T Delta F)=exp(i F^T z).
--   - `hyperbolicMixing`: PDF pp.5,8: two-mode squeezing R(r).
--   - `modeRotation`: PDF p.5, (25): passive rotation, with the source's signs.
--   - `xSqueeze`: PDF pp.7–9: the actual symplectic X(x), with inverse p scalings.
--   - `squeezeBoth`: PDF p.8: a two-mode squeeze acting with opposite r on p.
--   - `rotateBoth`: PDF p.8: the same passive rotation on q and p.
--   - `ySqueeze`: PDF p.7: equal local squeezes Y(y), with y>0 at every use.
--   - `congruence`: PDF p.8: covariance congruence, with its transpose explicit.
--   - `covarianceType`: PDF p.8: the symmetric chart takes precedence over overlapping raw ratios.
--   - `CovSeparable`: PDF pp.8–9: physical Gaussian covariance separability on the actual 1|1 cut.
--   - `CovBorder`: PDF pp.8–9: physical border adjacent to entangled Gaussian states.
--   - `typeICM`: PDF p.8: reverse the type-I diagonalization to construct the covariance.
--   - `typeIICM`: PDF pp.8–9: reverse the type-II diagonalization.
--   - `TypeIIDomain`: PDF p.9, following (38): nontrivial type-II parameter chart.
--   - `borderLeft`: PDF pp.8–9, (37),(38): common left-hand side, with unsquared factor 1/2.
--   - `borderRightI`: PDF p.8, (37): plus sign on the squared-eigenvalue sum.
--   - `borderRightII`: PDF p.9, (38): minus sign on the squared-eigenvalue sum.
--   - `PositiveRoots`: PDF p.9: solve x^2+x^(-2)=K in its positive domain.
--   - `exceptionalDelta`: PDF p.9: delta=(gamma_A^2-1/4)(gamma_B^2-1/4), not a symplectic form.
--   - `exceptionalLower`: PDF p.9: first triangular type-III border Sq.
--   - `exceptionalUpper`: PDF p.9: second triangular type-III border Sq.
--   - `symmetricBorderQ`: PDF p.9, (39): symmetric border Sq in the p.3 normalization.
--   - `borderCMFrom`: PDF p.9: construct a covariance from the displayed Sq and symplectic spectrum.
--   - `symmetricCandidateCM`: PDF pp.9,11, (39),(41): a symmetric border candidate, after the remaining common local squeezing. This is a covariance construction even at pure modes.
--   - `symmetricValue`: PDF p.11, (41): two-variable operator-defined objective, including endpoints. For fixed normal covariances, eliminate y>0 and evaluate actual Umegaki entropy of the explicitly constructed density. Uniqueness of Gaussian characteristic functions means the state variable introduces no extra variational freedom. At gamma=1/2 this definition uses the actual singular density, not Real.log 0, not an assigned scalar limit, and not GREE itself.
--   - `symmetricObjective`: PDF p.11, (41): finite scalar chart of the independent operator objective. The factor 1/2 multiplies the entire square root; coth and tanh each occur as products at half arguments. The state entropy is added separately.
--   - `tmstObjective`: PDF p.11, (42): one-variable objective, with u the positive finite EM normal parameter. This is not used to define the operator divergence or GREE.
--   - `tmstBorderCM`: PDF pp.9,11: a symmetric TMST border with equal normal eigenvalues.
-- source:
--   Gaussian relative entropy of entanglement, arXiv:quant-ph/0402109v3, https://arxiv.org/abs/quant-ph/0402109v3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P47
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P13
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P18
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41

/-!
Chen, arXiv:quant-ph/0402109v3; PDF pages throughout.
Accepted-paper imports follow the independent-paper override. Full oscillator
states have no cutoff. Divergence is independent of covariance formulas.
Covariances are symmetric with vacuum I/2. Pure modes remain in the state space;
CMEM is only a finite chart. HasBipartiteMoments is never used.
Compilation is pending the separate mechanical handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P46

open scoped BigOperators ENNReal ComplexOrder Matrix

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsSeparable)
open QAlgorithms.Papers.Independent.Dependency50.P13
  (finiteRelativeEntropy compression entropyWeight)
open QAlgorithms.Papers.Independent.Claimed50.P47
  (Occupation bipartiteCharacteristic bipartiteWeyl gaussianStateCharacteristic)

-- These accepted definitions have the same completed Hilbert-space meaning.
open QAlgorithms.Papers.Independent.Next46.P13 (coordinateBasis)
open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)
open QAlgorithms.Papers.Independent.Claimed50.P41 (IsDiagonal)

/-- PDF p.4, (16): extended Umegaki entropy in nats via finite orthogonal
compressions of generalized entropy, including its unequal-trace correction.
Infinity on support failure is preserved; no covariance expression defines D. -/
def operatorRelativeEntropy {I : Type} (rho sigma : State I) : ℝ≥0∞ :=
  ⨆ n : ℕ, ⨆ v : {v : Fin n → Hilbert I // Orthonormal ℂ v},
    finiteRelativeEntropy (compression v.val (boundedOperator rho.coefficients))
      (compression v.val (boundedOperator sigma.coefficients))

/-- PDF pp.4–5: independently defined spectral entropy in nats. The continuous
weight -x log x vanishes at zero; the nonnegative trace retains infinity. -/
def densityEntropy {I : Type} (rho : State I) : ℝ≥0∞ := by
  letI : ContinuousFunctionalCalculus ℂ (Hilbert I →L[ℂ] Hilbert I) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus (A := Hilbert I →L[ℂ] Hilbert I)
  letI : ContinuousFunctionalCalculus ℝ (Hilbert I →L[ℂ] Hilbert I) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus (A := Hilbert I →L[ℂ] Hilbert I)
  exact ∑' i, ENNReal.ofReal
    (inner ℂ (coordinateBasis I i)
      ((cfc entropyWeight (boundedOperator rho.coefficients)) (coordinateBasis I i))).re

/-- PDF p.4: unrestricted REE; no energy, rank or Gaussian restriction. -/
def ree {I J : Type} (rho : State (I × J)) : ℝ≥0∞ :=
  ⨅ sigma : {sigma : State (I × J) // IsSeparable sigma.coefficients},
    operatorRelativeEntropy rho sigma.val

/-- PDF p.4: boundary inside normalized states in trace norm. -/
def StateBorder {I J : Type} (sigma : State (I × J)) : Prop :=
  sigma ∈ frontier {tau : State (I × J) | IsSeparable tau.coefficients}

/-- PDF p.2: grouped coordinates, all q before all p. -/
abbrev GroupedPhase (I : Type) := I ⊕ I

/-- PDF p.2: real covariance/exponential arrays, not density operators. -/
abbrev ModeMatrix (I : Type) := Matrix (GroupedPhase I) (GroupedPhase I) ℝ

/-- PDF p.2, (3): grouped canonical form with [q_j,p_k]=i delta_jk. -/
def groupedCCR (I : Type) [Fintype I] : ModeMatrix I := Matrix.fromBlocks 0 1 (-1) 0

/-- PDF p.2: symmetric covariance with alpha-i Delta/2 nonnegative. -/
def IsPhysicalCovariance {I : Type} [Fintype I] (alpha : ModeMatrix I) : Prop :=
  alpha.transpose = alpha ∧
    (alpha.map (fun x : ℝ => (x : ℂ)) -
      (Complex.I / 2) • (groupedCCR I).map (fun x : ℝ => (x : ℂ))).PosSemidef

/-- PDF pp.2–3: finite exponential chart, excluding pure normal modes. -/
def StrictPhysical {I : Type} [Fintype I] (alpha : ModeMatrix I) : Prop :=
  alpha.transpose = alpha ∧
    (alpha.map (fun x : ℝ => (x : ℂ)) -
      (Complex.I / 2) • (groupedCCR I).map (fun x : ℝ => (x : ℂ))).PosDef

/-- PDF p.2, (2)–(3): invertible real symplectic transformation. -/
def IsSymplecticMatrix {I : Type} [Fintype I] (S : ModeMatrix I) : Prop :=
  IsUnit S ∧ S * groupedCCR I * S.transpose = groupedCCR I

/-- PDF p.2: repeat each normal-mode scalar in both blocks. -/
def normalDiagonal {I : Type} [Fintype I] (g : I → ℝ) : ModeMatrix I :=
  Matrix.fromBlocks (Matrix.diagonal g) 0 0 (Matrix.diagonal g)

/-- PDF p.2: used only with gamma>1/2, never at a pure mode. -/
def modeEM (gamma : ℝ) : ℝ := Real.log ((2 * gamma + 1) / (2 * gamma - 1))

/-- PDF p.3: scalar coth, used on positive finite normal parameters. -/
def coth (x : ℝ) : ℝ := Real.cosh x / Real.sinh x

/-- PDF pp.2–3, (4),(14): CM and finite EM have a common Williamson chart.
Existence from a given covariance is a conclusion, not a premise below. -/
def CMEM {I : Type} [Fintype I] (alpha M : ModeMatrix I) : Prop :=
  ∃ (S : ModeMatrix I) (g : I → ℝ), IsSymplecticMatrix S ∧ (∀ j, 1 / 2 < g j) ∧
    alpha = S * normalDiagonal g * S.transpose ∧
    M = S.transpose⁻¹ * normalDiagonal (modeEM ∘ g) * S⁻¹

/-- PDF pp.2,4,6: actual Gaussian density with physical symmetric covariance.
The accepted Weyl convention uses doubled covariance, hence 2 • alpha.
The explicit symmetry guard avoids the defective frozen moments predicate.
Trace class and normalization are provided by State. -/
def HasGaussian {A B : Type} [Fintype A] [Fintype B]
    (rho : State (Occupation A × Occupation B))
    (d : GroupedPhase (A ⊕ B) → ℝ) (alpha : ModeMatrix (A ⊕ B)) : Prop :=
  IsPhysicalCovariance alpha ∧ ∀ xi,
    (∀ u, Summable (fun v => rho.coefficients u v * bipartiteWeyl xi v u)) ∧
    Summable (fun u => ∑' v, rho.coefficients u v * bipartiteWeyl xi v u) ∧
    bipartiteCharacteristic rho.coefficients xi =
      gaussianStateCharacteristic d (2 • alpha) xi

/-- PDF p.4, (19): all Gaussian states, including displacements and pure modes. -/
def IsGaussianDensity {A B : Type} [Fintype A] [Fintype B]
    (rho : State (Occupation A × Occupation B)) : Prop :=
  ∃ d alpha, HasGaussian rho d alpha

/-- PDF p.4, (19), p.12: extended infimum over all actual separable Gaussian
states. It also makes sense for non-Gaussian rho; attainment is separate. -/
def gree {A B : Type} [Fintype A] [Fintype B]
    (rho : State (Occupation A × Occupation B)) : ℝ≥0∞ :=
  ⨅ sigma : {sigma : State (Occupation A × Occupation B) //
      IsSeparable sigma.coefficients ∧ IsGaussianDensity sigma}, operatorRelativeEntropy rho sigma.val

/-- PDF pp.4–6: separability border relative to physical Gaussian covariances.
Every positive covariance neighborhood meets inseparable Gaussian states.
Means are fixed because displacements are local; pure covariances are included. -/
def GaussianBorder {A B : Type} [Fintype A] [Fintype B]
    (sigma : State (Occupation A × Occupation B)) : Prop :=
  IsSeparable sigma.coefficients ∧ ∃ d alpha, HasGaussian sigma d alpha ∧
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ (tau : State (Occupation A × Occupation B)) (beta : ModeMatrix (A ⊕ B)),
        HasGaussian tau d beta ∧ ¬ IsSeparable tau.coefficients ∧
        ∀ i j, |beta i j - alpha i j| < epsilon

/-- PDF p.2, (1),(4): centered Gaussianity on a single complete occupation space.
This generic interface also covers matrices before a bipartite regrouping. -/
def CenteredGaussianKernel {I : Type} [Fintype I]
    (rho : Matrix (Occupation I) (Occupation I) ℂ) (alpha : ModeMatrix I) : Prop :=
  QAlgorithms.Papers.Independent.Dependency50.P33.IsDensity rho ∧ IsPhysicalCovariance alpha ∧
    ∀ xi,
      (∀ u, Summable (fun v => rho u v *
        QAlgorithms.Papers.Independent.Claimed50.P47.weylKernel xi v u)) ∧
      Summable (fun u => ∑' v, rho u v *
        QAlgorithms.Papers.Independent.Claimed50.P47.weylKernel xi v u) ∧
      QAlgorithms.Papers.Independent.Claimed50.P47.singleCharacteristic rho xi =
        gaussianStateCharacteristic 0 (2 • alpha) xi

/-- PDF p.2, (1),(4): normalized thermal Gibbs density in the number basis.
For positive m its diagonal weights are the normalized exp(-m(k+1/2)) weights.
The half-quanta cancel against the reciprocal partition function. -/
def thermalGibbsKernel {I : Type} [Fintype I] (m : I → ℝ) :
    Matrix (Occupation I) (Occupation I) ℂ :=
  fun u v => if u = v then
    ((∏ j, (1 - Real.exp (-m j)) * Real.exp (-m j * (u j : ℝ)) : ℝ) : ℂ)
    else 0

/-- PDF pp.2,8, (1),(2): actual finite Gibbs exponential, independently of
covariance identities. A bounded metaplectic unitary conjugates the normalized
thermal Gibbs density; its action is tested on EVERY bounded Weyl operator.
Thus the quadratic exponential is specified spectrally on the completed space,
without treating unbounded quadratures as bounded matrices or assuming an
entropy formula. The source's EM is S^(-T) diag(m,m) S^(-1). -/
def HasFiniteEM {I : Type} [Fintype I]
    (rho : Matrix (Occupation I) (Occupation I) ℂ) (M : ModeMatrix I) : Prop :=
  QAlgorithms.Papers.Independent.Dependency50.P33.IsDensity rho ∧
    ∃ (S : ModeMatrix I) (m : I → ℝ)
      (U : Hilbert (Occupation I) ≃ₗᵢ[ℂ] Hilbert (Occupation I)),
      IsSymplecticMatrix S ∧ (∀ j, 0 < m j) ∧
      (∀ xi,
        QAlgorithms.Papers.Independent.Frontier30.P14.boundedUnitaryConjugation U.symm
          (QAlgorithms.Papers.Independent.Claimed50.P47.weylKernel xi) =
        QAlgorithms.Papers.Independent.Claimed50.P47.weylKernel
          (QAlgorithms.Papers.Independent.Claimed50.P47.weylPullback S xi)) ∧
      rho = QAlgorithms.Papers.Independent.Frontier30.P14.boundedUnitaryConjugation U
        (thermalGibbsKernel m) ∧
      M = S.transpose⁻¹ * normalDiagonal m * S⁻¹

/-- PDF pp.2–3: the finite covariance chart AND its actual Gibbs meaning.
The operator bridge is a conclusion of the conversion theorems, never an
additional hypothesis on a supplied Gaussian density. CMEM retains the
coordinate relation; this predicate adds its independently specified meaning. -/
def GaussianEM {I : Type} [Fintype I] (alpha M : ModeMatrix I) : Prop :=
  CMEM alpha M ∧ ∀ rho : Matrix (Occupation I) (Occupation I) ℂ,
    CenteredGaussianKernel rho alpha → HasFiniteEM rho M

/-- PDF p.2: regroup the SAME full bipartite density into one occupation space.
No marginal, truncation or new state is chosen. -/
def joinedCoefficients {A B : Type}
    (rho : Matrix (Occupation A × Occupation B) (Occupation A × Occupation B) ℂ) :
    Matrix (Occupation (A ⊕ B)) (Occupation (A ⊕ B)) ℂ :=
  fun u v => rho (u ∘ Sum.inl, u ∘ Sum.inr) (v ∘ Sum.inl, v ∘ Sum.inr)

example {I : Type} [Fintype I] (m : I → ℝ) (u v : Occupation I) (h : u ≠ v) :
    thermalGibbsKernel m u v = 0 := by simp [thermalGibbsKernel, h]

example {I : Type} [Fintype I] (m : I → ℝ) :
    thermalGibbsKernel m (fun _ => 0) (fun _ => 0) =
      ((∏ j, (1 - Real.exp (-m j)) : ℝ) : ℂ) := by
  simp [thermalGibbsKernel]

example {I : Type} : operatorCoeff (0 : Hilbert I →L[ℂ] Hilbert I) = 0 := by
  ext i j
  simp [operatorCoeff]

example : entropyWeight 0 = 0 := by simp [entropyWeight]

example {I : Type} [Fintype I] (g : I → ℝ) (i : I) :
    normalDiagonal g (Sum.inl i) (Sum.inr i) = 0 := by
  simp [normalDiagonal]

example {I : Type} [Fintype I] (i : I) : groupedCCR I (Sum.inl i) (Sum.inr i) = 1 := by
  simp [groupedCCR]

/-- PDF pp.3,8: one oscillator per party, retaining the named A|B cut. -/
abbrev Two := Fin 1 ⊕ Fin 1

/-- PDF p.3: two mode values in party order. -/
def pairValues (a b : ℝ) : Two → ℝ := Sum.elim (fun _ => a) (fun _ => b)

/-- PDF pp.3,8: symmetric real two-by-two block [[a,c],[c,b]]. -/
def symmetricModeBlock (a c b : ℝ) : Matrix Two Two ℝ
  | Sum.inl _, Sum.inl _ => a
  | Sum.inl _, Sum.inr _ => c
  | Sum.inr _, Sum.inl _ => c
  | Sum.inr _, Sum.inr _ => b

/-- PDF p.8, (36): ordinary covariance convention, without a factor 1/2. -/
def standardCM (a b c1 c2 : ℝ) : ModeMatrix Two :=
  Matrix.fromBlocks (symmetricModeBlock a c1 b) 0 0 (symmetricModeBlock a (-c2) b)

/-- PDF p.3, (12): half-covariance convention specific to m,kq,kp. -/
def symmetricCM (m kq kp : ℝ) : ModeMatrix Two :=
  standardCM (m / 2) (m / 2) (kq / 2) (kp / 2)

/-- PDF p.3, (13): the symmetric-state block Sq. -/
def symmetricSq (m kq kp : ℝ) : Matrix Two Two ℝ :=
  (Real.sqrt 2)⁻¹ • (symmetricModeBlock 1 1 (-1) * Matrix.diagonal
    (pairValues (Real.rpow ((m + kq) / (m - kp)) (1 / 4))
      (Real.rpow ((m - kq) / (m + kp)) (1 / 4))))

/-- PDF p.3: a block symplectic candidate; invertibility is proved in the results. -/
def symplecticLift (Sq : Matrix Two Two ℝ) : ModeMatrix Two :=
  Matrix.fromBlocks Sq 0 0 Sq.transpose⁻¹

/-- PDF p.3, following (14): symplectic eigenvalues, including the pure endpoint. -/
def symmetricGammas (m kq kp : ℝ) : Two → ℝ :=
  pairValues (Real.sqrt ((m + kq) * (m - kp)) / 2)
    (Real.sqrt ((m - kq) * (m + kp)) / 2)

/-- PDF p.3, (14): the finite EM constructed from a specified normal chart. -/
def emFrom {I : Type} [Fintype I] (S : ModeMatrix I) (g : I → ℝ) : ModeMatrix I :=
  S.transpose⁻¹ * normalDiagonal (modeEM ∘ g) * S⁻¹

example : symmetricModeBlock 1 0 1 = (1 : Matrix Two Two ℝ) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;> simp [symmetricModeBlock]

example (m kq kp : ℝ) :
    symmetricCM m kq kp (Sum.inl (Sum.inl 0)) (Sum.inl (Sum.inr 0)) = kq / 2 := rfl

/-- PDF p.4, (17): reciprocal partition function, not the partition function. -/
def normalization {I : Type} [Fintype I] (g : I → ℝ) : ℝ :=
  ∏ j, 2 * Real.sinh (modeEM (g j) / 2)

/-- PDF p.5: bosonic entropy in nats, with 0 log 0=0. -/
def bosonic (x : ℝ) : ℝ := (x + 1) * Real.log (x + 1) - x * Real.log x

/-- PDF p.4, (18): the finite covariance expression, not the definition of D. -/
def covarianceObjective {I : Type} [Fintype I]
    (alpha M : ModeMatrix I) (c : ℝ) : ℝ := -Real.log c + (alpha * M).trace / 2

example : bosonic 0 = 0 := by simp [bosonic]

/-- PDF p.6, (28): the displacement correction with z in the source Weyl
convention W(z)=exp(i F^T z). The displaced density mean is -Delta z. -/
def displacementPenalty {I : Type} [Fintype I]
    (M : ModeMatrix I) (z : GroupedPhase I → ℝ) : ℝ :=
  (∑ i, ∑ j, (groupedCCR I).mulVec z i * M i j * (groupedCCR I).mulVec z j) / 2

example {I : Type} [Fintype I] (M : ModeMatrix I) : displacementPenalty M 0 = 0 := by
  simp [displacementPenalty]

/-- PDF p.6, (27): the actual W(z) sigma W(z)^* coefficients. The accepted
Weyl argument is xi=Delta*z, since W_xi=exp(i xi^T Delta F)=exp(i F^T z). -/
def weylDisplacedDensity {A B : Type} [Fintype A] [Fintype B]
    (sigma : State (Occupation A × Occupation B)) (z : GroupedPhase (A ⊕ B) → ℝ) :
    Matrix (Occupation A × Occupation B) (Occupation A × Occupation B) ℂ :=
  QAlgorithms.Papers.Independent.Frontier30.P14.conjugateKernel
    (bipartiteWeyl ((groupedCCR (A ⊕ B)).mulVec z)) sigma.coefficients

/-- PDF pp.5,8: two-mode squeezing R(r). -/
def hyperbolicMixing (r : ℝ) : Matrix Two Two ℝ :=
  symmetricModeBlock (Real.cosh r) (Real.sinh r) (Real.cosh r)

/-- PDF p.5, (25): passive rotation, with the source's signs. -/
def modeRotation (t : ℝ) : Matrix Two Two ℝ
  | Sum.inl _, Sum.inl _ => Real.cos t
  | Sum.inl _, Sum.inr _ => Real.sin t
  | Sum.inr _, Sum.inl _ => -Real.sin t
  | Sum.inr _, Sum.inr _ => Real.cos t

/-- PDF pp.7–9: the actual symplectic X(x), with inverse p scalings. -/
def xSqueeze (x : ℝ) : ModeMatrix Two :=
  Matrix.fromBlocks (Matrix.diagonal (pairValues (Real.sqrt x) ((Real.sqrt x)⁻¹))) 0 0
    (Matrix.diagonal (pairValues ((Real.sqrt x)⁻¹) (Real.sqrt x)))

/-- PDF p.8: a two-mode squeeze acting with opposite r on p. -/
def squeezeBoth (r : ℝ) : ModeMatrix Two := Matrix.fromBlocks (hyperbolicMixing r) 0 0 (hyperbolicMixing (-r))

/-- PDF p.8: the same passive rotation on q and p. -/
def rotateBoth (t : ℝ) : ModeMatrix Two := Matrix.fromBlocks (modeRotation t) 0 0 (modeRotation t)

/-- PDF p.7: equal local squeezes Y(y), with y>0 at every use. -/
def ySqueeze (y : ℝ) : ModeMatrix Two :=
  Matrix.fromBlocks ((Real.sqrt y) • (1 : Matrix Two Two ℝ)) 0 0
    ((Real.sqrt y)⁻¹ • (1 : Matrix Two Two ℝ))

/-- PDF p.8: covariance congruence, with its transpose explicit. -/
def congruence (S alpha : ModeMatrix Two) : ModeMatrix Two := S * alpha * S.transpose

/-- PDF p.8: the symmetric chart takes precedence over overlapping raw ratios. -/
def covarianceType (a b c1 c2 : ℝ) : ℕ :=
  if a = b then 4 else if c1 / c2 + c2 / c1 < a / b + b / a then 1
  else if a / b + b / a < c1 / c2 + c2 / c1 then 2 else 3

example (a c1 c2 : ℝ) : covarianceType a a c1 c2 = 4 := by
  simp [covarianceType]

example : modeRotation 0 = (1 : Matrix Two Two ℝ) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;> simp [modeRotation]

/-- PDF pp.8–9: physical Gaussian covariance separability on the actual 1|1 cut. -/
def CovSeparable (alpha : ModeMatrix Two) : Prop :=
  ∃ sigma : State (Occupation (Fin 1) × Occupation (Fin 1)),
    HasGaussian sigma 0 alpha ∧ IsSeparable sigma.coefficients

/-- PDF pp.8–9: physical border adjacent to entangled Gaussian states. -/
def CovBorder (alpha : ModeMatrix Two) : Prop :=
  ∃ sigma : State (Occupation (Fin 1) × Occupation (Fin 1)),
    HasGaussian sigma 0 alpha ∧ GaussianBorder sigma

/-- PDF p.8: reverse the type-I diagonalization to construct the covariance. -/
def typeICM (gA gB r x : ℝ) : ModeMatrix Two :=
  congruence (squeezeBoth (-r) * xSqueeze x⁻¹) (normalDiagonal (pairValues gA gB))

/-- PDF pp.8–9: reverse the type-II diagonalization. -/
def typeIICM (gA gB t x : ℝ) : ModeMatrix Two :=
  congruence (rotateBoth (-t) * xSqueeze x⁻¹) (normalDiagonal (pairValues gA gB))

/-- PDF p.9, following (38): nontrivial type-II parameter chart. -/
def TypeIIDomain (gA gB x : ℝ) : Prop :=
  0 < x ∧ (max (Real.sqrt (gA / gB)) (Real.sqrt (gB / gA)) < x ∨
    x < min (Real.sqrt (gA / gB)) (Real.sqrt (gB / gA)))

/-- PDF pp.8–9, (37),(38): common left-hand side, with unsquared factor 1/2. -/
def borderLeft (gA gB : ℝ) : ℝ := (2 * gA ^ 2 - 1 / 2) * (2 * gB ^ 2 - 1 / 2)

/-- PDF p.8, (37): plus sign on the squared-eigenvalue sum. -/
def borderRightI (gA gB r x : ℝ) : ℝ :=
  Real.sinh (2 * r) ^ 2 * ((x ^ 2 + (x⁻¹) ^ 2) * gA * gB + (gA ^ 2 + gB ^ 2))

/-- PDF p.9, (38): minus sign on the squared-eigenvalue sum. -/
def borderRightII (gA gB t x : ℝ) : ℝ :=
  Real.sin (2 * t) ^ 2 * ((x ^ 2 + (x⁻¹) ^ 2) * gA * gB - (gA ^ 2 + gB ^ 2))

/-- PDF p.9: solve x^2+x^(-2)=K in its positive domain. -/
def PositiveRoots (K x : ℝ) : Prop :=
  2 ≤ K ∧ (x = Real.sqrt ((K + Real.sqrt (K ^ 2 - 4)) / 2) ∨
    x = Real.sqrt ((K - Real.sqrt (K ^ 2 - 4)) / 2))

example (gA gB x : ℝ) : borderRightI gA gB 0 x = 0 := by
  simp [borderRightI]

/-- PDF p.9: delta=(gamma_A^2-1/4)(gamma_B^2-1/4), not a symplectic form. -/
def exceptionalDelta (gA gB : ℝ) : ℝ := (gA ^ 2 - 1 / 4) * (gB ^ 2 - 1 / 4)

/-- PDF p.9: first triangular type-III border Sq. -/
def exceptionalLower (gA gB : ℝ) : Matrix Two Two ℝ :=
  let d := exceptionalDelta gA gB
  fun i j => match i, j with
    | Sum.inl _, Sum.inl _ => Real.rpow (1 + d / gA ^ 2) (1 / 4)
    | Sum.inl _, Sum.inr _ => 0
    | Sum.inr _, Sum.inl _ => Real.rpow (d ^ 2 / (gA ^ 2 * (gB ^ 2 + d))) (1 / 4)
    | Sum.inr _, Sum.inr _ => Real.rpow (gB ^ 2 / (gB ^ 2 + d)) (1 / 4)

/-- PDF p.9: second triangular type-III border Sq. -/
def exceptionalUpper (gA gB : ℝ) : Matrix Two Two ℝ :=
  let d := exceptionalDelta gA gB
  fun i j => match i, j with
    | Sum.inl _, Sum.inl _ => Real.rpow (gA ^ 2 / (gA ^ 2 + d)) (1 / 4)
    | Sum.inl _, Sum.inr _ => Real.rpow (d ^ 2 / (gB ^ 2 * (gA ^ 2 + d))) (1 / 4)
    | Sum.inr _, Sum.inl _ => 0
    | Sum.inr _, Sum.inr _ => Real.rpow (1 + d / gB ^ 2) (1 / 4)

/-- PDF p.9, (39): symmetric border Sq in the p.3 normalization. -/
def symmetricBorderQ (gA gB : ℝ) : Matrix Two Two ℝ :=
  (Real.sqrt 2)⁻¹ • (symmetricModeBlock 1 1 (-1) * Matrix.diagonal (pairValues
    (Real.rpow (4 * gA ^ 2 * (4 * gB ^ 2 + 1) / (4 * gA ^ 2 + 1)) (1 / 4))
    (Real.rpow ((4 * gB ^ 2 + 1) / (4 * gB ^ 2 * (4 * gA ^ 2 + 1))) (1 / 4))))

/-- PDF p.9: construct a covariance from the displayed Sq and symplectic spectrum. -/
def borderCMFrom (Sq : Matrix Two Two ℝ) (gA gB : ℝ) : ModeMatrix Two :=
  congruence (symplecticLift Sq) (normalDiagonal (pairValues gA gB))

example : exceptionalDelta (1 / 2) (1 / 2) = 0 := by
  norm_num [exceptionalDelta]

/-- PDF pp.9,11, (39),(41): a symmetric border candidate, after the remaining
common local squeezing. This is a covariance construction even at pure modes. -/
def symmetricCandidateCM (gA gB y : ℝ) : ModeMatrix Two :=
  congruence (ySqueeze y⁻¹) (borderCMFrom (symmetricBorderQ gA gB) gA gB)

/-- PDF p.11, (41): two-variable operator-defined objective, including endpoints.
For fixed normal covariances, eliminate y>0 and evaluate actual Umegaki entropy
of the explicitly constructed density. Uniqueness of Gaussian characteristic
functions means the state variable introduces no extra variational freedom.
At gamma=1/2 this definition uses the actual singular density, not Real.log 0,
not an assigned scalar limit, and not GREE itself. -/
def symmetricValue
    (rho : State (Occupation (Fin 1) × Occupation (Fin 1))) (gA gB : ℝ) : ℝ≥0∞ :=
  ⨅ candidate : {p : ℝ × State (Occupation (Fin 1) × Occupation (Fin 1)) //
      0 < p.1 ∧ HasGaussian p.2 0 (symmetricCandidateCM gA gB p.1)},
    operatorRelativeEntropy rho candidate.val.2

/-- PDF p.11, (41): finite scalar chart of the independent operator objective.
The factor 1/2 multiplies the entire square root; coth and tanh each occur as
products at half arguments. The state entropy is added separately. -/
def symmetricObjective (m kq kp u v : ℝ) : ℝ :=
  -Real.log (2 * Real.sinh (u / 2)) - Real.log (2 * Real.sinh (v / 2)) +
    Real.sqrt ((m + kq) * (m - kp) * u ^ 2 +
      (m - kq) * (m + kp) * v ^ 2 +
      (m - kq) * (m - kp) * u * v * coth (u / 2) * coth (v / 2) +
      (m + kq) * (m + kp) * u * v * Real.tanh (u / 2) * Real.tanh (v / 2)) / 2

example : ySqueeze 1 = (1 : ModeMatrix Two) := by
  simpa only [ySqueeze, Real.sqrt_one, inv_one, one_smul] using
    (Matrix.fromBlocks_one :
      Matrix.fromBlocks (1 : Matrix Two Two ℝ) 0 0 (1 : Matrix Two Two ℝ) = 1)

/-- PDF p.11, (42): one-variable objective, with u the positive finite EM
normal parameter. This is not used to define the operator divergence or GREE. -/
def tmstObjective (m k u : ℝ) : ℝ :=
  -2 * Real.log (2 * Real.sinh (u / 2)) +
    u / 2 * ((m - k) * coth (u / 2) + (m + k) * Real.tanh (u / 2))

/-- PDF pp.9,11: a symmetric TMST border with equal normal eigenvalues. -/
def tmstBorderCM (u : ℝ) : ModeMatrix Two :=
  let g := coth (u / 2) / 2
  symmetricCM (2 * g ^ 2 + 1 / 2) (2 * g ^ 2 - 1 / 2) (2 * g ^ 2 - 1 / 2)

end QAlgorithms.Papers.Independent.Intakenext100.P46


