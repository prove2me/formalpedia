-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P05
-- name    : QAlgorithms_Papers_Independent_Bridge50_P05
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T11:58:10.429849+00:00
-- url     : https://prove2.me/theorems/6d584c0a-a61c-45a8-b59e-5e606e02af80
-- title:
--   Definitions for On Weyl-covariant channels
-- statement:
--   The objects the formalized statements of *On Weyl-covariant channels* (arXiv:quant-ph/0510148) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `W`: PDF p.2: the source's forward-shift, positive-clock Weyl operator.
--   - `rotateWeylLabel`: PDF p.2: J(x,y)=(y,-x).
--   - `duality`: PDF p.2: positive ordinary duality character, arithmetic modulo d.
--   - `residueSymplectic`: PDF pp.2,7: alternating pairing in ZMod d, not a chosen real representative.
--   - `weylFourierCoefficient`: PDF pp.2--3: f_X(z)=Tr(X W_z*)/d.
--   - `WeylCovariantMap`: PDF pp.3--4: Weyl covariance on every operator of a complex-linear map.
--   - `NormalizedWeylMap`: PDF p.4: W1 consists of normalized covariant linear maps; CP is not required.
--   - `symbol`: PDF p.4: the map's symbol is computed from its action, never supplied freely.
--   - `multiplier`: PDF p.4: the complex multiplier on the entire Weyl expansion.
--   - `fourier`: PDF p.4: positive-sign Fourier transform, without a probability restriction.
--   - `weylConvolution`: PDF p.4: convolution on the finite additive phase space.
--   - `maxSq`: PDF pp.4,6: finite squared maximum. Its explicitly disclosed d=1 value is zero. For d>1, inserting zero does not change the maximum of nonnegative squared moduli.
--   - `optimizers`: PDF p.6: the set of maximizing NONZERO Weyl labels.
--   - `saturationValue`: PDF p.5, (2.7): the saturation value, with both square roots retained.
--   - `eigenSet`: PDF p.6: G_psi is computed from a vector; unit normalization is a theorem premise.
--   - `Degenerate`: PDF p.7: pairwise degeneracy modulo d, valid also for the empty set.
--   - `MaximalDegenerate`: PDF p.7: inclusion maximality among degenerate subsets, with actual subgroup data. Cardinality d is derived by the geometry result rather than built into this predicate.
--   - `annihilator`: PDF p.8: annihilator for the ordinary duality form.
--   - `twoSymbol`: PDF p.8, (2.13): complex two-parameter symbol; normalization is explicit.
--   - `subgroupTwirl`: PDF p.9, (2.18): the sum is over the ordinary annihilator G-perp.
--   - `maximallyMixedReplacement`: PDF p.8: the completely depolarizing term, extended linearly to all operators.
--   - `complexDepolarizing`: PDF p.8: the complex-parameter depolarizing map, without a CP restriction.
--   - `twoMap`: PDF p.8, (2.17): the two-parameter family for its computed subgroup twirl.
--   - `HermiticityPreserving`: PDF p.7: Hermitian means Hermiticity preserving, not superoperator self-adjointness.
--   - `channelTriangle`: PDF p.10 and Figure p.14: the CLOSED real parameter triangle; used only for d>=2.
--   - `diagonalBlock`: PDF p.12: D_s in cyclic source order r=1,...,d, with d representing residue zero.
--   - `complementBlock`: PDF pp.12--13: concatenated d complementary Kraus blocks, of size d² by d². Column block t has Weyl factor U^(1-t)V^(1-s), retaining all phases.
--   - `reorderedKraus`: PDF pp.11--12: reorder actual Kraus operators by environment (s,r), corresponding to x=1-r,y=1-s. Nonnegative lambda is the canonical square root.
-- source:
--   On Weyl-covariant channels, arXiv:quant-ph/0510148v3, https://arxiv.org/abs/quant-ph/0510148v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P36
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

/-! Fukuda--Holevo, arXiv:quant-ph/0510148v3. All locators are PDF pages.
The independent-paper override permits imports from the pinned accepted library.
New definitions are confined to this namespace. The two false printed claims are
recorded in HARD.md. Compilation is pending the batch handoff. -/

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P05

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal
open QAlgorithms.Papers.Independent.Information100.P34 (cyclicPhase weyl dephasing)
open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)
open QAlgorithms.Papers.Independent.Gap48.P36 (WeylLabel)
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)
open QAlgorithms.Papers.Independent.Claimed50.P48
  (nu superopTensor UniversalMultiplicative rowKraus indexedKrausDilation)
open QAlgorithms.Papers.Independent.Information100.P67 (complementaryChannel)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {d : ℕ} [NeZero d]

/-- PDF p.2: the source's forward-shift, positive-clock Weyl operator. -/
def W (z : WeylLabel d) : Op (ZMod d) := weyl z.1 z.2

/-- PDF p.2: J(x,y)=(y,-x). -/
def rotateWeylLabel (z : WeylLabel d) : WeylLabel d := (z.2, -z.1)

/-- PDF p.2: positive ordinary duality character, arithmetic modulo d. -/
def duality (g z : WeylLabel d) : ℂ := cyclicPhase d (g.1 * z.1 + g.2 * z.2)

/-- PDF pp.2,7: alternating pairing in ZMod d, not a chosen real representative. -/
def residueSymplectic (u v : WeylLabel d) : ZMod d := u.1 * v.2 - u.2 * v.1

/-- PDF pp.2--3: f_X(z)=Tr(X W_z*)/d. -/
def weylFourierCoefficient (X : Op (ZMod d)) (z : WeylLabel d) : ℂ := (X * (W z)ᴴ).trace / (d : ℂ)

/-- PDF pp.3--4: Weyl covariance on every operator of a complex-linear map. -/
def WeylCovariantMap (Phi : Op (ZMod d) →ₗ[ℂ] Op (ZMod d)) : Prop :=
  ∀ z X, Phi (W z * X * (W z)ᴴ) = W z * Phi X * (W z)ᴴ

/-- PDF p.4: W1 consists of normalized covariant linear maps; CP is not required. -/
def NormalizedWeylMap (Phi : Op (ZMod d) →ₗ[ℂ] Op (ZMod d)) : Prop := WeylCovariantMap Phi ∧ Phi 1 = 1

/-- PDF p.4: the map's symbol is computed from its action, never supplied freely. -/
def symbol (Phi : Superop (ZMod d) (ZMod d)) (z : WeylLabel d) : ℂ :=
  weylFourierCoefficient (Phi (W z)) z

/-- PDF p.4: the complex multiplier on the entire Weyl expansion. -/
def multiplier (phi : WeylLabel d → ℂ) : Superop (ZMod d) (ZMod d) :=
  fun X => ∑ z, (weylFourierCoefficient X z * phi z) • W z

/-- PDF p.4: positive-sign Fourier transform, without a probability restriction. -/
def fourier (phi : WeylLabel d → ℂ) (g : WeylLabel d) : ℂ :=
  (d : ℂ)⁻¹ ^ 2 * ∑ z, phi z * duality g z

/-- PDF p.4: convolution on the finite additive phase space. -/
def weylConvolution (p q : WeylLabel d → ℂ) (g : WeylLabel d) : ℂ := ∑ h, p h * q (g - h)

/-- PDF pp.4,6: finite squared maximum. Its explicitly disclosed d=1 value is zero.
For d>1, inserting zero does not change the maximum of nonnegative squared moduli. -/
def maxSq (phi : WeylLabel d → ℂ) : ℝ :=
  if d = 1 then 0 else
    ((Finset.univ.sup fun z : WeylLabel d =>
      if z = 0 then (0 : NNReal) else (⟨‖phi z‖ ^ 2, sq_nonneg _⟩ : NNReal)) : NNReal)

/-- PDF p.6: the set of maximizing NONZERO Weyl labels. -/
def optimizers (phi : WeylLabel d → ℂ) : Set (WeylLabel d) :=
  {z | z ≠ 0 ∧ ‖phi z‖ ^ 2 = maxSq phi}

/-- PDF p.5, (2.7): the saturation value, with both square roots retained. -/
def saturationValue (phi : WeylLabel d → ℂ) : ℝ :=
  (Real.sqrt d)⁻¹ * Real.sqrt (1 + ((d : ℝ) - 1) * maxSq phi)

/-- PDF p.6: G_psi is computed from a vector; unit normalization is a theorem premise. -/
def eigenSet (psi : EuclideanSpace ℂ (ZMod d)) : Set (WeylLabel d) :=
  {z | ∃ c : ℂ, act (W z) psi = c • psi}

/-- PDF p.7: pairwise degeneracy modulo d, valid also for the empty set. -/
def Degenerate (F : Set (WeylLabel d)) : Prop :=
  ∀ u ∈ F, ∀ v ∈ F, residueSymplectic u v = 0

/-- PDF p.7: inclusion maximality among degenerate subsets, with actual subgroup data.
Cardinality d is derived by the geometry result rather than built into this predicate. -/
def MaximalDegenerate (G : AddSubgroup (WeylLabel d)) : Prop :=
  Degenerate (G : Set (WeylLabel d)) ∧
    ∀ F : Set (WeylLabel d), Degenerate F → (G : Set (WeylLabel d)) ⊆ F → F ⊆ G

/-- PDF p.8: annihilator for the ordinary duality form. -/
def annihilator (G : AddSubgroup (WeylLabel d)) : Set (WeylLabel d) :=
  {g | ∀ z ∈ G, g.1 * z.1 + g.2 * z.2 = 0}

/-- PDF p.8, (2.13): complex two-parameter symbol; normalization is explicit. -/
def twoSymbol (G : AddSubgroup (WeylLabel d)) (a b : ℂ) (z : WeylLabel d) : ℂ :=
  if z = 0 then 1 else if z ∈ G then a + b else b

/-- PDF p.9, (2.18): the sum is over the ordinary annihilator G-perp. -/
def subgroupTwirl (G : AddSubgroup (WeylLabel d)) : Superop (ZMod d) (ZMod d) :=
  fun X => (d : ℂ)⁻¹ • ∑ z ∈ Finset.univ.filter (fun z => z ∈ annihilator G),
    W (rotateWeylLabel z) * X * (W (rotateWeylLabel z))ᴴ

/-- PDF p.8: the completely depolarizing term, extended linearly to all operators. -/
def maximallyMixedReplacement (X : Op (ZMod d)) : Op (ZMod d) := (X.trace / (d : ℂ)) • 1

/-- PDF p.8: the complex-parameter depolarizing map, without a CP restriction. -/
def complexDepolarizing (lam : ℂ) : Superop (ZMod d) (ZMod d) :=
  fun X => lam • X + (1 - lam) • maximallyMixedReplacement X

/-- PDF p.8, (2.17): the two-parameter family for its computed subgroup twirl. -/
def twoMap (G : AddSubgroup (WeylLabel d)) (a b : ℂ) : Superop (ZMod d) (ZMod d) :=
  fun X => a • subgroupTwirl G X + b • X + (1 - a - b) • maximallyMixedReplacement X

/-- PDF p.7: Hermitian means Hermiticity preserving, not superoperator self-adjointness. -/
def HermiticityPreserving (Phi : Op (ZMod d) →ₗ[ℂ] Op (ZMod d)) : Prop :=
  ∀ X, X.IsHermitian → (Phi X).IsHermitian

/-- PDF p.10 and Figure p.14: the CLOSED real parameter triangle; used only for d>=2. -/
def channelTriangle (d : ℕ) : Set (ℝ × ℝ) :=
  convexHull ℝ {((0 : ℝ), (1 : ℝ)), (-1 / ((d : ℝ) - 1), 0),
    ((d : ℝ) / ((d : ℝ) - 1), -1 / ((d : ℝ) - 1))}

/-- PDF p.12: D_s in cyclic source order r=1,...,d, with d representing residue zero. -/
def diagonalBlock (lam : WeylLabel d → ℝ) (s : ZMod d) : Op (ZMod d) :=
  Matrix.diagonal fun r => (lam (1 - r, 1 - s) : ℂ)

/-- PDF pp.12--13: concatenated d complementary Kraus blocks, of size d² by d².
Column block t has Weyl factor U^(1-t)V^(1-s), retaining all phases. -/
def complementBlock (lam : WeylLabel d → ℝ) : Matrix (WeylLabel d) (WeylLabel d) ℂ :=
  fun sr tu =>
    let M : Op (ZMod d) := diagonalBlock lam sr.1 * W (1 - tu.1, 1 - sr.1)
    M sr.2 tu.2

/-- PDF pp.11--12: reorder actual Kraus operators by environment (s,r),
corresponding to x=1-r,y=1-s. Nonnegative lambda is the canonical square root. -/
def reorderedKraus (lam : WeylLabel d → ℝ) (sr : WeylLabel d) : Op (ZMod d) :=
  (lam (1 - sr.2, 1 - sr.1) : ℂ) • W (1 - sr.2, 1 - sr.1)

/-- Sanity checks: J has square minus identity and the d=1 maximum is explicit. -/
example (z : WeylLabel d) : rotateWeylLabel (rotateWeylLabel z) = -z := by
  apply Prod.ext <;> simp [rotateWeylLabel]

example (phi : WeylLabel 1 → ℂ) : maxSq phi = 0 := by simp [maxSq]

example (G : AddSubgroup (WeylLabel d)) (a b : ℂ) : twoSymbol G a b 0 = 1 := by
  simp [twoSymbol]

example (lam : WeylLabel d → ℝ) (s r : ZMod d) :
    diagonalBlock lam s r r = (lam (1 - r, 1 - s) : ℂ) := by
  simp [diagonalBlock]

end QAlgorithms.Papers.Independent.Bridge50.P05


