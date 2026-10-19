-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44
-- name    : QAlgorithms_Papers_Independent_Information100_P44
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T11:26:24.919861+00:00
-- url     : https://prove2.me/theorems/ef50a9b8-4d25-4b13-8824-b58dfbcd8d77
-- title:
--   Definitions for Limitations on Joint Coherence Transfer in Quantum Thermodynamics
-- statement:
--   The objects the formalized statements of *Limitations on Joint Coherence Transfer in Quantum Thermodynamics* (arXiv:2608.11872) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Mat`
--   - `Map`
--   - `matrixUnit`: PDF p.6: the matrix unit |i><j|.
--   - `IsTracePreserving`: PDF pp.4,6: trace preservation on all operators.
--   - `IsComplexLinear`: PDF p.15: complex linearity of a map, including maps not assumed CP.
--   - `krausVector`: PDF p.6, Eq.(25): unnormalized Kraus–Gram vector.
--   - `population`: PDF pp.4,6: basis-state transition weight (not an energy-level population).
--   - `Collinear`: PDF p.6: complex collinearity; equality characterizations separately require nonzero vectors.
--   - `gibbsWeight`: PDF p.4: normalized Gibbs weight per basis state at a finite real inverse temperature.
--   - `gibbsDensity`: PDF p.4, Eq.(8): diagonal Gibbs density. Only used on nonzero systems.
--   - `timeEvolution`: PDF p.4, Eq.(7): e^{-itH} X e^{itH} in the fixed energy eigenbasis.
--   - `IsCovariant`: PDF p.4: time-translation covariance on every operator.
--   - `IsCGP`: PDF p.4: covariant Gibbs-preserving CPTP map.
--   - `ThermalDilation`: PDF pp.4,7: one finite nonempty bath and one common energy-preserving unitary.
--   - `thermalKraus`: PDF p.7, Eq.(33): Kraus index is the ordered bath input-output pair (mu,nu).
--   - `thermalApply`: PDF p.4, Eq.(5), via its explicit Kraus family in Eq.(33).
--   - `shellVector`: PDF p.7, Eq.(38): zero-padded coordinates in one common bath-pair Hilbert space.
--   - `IsFiniteThermal`: PDF p.4: TO means finite-bath TO, with no topological closure.
--   - `contributors`: PDF p.10, Eq.(64): exactly the nonzero contributing pairs.
--   - `modeBound`: PDF p.10, Eq.(65): the mode-transport upper bound, omitting only vanishing terms.
--   - `TransferEdges`
--   - `JointElementary`: PDF pp.10–11: a selected elementary bound connects transitions (r,i) and (s,j).
--   - `saturationAdj`: PDF pp.10–11: graph vertices exclude zero vectors; edges are undirected selected pairs.
--   - `PopulationTask`: PDF pp.6,16: only total energy-eigenspace populations are constrained.
--   - `energyBlock`: PDF p.11: a rectangular coherence block, with the L2 operator norm used below.
--   - `choi`: PDF p.16, Eq.(117): output-first, unnormalized Choi matrix.
--   - `fromChoi`: PDF p.16, Eq.(117): reconstruction has no transpose or conjugation of the input.
--   - `fixedEnergy`: PDF pp.15–16: fixed energies in order (0,1a,1b,3).
--   - `fixedRho`: PDF p.16, Eq.(111): exact rational input matrix, not rounded eigenvalues.
--   - `FixedPopulations`: PDF pp.16–17, Eqs.(114)–(116): the middle basis populations are not fixed separately.
--   - `FixedChannelFeasible`: PDF p.16, Eq.(113): the concrete CGP channel feasible set.
--   - `FixedChoiFeasible`: PDF pp.16–17, Eqs.(118)–(121): exact Choi SDP feasible set.
--   - `objectivePair`: PDF pp.17–18: three signed real directional objectives in the specified order.
--   - `channelObjective`: PDF p.17: directional witness on channels.
--   - `cgpOptimum`: PDF p.18, Eq.(128): fixed CGP optima. Nonemptiness and boundedness follow from the source's Lemma 3 and Remark 7 and are conclusions below, not additional hypotheses.
--   - `cgpSumOptimum`: PDF p.18, Eq.(129): optimize the sum over one common channel.
--   - `FixedTOFeasible`: PDF p.19: finite-TO feasibility; its nonemptiness is not assumed.
--   - `toOptimum`: PDF p.19, Eq.(138): extended-real supremum, equal to minus infinity if infeasible.
--   - `toSumOptimum`: PDF p.19, Eq.(139): optimize the summed witness over finite baths.
--   - `signMatrix`: PDF p.20: U_minus = diag(1,1,-1); U_plus is the identity.
--   - `directionalMixture`: PDF p.20, Proposition 3: the displayed random-unitary channel on all operators.
--   - `shortModeMatrix`: PDF p.20: actual coefficients of the map on span{|0><1|,|0><2|}.
--   - `mixtureBathGap`: PDF p.20, Remark 11: the nonnegative bath gap, including zero at q=1/2.
--   - `mixtureBathUnitary`: PDF p.20, Remark 11: the controlled unitary, with control labels swapped for q<1/2.
--   - `augment`: PDF p.21: append two rectangular matrices horizontally.
--   - `ladderGram`: PDF pp.21,23, Eqs.(148),(157): the one common (g,g,1) Gram block.
--   - `gramSelector`: PDF p.21: combine the two directional selectors with the scalar selector.
--   - `frustration`: PDF p.22, Eq.(152): the fixed scalar phase-frustration matrix.
--   - `frustrationEmbedding`: PDF p.22: (g,g,1) zero extension along two selected rays.
--   - `commonGram`: PDF p.22, Eq.(153): all coupling blocks share the same leading corner.
--   - `AllMinorsZero`: PDF pp.22–24: vanishing of all k-by-k minors, with no repeated rows or columns.
--   - `angularDirection`: PDF p.24, Eq.(161): the chosen nonzero angular direction.
--   - `alignmentPolynomial`: PDF pp.24–25, Eq.(162): the determinant polynomial in vector entries.
--   - `angularDeterminant`: PDF pp.24–25: angular substitution in the determinant, not a polynomial in the angles.
-- source:
--   Limitations on Joint Coherence Transfer in Quantum Thermodynamics, arXiv:2608.11872v1, https://arxiv.org/abs/2608.11872v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity

/-!
Statements from *Limitations on Joint Coherence Transfer in Quantum Thermodynamics*,
arXiv:2608.11872v1. All page numbers refer to PDF pages.
Paper-local definitions implement the finite-bath convention of pp.4,7, the
output-first unnormalized Choi convention of p.16, and the common Gram blocks of
pp.21–24. These definitions do not assert physical realizability of arbitrary Gram data.
-/

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

abbrev Map (d : ℕ) := Superop (Fin d) (Fin d)

/-- PDF p.6: the matrix unit |i><j|. -/
def matrixUnit {d : ℕ} (i j : Fin d) : Mat d :=
  Matrix.single i j 1

/-- PDF pp.4,6: trace preservation on all operators. -/
def IsTracePreserving {d : ℕ} (Phi : Map d) : Prop :=
  ∀ X, (Phi X).trace = X.trace

/-- PDF p.15: complex linearity of a map, including maps not assumed CP. -/
def IsComplexLinear {d : ℕ} (Phi : Map d) : Prop :=
  (∀ X Y, Phi (X + Y) = Phi X + Phi Y) ∧
  (∀ (z : ℂ) X, Phi (z • X) = z • Phi X)

/-- PDF p.6, Eq.(25): unnormalized Kraus–Gram vector. -/
def krausVector {d n : ℕ} (K : Fin n → Mat d) (r i : Fin d) :
    EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 fun a => K a r i

/-- PDF pp.4,6: basis-state transition weight (not an energy-level population). -/
def population {d : ℕ} (Phi : Map d) (r i : Fin d) : ℝ :=
  (Phi (matrixUnit i i) r r).re

/-- PDF p.6: complex collinearity; equality characterizations separately require nonzero vectors. -/
def Collinear {V : Type*} [AddCommGroup V] [Module ℂ V] (v w : V) : Prop :=
  ∃ a b : ℂ, (a ≠ 0 ∨ b ≠ 0) ∧ a • v + b • w = 0

/-- PDF p.4: normalized Gibbs weight per basis state at a finite real inverse temperature. -/
def gibbsWeight {d : ℕ} (E : Fin d → ℝ) (beta : ℝ) (i : Fin d) : ℝ :=
  Real.exp (-beta * E i) / ∑ j, Real.exp (-beta * E j)

/-- PDF p.4, Eq.(8): diagonal Gibbs density. Only used on nonzero systems. -/
def gibbsDensity {d : ℕ} (E : Fin d → ℝ) (beta : ℝ) : Mat d :=
  Matrix.diagonal fun i => (gibbsWeight E beta i : ℂ)

/-- PDF p.4, Eq.(7): e^{-itH} X e^{itH} in the fixed energy eigenbasis. -/
def timeEvolution {d : ℕ} (E : Fin d → ℝ) (t : ℝ) (X : Mat d) : Mat d :=
  fun i j => Complex.exp (-Complex.I * (t : ℂ) * ((E i - E j : ℝ) : ℂ)) * X i j

/-- PDF p.4: time-translation covariance on every operator. -/
def IsCovariant {d : ℕ} (E : Fin d → ℝ) (Phi : Map d) : Prop :=
  ∀ (t : ℝ) X, Phi (timeEvolution E t X) = timeEvolution E t (Phi X)

/-- PDF p.4: covariant Gibbs-preserving CPTP map. -/
def IsCGP {d : ℕ} (E : Fin d → ℝ) (beta : ℝ) (Phi : Map d) : Prop :=
  IsChannel Phi ∧ IsCovariant E Phi ∧ Phi (gibbsDensity E beta) = gibbsDensity E beta

/-- PDF pp.4,7: one finite nonempty bath and one common energy-preserving unitary. -/
structure ThermalDilation {d : ℕ} (E : Fin d → ℝ) (beta : ℝ) (b : ℕ) where
  bathPositive : 0 < b
  bathEnergy : Fin b → ℝ
  U : Matrix.unitaryGroup (Fin d × Fin b) ℂ
  support : ∀ (r i : Fin d) (nu mu : Fin b),
    E i + bathEnergy mu ≠ E r + bathEnergy nu →
    (U : Matrix (Fin d × Fin b) (Fin d × Fin b) ℂ) (r, nu) (i, mu) = 0

/-- PDF p.7, Eq.(33): Kraus index is the ordered bath input-output pair (mu,nu). -/
def thermalKraus {d b : ℕ} {E : Fin d → ℝ} {beta : ℝ}
    (D : ThermalDilation E beta b) : (Fin b × Fin b) → Mat d :=
  fun a r i => (Real.sqrt (gibbsWeight D.bathEnergy beta a.1) : ℂ) *
    (D.U : Matrix (Fin d × Fin b) (Fin d × Fin b) ℂ) (r, a.2) (i, a.1)

/-- PDF p.4, Eq.(5), via its explicit Kraus family in Eq.(33). -/
def thermalApply {d b : ℕ} {E : Fin d → ℝ} {beta : ℝ}
    (D : ThermalDilation E beta b) : Map d :=
  krausApply (thermalKraus D)

/-- PDF p.7, Eq.(38): zero-padded coordinates in one common bath-pair Hilbert space. -/
def shellVector {d b : ℕ} {E : Fin d → ℝ} {beta : ℝ}
    (D : ThermalDilation E beta b) (r i : Fin d) :
    EuclideanSpace ℂ (Fin b × Fin b) :=
  WithLp.toLp 2 fun a =>
    if E i + D.bathEnergy a.1 = E r + D.bathEnergy a.2
    then thermalKraus D a r i else 0

/-- PDF p.4: TO means finite-bath TO, with no topological closure. -/
def IsFiniteThermal {d : ℕ} (E : Fin d → ℝ) (beta : ℝ) (Phi : Map d) : Prop :=
  ∃ (b : ℕ) (D : ThermalDilation E beta b), ∀ X, Phi X = thermalApply D X

/-- PDF p.10, Eq.(64): exactly the nonzero contributing pairs. -/
def contributors {d : ℕ} (E : Fin d → ℝ) (Phi : Map d) (rho : Mat d)
    (r s : Fin d) : Finset (Fin d × Fin d) :=
  Finset.univ.filter fun a => E a.1 - E a.2 = E r - E s ∧
    rho a.1 a.2 ≠ 0 ∧ 0 < population Phi r a.1 * population Phi s a.2

/-- PDF p.10, Eq.(65): the mode-transport upper bound, omitting only vanishing terms. -/
def modeBound {d : ℕ} (E : Fin d → ℝ) (Phi : Map d) (rho : Mat d)
    (r s : Fin d) : ℝ :=
  ∑ a ∈ contributors E Phi rho r s,
    ‖rho a.1 a.2‖ * Real.sqrt (population Phi r a.1 * population Phi s a.2)

abbrev TransferEdges (d : ℕ) := Set ((Fin d × Fin d) × (Fin d × Fin d))

/-- PDF pp.10–11: a selected elementary bound connects transitions (r,i) and (s,j). -/
def JointElementary {d : ℕ} (Phi : Map d) (edges : TransferEdges d) : Prop :=
  ∀ e ∈ edges,
    ‖Phi (matrixUnit e.1.2 e.2.2) e.1.1 e.2.1‖ ^ 2 =
      population Phi e.1.1 e.1.2 * population Phi e.2.1 e.2.2

/-- PDF pp.10–11: graph vertices exclude zero vectors; edges are undirected selected pairs. -/
def saturationAdj {d b : ℕ} {E : Fin d → ℝ} {beta : ℝ}
    (D : ThermalDilation E beta b) (edges : TransferEdges d)
    (u v : {a : Fin d × Fin d // shellVector D a.1 a.2 ≠ 0}) : Prop :=
  u ≠ v ∧ ((u.val, v.val) ∈ edges ∨ (v.val, u.val) ∈ edges)

/-- PDF pp.6,16: only total energy-eigenspace populations are constrained. -/
def PopulationTask {d : ℕ} (E : Fin d → ℝ) (rho : Mat d) (pf : ℝ → ℝ)
    (Phi : Map d) : Prop :=
  ∀ i, (∑ r ∈ Finset.univ.filter (fun r => E r = E i), (Phi rho r r).re) = pf (E i)

/-- PDF p.11: a rectangular coherence block, with the L2 operator norm used below. -/
def energyBlock {d : ℕ} (E : Fin d → ℝ) (a b : ℝ) (X : Mat d) :
    Matrix {i : Fin d // E i = a} {j : Fin d // E j = b} ℂ :=
  fun i j => X i.val j.val

/-- PDF p.16, Eq.(117): output-first, unnormalized Choi matrix. -/
def choi {d : ℕ} (Phi : Map d) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  fun p q => Phi (matrixUnit p.2 q.2) p.1 q.1

/-- PDF p.16, Eq.(117): reconstruction has no transpose or conjugation of the input. -/
def fromChoi {d : ℕ} (J : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : Map d :=
  fun X x y => ∑ u, ∑ v, J (x, u) (y, v) * X u v

/-- PDF pp.15–16: fixed energies in order (0,1a,1b,3). -/
def fixedEnergy : Fin 4 → ℝ := ![0, 1, 1, 3]

/-- PDF p.16, Eq.(111): exact rational input matrix, not rounded eigenvalues. -/
def fixedRho : Mat 4 :=
  !![35/100, 5/100, 0, 4/100;
     5/100, 25/100, 0, 0;
     0, 0, 20/100, 5/100;
     4/100, 0, 5/100, 20/100]

/-- PDF pp.16–17, Eqs.(114)–(116): the middle basis populations are not fixed separately. -/
def FixedPopulations (X : Mat 4) : Prop :=
  X 0 0 = (1/2 : ℂ) ∧ X 1 1 + X 2 2 = (7/20 : ℂ) ∧ X 3 3 = (3/20 : ℂ)

/-- PDF p.16, Eq.(113): the concrete CGP channel feasible set. -/
def FixedChannelFeasible (Phi : Map 4) : Prop :=
  IsCGP fixedEnergy 1 Phi ∧ FixedPopulations (Phi fixedRho)

/-- PDF pp.16–17, Eqs.(118)–(121): exact Choi SDP feasible set. -/
def FixedChoiFeasible (J : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ) : Prop :=
  J.PosSemidef ∧
  (∀ u v, ∑ x, J (x,u) (x,v) = if u = v then 1 else 0) ∧
  (∀ x y, (∑ u, J (x,u) (y,u) * (gibbsWeight fixedEnergy 1 u : ℂ)) =
    if x = y then (gibbsWeight fixedEnergy 1 x : ℂ) else 0) ∧
  (∀ x u y v, fixedEnergy x - fixedEnergy u ≠ fixedEnergy y - fixedEnergy v →
    J (x,u) (y,v) = 0) ∧
  FixedPopulations (fromChoi J fixedRho)

/-- PDF pp.17–18: three signed real directional objectives in the specified order. -/
def objectivePair : Fin 3 → Fin 4 × Fin 4 := ![(0,1), (2,3), (0,3)]

/-- PDF p.17: directional witness on channels. -/
def channelObjective (k : Fin 3) (Phi : Map 4) : ℝ :=
  (Phi fixedRho (objectivePair k).1 (objectivePair k).2).re

/-- PDF p.18, Eq.(128): fixed CGP optima. Nonemptiness and boundedness follow from the
source's Lemma 3 and Remark 7 and are conclusions below, not additional hypotheses. -/
def cgpOptimum (k : Fin 3) : ℝ :=
  sSup ((fun J => channelObjective k (fromChoi J)) '' {J | FixedChoiFeasible J})

/-- PDF p.18, Eq.(129): optimize the sum over one common channel. -/
def cgpSumOptimum : ℝ :=
  sSup ((fun J => ∑ k : Fin 3, channelObjective k (fromChoi J)) '' {J | FixedChoiFeasible J})

/-- PDF p.19: finite-TO feasibility; its nonemptiness is not assumed. -/
def FixedTOFeasible (Phi : Map 4) : Prop :=
  IsFiniteThermal fixedEnergy 1 Phi ∧ FixedPopulations (Phi fixedRho)

/-- PDF p.19, Eq.(138): extended-real supremum, equal to minus infinity if infeasible. -/
def toOptimum (k : Fin 3) : EReal :=
  sSup ((fun Phi => (channelObjective k Phi : EReal)) '' {Phi | FixedTOFeasible Phi})

/-- PDF p.19, Eq.(139): optimize the summed witness over finite baths. -/
def toSumOptimum : EReal :=
  sSup ((fun Phi => ((∑ k : Fin 3, channelObjective k Phi : ℝ) : EReal)) ''
    {Phi | FixedTOFeasible Phi})

example {d n : ℕ} (K : Fin n → Mat d) (r i : Fin d) (a : Fin n) :
    krausVector K r i a = K a r i := rfl

example {d : ℕ} :
    QAlgorithms.Entanglement.IsCompletelyPositive (0 : Mat d →ₗ[ℂ] Mat d) := by
  intro r X _
  change (0 : Matrix (Fin r × Fin d) (Fin r × Fin d) ℂ).PosSemidef
  exact Matrix.PosSemidef.zero

example : fixedEnergy 1 = fixedEnergy 2 ∧ fixedRho 0 3 = (4/100 : ℂ) := by
  norm_num [fixedEnergy, fixedRho, Matrix.cons_val_two, Matrix.cons_val_three]

example (J : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ) :
    channelObjective 0 (fromChoi J) = (fromChoi J fixedRho 0 1).re := rfl

example : gibbsWeight ![0] 0 0 = 1 := by
  norm_num [gibbsWeight]

example {d : ℕ} (E : Fin d → ℝ) (X : Mat d) : timeEvolution E 0 X = X := by
  ext i j
  simp [timeEvolution]

example {d : ℕ} (X : Mat d) :
    fromChoi (0 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) X = 0 := by
  ext i j
  simp [fromChoi]

example {d b : ℕ} {E : Fin d → ℝ} {beta : ℝ}
    (D : ThermalDilation E beta b) (r i : Fin d) (mu nu : Fin b) :
    shellVector D r i (mu,nu) =
      if E i + D.bathEnergy mu = E r + D.bathEnergy nu
      then thermalKraus D (mu,nu) r i else 0 := rfl

/-- PDF p.20: U_minus = diag(1,1,-1); U_plus is the identity. -/
def signMatrix : Mat 3 := Matrix.diagonal ![1, 1, -1]

/-- PDF p.20, Proposition 3: the displayed random-unitary channel on all operators. -/
def directionalMixture (q : ℝ) : Map 3 :=
  fun X => (q : ℂ) • X + ((1 - q : ℝ) : ℂ) • (signMatrix * X * signMatrixᴴ)

/-- PDF p.20: actual coefficients of the map on span{|0><1|,|0><2|}. -/
def shortModeMatrix (q : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => directionalMixture q (matrixUnit 0 (Fin.succ j)) 0 (Fin.succ i)

/-- PDF p.20, Remark 11: the nonnegative bath gap, including zero at q=1/2. -/
def mixtureBathGap (beta q : ℝ) : ℝ :=
  beta⁻¹ * Real.log (if 1/2 ≤ q then q / (1 - q) else (1 - q) / q)

/-- PDF p.20, Remark 11: the controlled unitary, with control labels swapped for q<1/2. -/
def mixtureBathUnitary (q : ℝ) : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ :=
  fun x y => if x.2 = y.2 then
    if (1/2 ≤ q ∧ x.2 = 0) ∨ (q < 1/2 ∧ x.2 = 1)
    then (1 : Mat 3) x.1 y.1 else signMatrix x.1 y.1
  else 0

/-- PDF p.21: append two rectangular matrices horizontally. -/
def augment {a b c : Type*} (A : Matrix a b ℂ) (B : Matrix a c ℂ) :
    Matrix a (b ⊕ c) ℂ :=
  fun i j => Sum.elim (A i) (B i) j

/-- PDF pp.21,23, Eqs.(148),(157): the one common (g,g,1) Gram block. -/
def ladderGram {g : ℕ} (A B F : Mat g) (D E : Fin g → ℂ) (c : ℂ) :
    Matrix (Fin g ⊕ (Fin g ⊕ Fin 1)) (Fin g ⊕ (Fin g ⊕ Fin 1)) ℂ :=
  let colD : Matrix (Fin g) (Fin 1) ℂ := fun i _ => D i
  let colE : Matrix (Fin g) (Fin 1) ℂ := fun i _ => E i
  Matrix.fromBlocks A (augment F colD) (augment F colD)ᴴ
    (Matrix.fromBlocks B colE colEᴴ (fun _ _ => c))

/-- PDF p.21: combine the two directional selectors with the scalar selector. -/
def gramSelector {h g : ℕ} (R S : Matrix (Fin h) (Fin g) ℂ) (z : Fin h → ℂ) :
    Matrix (Fin h) (Fin g ⊕ (Fin g ⊕ Fin 1)) ℂ :=
  fun i j => Sum.elim (R i) (Sum.elim (S i) (fun _ => z i)) j

/-- PDF p.22, Eq.(152): the fixed scalar phase-frustration matrix. -/
def frustration : Mat 3 := !![1, -1, 1; -1, 1, 1; 1, 1, 1]

/-- PDF p.22: (g,g,1) zero extension along two selected rays. -/
def frustrationEmbedding {g : ℕ} (u v : Fin g → ℂ) :
    Matrix (Fin g ⊕ (Fin g ⊕ Fin 1)) (Fin g ⊕ (Fin g ⊕ Fin 1)) ℂ :=
  ladderGram (Matrix.vecMulVec u (fun i => conj (u i)))
    (Matrix.vecMulVec v (fun i => conj (v i)))
    (-Matrix.vecMulVec u (fun i => conj (v i))) u v 1

/-- PDF p.22, Eq.(153): all coupling blocks share the same leading corner. -/
def commonGram {d m : ℕ} (n : Fin m → ℕ) (A : Mat d)
    (B : (a : Fin m) → Matrix (Fin d) (Fin (n a)) ℂ)
    (C : (a b : Fin m) → Matrix (Fin (n a)) (Fin (n b)) ℂ) :
    Matrix (Fin d ⊕ (Sigma fun a => Fin (n a)))
      (Fin d ⊕ (Sigma fun a => Fin (n a))) ℂ :=
  let allB : Matrix (Fin d) (Sigma fun a => Fin (n a)) ℂ := fun i a => B a.1 i a.2
  Matrix.fromBlocks A allB allBᴴ (fun a b => C a.1 b.1 a.2 b.2)

/-- PDF pp.22–24: vanishing of all k-by-k minors, with no repeated rows or columns. -/
def AllMinorsZero {a b : Type*} (k : ℕ) (M : Matrix a b ℂ) : Prop :=
  ∀ (rows : Fin k ↪ a) (cols : Fin k ↪ b), (M.submatrix rows cols).det = 0

/-- PDF p.24, Eq.(161): the chosen nonzero angular direction. -/
def angularDirection (theta phi : ℝ) : Fin 2 → ℂ :=
  ![(Real.cos theta : ℂ), Complex.exp (Complex.I * (phi : ℂ)) * (Real.sin theta : ℂ)]

/-- PDF pp.24–25, Eq.(162): the determinant polynomial in vector entries. -/
def alignmentPolynomial : MvPolynomial (Fin 4) ℂ :=
  MvPolynomial.X 0 * MvPolynomial.X 3 - MvPolynomial.X 1 * MvPolynomial.X 2

/-- PDF pp.24–25: angular substitution in the determinant, not a polynomial in the angles. -/
def angularDeterminant (E : Fin 2 → ℂ) (p : ℝ × ℝ) : ℂ :=
  E 0 * Complex.exp (Complex.I * (p.2 : ℂ)) * (Real.sin p.1 : ℂ) -
    E 1 * (Real.cos p.1 : ℂ)

example (q : ℝ) : mixtureBathUnitary q (0,0) (0,1) = 0 := by
  simp [mixtureBathUnitary]

example {a b c : Type*} (A : Matrix a b ℂ) (B : Matrix a c ℂ) (i : a) (j : b) :
    augment A B i (Sum.inl j) = A i j := rfl

example : frustration 0 1 = -1 ∧ frustration 1 2 = 1 := by
  norm_num [frustration, Matrix.cons_val_two]

example (E : Fin 2 → ℂ) (theta phi : ℝ) :
    angularDeterminant E (theta,phi) =
      E 0 * angularDirection theta phi 1 - E 1 * angularDirection theta phi 0 := by
  simp [angularDeterminant, angularDirection, mul_assoc]

example : MvPolynomial.eval (fun _ : Fin 4 => (0 : ℂ)) alignmentPolynomial = 0 := by
  simp [alignmentPolynomial]

end

end QAlgorithms.Papers.Independent.Information100.P44


