-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
-- name    : QAlgorithms_Papers_Independent_Information100_P21
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T09:43:50.416984+00:00
-- url     : https://prove2.me/theorems/b73aed84-6268-4af0-b56e-5694e0859348
-- title:
--   Definitions for The Minimal Dimension of Entangled -Noise Advantage
-- statement:
--   The objects the formalized statements of *The Minimal Dimension of Entangled -Noise Advantage* (arXiv:2609.28367) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Op`
--   - `Vec`
--   - `QQ`
--   - `QT`
--   - `pt`: PDF p.4, S3: transpose the second register, in the displayed product basis.
--   - `tensor`: PDF pp.4,6: product ket in the fixed product basis.
--   - `conjugate`: PDF p.6: entrywise conjugation in the transpose basis.
--   - `proj`: PDF p.4: rank-one operator, allowing unnormalized vectors where explicitly intended.
--   - `quad`: PDF p.6: the real expectation of a Hermitian operator.
--   - `sep`: PDF p.4, S2: the actual separable cone's trace-one slice.
--   - `mix`: PDF p.5, S8--S9: normalized admixture, with noise-to-signal weight s.
--   - `robust`: PDF pp.5,28: robustness relative to a specified free set; true selects standard noise. In every use below the register is positive finite dimensional and the free set is the actual separable or fully separable set, so feasible costs are nonempty and bounded below. The explicit conic-attainment statement records these guards for the two-qubit SDPs.
--   - `rs`: PDF p.5: standard robustness with the actual bipartite free set.
--   - `rg`: PDF p.5: generalized robustness with the actual bipartite free set.
--   - `primalG`: PDF p.5: generalized conic feasibility in physical, untransposed noise Y.
--   - `primalS`: PDF p.5: standard conic feasibility, expressed in physical noise Y=K^Gamma.
--   - `dualG`: PDF p.6, Dg.
--   - `dualS`: PDF p.6, Ds; no density or entanglement hypothesis belongs to this predicate.
--   - `optG`: PDF pp.5--6: attained generalized primal optimum.
--   - `optS`: PDF pp.5--6: attained standard primal optimum, in physical noise coordinates.
--   - `optDG`: PDF p.6: generalized dual optimality means feasibility and domination of every feasible point.
--   - `optDS`: PDF p.6: standard dual optimality is not supplied as a rank-one hypothesis.
--   - `unitProduct`: PDF pp.7,12: normalized product vectors have normalized local factors.
--   - `pseudo`: PDF p.7, S20: spectral Moore--Penrose inverse, reciprocal zero on the kernel.
--   - `schmidtSq`: PDF pp.7,9: the larger Schmidt coefficient squared for a unit two-qubit ket. The determinant formula is the root formula for the reduced 2 by 2 density matrix.
--   - `quotient`: PDF p.9, S36: positive-part variational quotient.
--   - `maximizer`: PDF p.9: a maximizer is normalized and dominates the entire unit sphere.
--   - `schmidt`: PDF pp.7,10: an ordered normalized Schmidt decomposition, including the product case.
--   - `qmin`: PDF p.12, S52: lower endpoint of the compact product numerical range.
--   - `rprod`: PDF p.12, S53: extended nonnegative infimum; an empty feasible set has value infinity.
--   - `xstate`: PDF p.13, S59: real canonical X matrix, ordered 00,01,10,11.
--   - `physicalX`: PDF p.13, S59--S60: all physicality assumptions, with no full-rank restriction.
--   - `branchValue`: PDF p.13, S62: this branch is used only when t^2>x*y.
--   - `weights`: PDF p.20, S111: representative compressed weights, including t=max(x,y).
--   - `compressed`: PDF pp.19--20: two computational product projectors on a selected parity sector.
--   - `preparation`: PDF p.20: exactly k nonzero pure-product terms in a convex preparation.
--   - `preparationSizes`: PDF p.20: all optimal separable noises, with no diagonality restriction.
--   - `pureBSA`: PDF p.21, S115: the separable part has maximal trace among all PSD-remainder decompositions.
--   - `pureConcurrence`: PDF pp.15,23: pure-state two-qubit concurrence, also valid for subnormalized kets.
--   - `concurrence`: PDF pp.15,23: Wootters concurrence as its equivalent minimum-ensemble convex roof. All ensembles are finite, nonnegative, normalized, and consist of unit kets.
--   - `rhoStar`: PDF p.25, S134: the literal rational full-rank qubit--qutrit state.
--   - `noiseKet`: PDF p.25, S138: this ket is intentionally unnormalized.
--   - `noiseStar`: PDF p.25: feasible noise, not asserted optimal.
--   - `entangledPair`: PDF p.25, S140: the two entangled-subspace generators.
--   - `witnessW`: PDF pp.25--26: standard witness with factor 2/3.
--   - `witnessZ`: PDF p.25: physical entanglement witness, transposed on the qutrit.
--   - `familyM`: PDF p.26, S147: parameter family before subtracting the fixed projector.
--   - `familyT`: PDF p.26: T is computed from the parameters, never supplied as an arbitrary normalizer.
--   - `familyRho`: PDF p.26: normalized parameter-family input.
--   - `noisyStar`: PDF p.26, S149: epsilon is the white-noise weight.
--   - `rhoEx`: PDF p.16, S83: full-rank generic counterexample to the earlier candidate.
--   - `noiseEx`: PDF p.16, S87: exact standard-optimal unnormalized noise.
--   - `noiseOld`: PDF p.17, S92: restricted-family candidate; chi has norm squared 5/4.
--   - `descent`: PDF p.17, S95: continuous feasible descent toward the certified optimum.
--   - `spinFlip`: PDF p.15: spin-flip on a two-qubit ket in the fixed computational basis.
--   - `woottersFrame`: PDF p.15, S74: a Wootters frame, with lambda labels not yet sorted.
--   - `frameNorm`: PDF p.15, S75: the squared norm after Wootters rescaling.
--   - `oldCandidate`: PDF p.15, S76: the candidate formula, deliberately not identified with robustness.
--   - `truncWeight`: PDF p.18: positive one-based truncation weight.
--   - `truncC`: PDF p.18: finite positive normalization c_N.
--   - `truncRho`: PDF p.18: the two explicit finite maximally correlated states.
--   - `truncLower`: PDF p.18: explicit negativity sum (one-based indexing after shifting Fin coordinates).
--   - `Config`: PDF p.28, S158: computational basis of an arbitrary finite multipartite system.
--   - `productKet`: PDF p.28: tensor product of local pure kets, in a dependent product basis.
--   - `fs`: PDF p.28, S158: full separability, the actual finite convex hull of unit product projectors.
--   - `fsR`: PDF p.28: generalized and standard full-separability robustness use the same free set.
--   - `spectator`: PDF p.28: tensor a spectator without changing the displayed party partition.
--   - `localTensor`: PDF p.28: tensor of rectangular local isometries in the displayed product basis.
--   - `constantKet`: PDF p.29, S165: all-zero or all-one computational ket.
--   - `ghzKet`: PDF p.29, S165: normalized GHZ ket (used only for n>=2).
--   - `ghz`: PDF p.29: GHZ density operator.
--   - `ghzE`: PDF p.29, S165: the extreme computational diagonal projector.
--   - `ghzC`: PDF p.29, S165: GHZ coherence operator.
--   - `phaseMixture`: PDF p.29: explicit fully separable phase mixtures.
--   - `ghzZ`: PDF p.29, S167: standard GHZ witness.
--   - `ghzZg`: PDF p.29, S167: generalized GHZ witness.
--   - `noisyGHZ`: PDF p.30, S172: white noise has weight p, not 1-p.
--   - `Side`: PDF p.27: grouped basis on one side of a fixed cut.
--   - `cutGHZ`: PDF pp.3,30: the same GHZ state on a fixed grouped bipartition.
--   - `success`: PDF p.24, S129: success probability for one fixed POVM and ensemble.
--   - `advantageGeneral`: PDF p.24, S130: general-channel advantage; numerator and denominator share one POVM.
--   - `binaryGain`: PDF p.24, S131: binary gain optimizes the measurement for each input separately.
--   - `advantageBinary`: PDF p.24, S132: positive-denominator ratio of binary gains, not success probabilities.
--   - `FiniteLOCC`: PDF pp.2,24: finite adaptive LOCC, with arbitrary intermediate local dimensions, complete local Kraus instruments and outcome-dependent continuation. Local ancillas, classical randomness and disposal are included by the rectangular Kraus operators. Taking suprema permits limits of finite protocols, without claiming attainment.
--   - `singletFraction`: PDF p.24: optimized deterministic singlet fraction of the shared two-qubit state. The Bell overlap is evaluated after an actual LOCC protocol, not a free scalar or arbitrary channel.
--   - `blochKet`: PDF p.24: Bloch-sphere pure input for mean teleportation fidelity.
--   - `teleportInput`: PDF p.24: Alice initially holds the unknown input and her resource qubit. Fin 4 is ordered input-major, so its quotient/remainder by 2 select those registers.
--   - `meanFidelity`: PDF p.24: Haar-uniform qubit mean fidelity of a deterministic LOCC teleportation protocol. The integrands are continuous for valid finite protocols, hence integrable.
--   - `teleportFidelity`: PDF p.24: optimized mean fidelity over actual deterministic teleportation protocols. As for the singlet fraction, use the supremal finite-round value, allowing protocol limits.
-- source:
--   The Minimal Dimension of Entangled-Noise Advantage, arXiv:2609.28367v1, https://arxiv.org/abs/2609.28367v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Defs_EntanglementNegativity

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

abbrev Op (I : Type*) := Matrix I I ℂ

abbrev Vec (I : Type*) := EuclideanSpace ℂ I

abbrev QQ := Fin 2 × Fin 2

abbrev QT := Fin 2 × Fin 3

/-- PDF p.4, S3: transpose the second register, in the displayed product basis. -/
def pt {I J : Type*} (X : Op (I × J)) : Op (I × J) :=
  fun p q => X (p.1, q.2) (q.1, p.2)

/-- PDF pp.4,6: product ket in the fixed product basis. -/
def tensor {I J : Type*} (e : Vec I) (f : Vec J) : Vec (I × J) :=
  WithLp.toLp 2 fun p => e p.1 * f p.2

/-- PDF p.6: entrywise conjugation in the transpose basis. -/
def conjugate {I : Type*} (v : Vec I) : Vec I := WithLp.toLp 2 fun i => conj (v i)

/-- PDF p.4: rank-one operator, allowing unnormalized vectors where explicitly intended. -/
abbrev proj {I : Type*} (v : Vec I) : Op I := QAlgorithms.pureDensity v

/-- PDF p.6: the real expectation of a Hermitian operator. -/
def quad {I : Type*} [Fintype I] (M : Op I) (v : Vec I) : ℝ :=
  (∑ i, ∑ j, conj (v i) * M i j * v j).re

/-- PDF p.4, S2: the actual separable cone's trace-one slice. -/
def sep {I J : Type*} [Fintype I] [Fintype J] (X : Op (I × J)) : Prop :=
  QAlgorithms.Entanglement.IsSeparablePositive X ∧ X.trace = 1

/-- PDF p.5, S8--S9: normalized admixture, with noise-to-signal weight s. -/
def mix {I : Type*} (rho omega : Op I) (s : ℝ) : Op I :=
  (((1 + s)⁻¹ : ℝ) : ℂ) • (rho + (s : ℂ) • omega)

/-- PDF pp.5,28: robustness relative to a specified free set; true selects standard noise.
In every use below the register is positive finite dimensional and the free set is the
actual separable or fully separable set, so feasible costs are nonempty and bounded below.
The explicit conic-attainment statement records these guards for the two-qubit SDPs. -/
def robust {I : Type*} [Fintype I] (F : Set (Op I)) (standard : Bool) (rho : Op I) : ℝ :=
  sInf {s : ℝ | 0 ≤ s ∧ ∃ omega : Op I, QAlgorithms.IsDensityMatrix omega ∧
    (standard = true → omega ∈ F) ∧ mix rho omega s ∈ F}

/-- PDF p.5: standard robustness with the actual bipartite free set. -/
def rs {I J : Type*} [Fintype I] [Fintype J] (rho : Op (I × J)) : ℝ :=
  robust {X | sep X} true rho

/-- PDF p.5: generalized robustness with the actual bipartite free set. -/
def rg {I J : Type*} [Fintype I] [Fintype J] (rho : Op (I × J)) : ℝ :=
  robust {X | sep X} false rho

/-- PDF p.5: generalized conic feasibility in physical, untransposed noise Y. -/
def primalG (rho Y : Op QQ) : Prop := Y.PosSemidef ∧ (pt rho + pt Y).PosSemidef

/-- PDF p.5: standard conic feasibility, expressed in physical noise Y=K^Gamma. -/
def primalS (rho Y : Op QQ) : Prop := primalG rho Y ∧ (pt Y).PosSemidef

/-- PDF p.6, Dg. -/
def dualG (W : Op QQ) : Prop := W.PosSemidef ∧ (1 - pt W).PosSemidef

/-- PDF p.6, Ds; no density or entanglement hypothesis belongs to this predicate. -/
def dualS (W P Q : Op QQ) : Prop :=
  W.PosSemidef ∧ P.PosSemidef ∧ Q.PosSemidef ∧ 1 - W = P + pt Q

/-- PDF pp.5--6: attained generalized primal optimum. -/
def optG (rho Y : Op QQ) : Prop := primalG rho Y ∧ Y.trace.re = rg rho

/-- PDF pp.5--6: attained standard primal optimum, in physical noise coordinates. -/
def optS (rho Y : Op QQ) : Prop := primalS rho Y ∧ Y.trace.re = rs rho

/-- PDF p.6: generalized dual optimality means feasibility and domination of every feasible point. -/
def optDG (rho W : Op QQ) : Prop :=
  dualG W ∧ ∀ V, dualG V → (-(V * pt rho).trace.re) ≤ (-(W * pt rho).trace.re)

/-- PDF p.6: standard dual optimality is not supplied as a rank-one hypothesis. -/
def optDS (rho W P Q : Op QQ) : Prop :=
  dualS W P Q ∧ ∀ V A B, dualS V A B → (-(V * pt rho).trace.re) ≤ (-(W * pt rho).trace.re)

/-- PDF pp.7,12: normalized product vectors have normalized local factors. -/
def unitProduct {I J : Type*} [Fintype I] [Fintype J] (p : Vec (I × J)) : Prop :=
  ∃ e : Vec I, ∃ f : Vec J, ‖e‖ = 1 ∧ ‖f‖ = 1 ∧ p = tensor e f

/-- PDF p.7, S20: spectral Moore--Penrose inverse, reciprocal zero on the kernel. -/
def pseudo {I : Type*} [Fintype I] [DecidableEq I] (W : Op I) : Op I :=
  cfc (fun x : ℝ => x⁻¹) W

/-- PDF pp.7,9: the larger Schmidt coefficient squared for a unit two-qubit ket.
The determinant formula is the root formula for the reduced 2 by 2 density matrix. -/
def schmidtSq (b : Vec QQ) : ℝ :=
  (1 + Real.sqrt (1 - 4 * Complex.normSq (b (0,0) * b (1,1) - b (0,1) * b (1,0)))) / 2

/-- PDF p.9, S36: positive-part variational quotient. -/
def quotient (rho : Op QQ) (b : Vec QQ) : ℝ := max (-quad (pt rho) b) 0 / schmidtSq b

/-- PDF p.9: a maximizer is normalized and dominates the entire unit sphere. -/
def maximizer (rho : Op QQ) (b : Vec QQ) : Prop :=
  ‖b‖ = 1 ∧ ∀ v : Vec QQ, ‖v‖ = 1 → quotient rho v ≤ quotient rho b

/-- PDF pp.7,10: an ordered normalized Schmidt decomposition, including the product case. -/
def schmidt (b : Vec QQ) (a1 a2 : ℝ) (u f : Fin 2 → Vec (Fin 2)) : Prop :=
  Orthonormal ℂ u ∧ Orthonormal ℂ f ∧ 0 ≤ a2 ∧ a2 ≤ a1 ∧ a1^2 + a2^2 = 1 ∧
    b = (a1 : ℂ) • tensor (u 0) (f 0) + (a2 : ℂ) • tensor (u 1) (f 1)

/-- PDF p.12, S52: lower endpoint of the compact product numerical range. -/
def qmin (A : Op QQ) : ℝ := sInf {q : ℝ | ∃ p : Vec QQ, unitProduct p ∧ q = quad A p}

/-- PDF p.12, S53: extended nonnegative infimum; an empty feasible set has value infinity. -/
def rprod (rho : Op QQ) : ℝ≥0∞ :=
  ⨅ (t : ℝ) (_ : 0 ≤ t) (p : Vec QQ) (_ : unitProduct p)
    (_ : (pt rho + (t : ℂ) • proj p).PosSemidef), ENNReal.ofReal t

/-- PDF p.13, S59: real canonical X matrix, ordered 00,01,10,11. -/
def xstate (a b c d w z : ℝ) : Op QQ :=
  fun i j => (!![(a:ℂ),0,0,(w:ℂ); 0,(b:ℂ),(z:ℂ),0;
    0,(z:ℂ),(c:ℂ),0; (w:ℂ),0,0,(d:ℂ)]) ⟨2*i.1.val+i.2.val, by omega⟩ ⟨2*j.1.val+j.2.val, by omega⟩

/-- PDF p.13, S59--S60: all physicality assumptions, with no full-rank restriction. -/
def physicalX (a b c d w z : ℝ) : Prop :=
  0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ w ∧ 0 ≤ z ∧
    a+b+c+d=1 ∧ w^2 ≤ a*d ∧ z^2 ≤ b*c

/-- PDF p.13, S62: this branch is used only when t^2>x*y. -/
def branchValue (x y t : ℝ) : ℝ :=
  if t ≤ max x y then (t^2-x*y)/max x y else 2*t-x-y

/-- PDF p.20, S111: representative compressed weights, including t=max(x,y). -/
def weights (x y t : ℝ) : ℝ × ℝ :=
  if max x y ≤ t then (t-x,t-y) else if t < x then (0,t^2/x-y) else (t^2/y-x,0)

/-- PDF pp.19--20: two computational product projectors on a selected parity sector. -/
def compressed (odd : Bool) (u v : ℝ) : Op QQ :=
  (u : ℂ) • proj (QAlgorithms.ket (0, if odd then 1 else 0)) +
  (v : ℂ) • proj (QAlgorithms.ket (1, if odd then 0 else 1))

/-- PDF p.20: exactly k nonzero pure-product terms in a convex preparation. -/
def preparation (k : ℕ) (omega : Op QQ) : Prop :=
  ∃ w : Fin k → ℝ, ∃ p : Fin k → Vec QQ,
    (∀ i, 0 < w i ∧ unitProduct (p i)) ∧ (∑ i, w i)=1 ∧
      omega = ∑ i, (w i : ℂ) • proj (p i)

/-- PDF p.20: all optimal separable noises, with no diagonality restriction. -/
def preparationSizes (rho : Op QQ) : Set ℕ :=
  {k | ∃ omega : Op QQ, QAlgorithms.IsDensityMatrix omega ∧ sep omega ∧
    sep (mix rho omega (rs rho)) ∧ preparation k omega}

/-- PDF p.21, S115: the separable part has maximal trace among all PSD-remainder decompositions. -/
def pureBSA (rho S : Op QQ) (epsilon : ℝ) (psi : Vec QQ) : Prop :=
  QAlgorithms.Entanglement.IsSeparablePositive S ∧ 0 < epsilon ∧ ‖psi‖=1 ∧
    rho = S + (epsilon:ℂ) • proj psi ∧
    ∀ T : Op QQ, QAlgorithms.Entanglement.IsSeparablePositive T →
      (rho-T).PosSemidef → T.trace.re ≤ S.trace.re

/-- PDF pp.15,23: pure-state two-qubit concurrence, also valid for subnormalized kets. -/
def pureConcurrence (b : Vec QQ) : ℝ :=
  2 * ‖b (0,0)*b (1,1)-b (0,1)*b (1,0)‖

/-- PDF pp.15,23: Wootters concurrence as its equivalent minimum-ensemble convex roof.
All ensembles are finite, nonnegative, normalized, and consist of unit kets. -/
def concurrence (rho : Op QQ) : ℝ :=
  sInf {c : ℝ | ∃ k : ℕ, ∃ w : Fin k → ℝ, ∃ v : Fin k → Vec QQ,
    (∀ i, 0 ≤ w i ∧ ‖v i‖=1) ∧ (∑ i,w i)=1 ∧
    rho = ∑ i, (w i:ℂ) • proj (v i) ∧ c = ∑ i,w i * pureConcurrence (v i)}

/-- PDF p.25, S134: the literal rational full-rank qubit--qutrit state. -/
def rhoStar : Op QT :=
  fun i j => (1/40:ℂ) * (!![2,0,0,0,0,0; 0,1,0,-4,0,0; 0,0,13,0,-5,0;
    0,-4,0,17,0,0; 0,0,-5,0,2,0; 0,0,0,0,0,5])
    ⟨3*i.1.val+i.2.val, by omega⟩ ⟨3*j.1.val+j.2.val, by omega⟩

/-- PDF p.25, S138: this ket is intentionally unnormalized. -/
def noiseKet : Vec QT := 2 • QAlgorithms.ket (0,1) + QAlgorithms.ket (1,0)

/-- PDF p.25: feasible noise, not asserted optimal. -/
def noiseStar : Op QT := (1/40:ℂ) • proj noiseKet

/-- PDF p.25, S140: the two entangled-subspace generators. -/
def entangledPair (j : Fin 2) : Vec QT :=
  if j=0 then QAlgorithms.ket (0,0) + QAlgorithms.ket (1,1)
  else QAlgorithms.ket (0,1) + QAlgorithms.ket (1,2)

/-- PDF pp.25--26: standard witness with factor 2/3. -/
def witnessW : Op QT := (2/3:ℂ) • (proj (entangledPair 0) + proj (entangledPair 1))

/-- PDF p.25: physical entanglement witness, transposed on the qutrit. -/
def witnessZ : Op QT := pt witnessW

/-- PDF p.26, S147: parameter family before subtracting the fixed projector. -/
def familyM (a b c d : ℝ) : Op QT :=
  fun i j => (!![(a:ℂ),0,0,0,0,0; 0,(b:ℂ),0,(-a:ℂ),0,0;
    0,0,(c:ℂ),0,(-b:ℂ),0; 0,(-a:ℂ),0,(d:ℂ),0,0;
    0,0,(-b:ℂ),0,(a:ℂ),0; 0,0,0,0,0,(b:ℂ)])
    ⟨3*i.1.val+i.2.val, by omega⟩ ⟨3*j.1.val+j.2.val, by omega⟩

/-- PDF p.26: T is computed from the parameters, never supplied as an arbitrary normalizer. -/
def familyT (a b c d : ℝ) : ℝ := 2*a+2*b+c+d-5

/-- PDF p.26: normalized parameter-family input. -/
def familyRho (a b c d : ℝ) : Op QT :=
  ((familyT a b c d)⁻¹:ℂ) • (familyM a b c d - proj noiseKet)

/-- PDF p.26, S149: epsilon is the white-noise weight. -/
def noisyStar (epsilon : ℝ) : Op QT := (1-epsilon:ℂ) • rhoStar + (epsilon/6:ℂ) • 1

/-- PDF p.16, S83: full-rank generic counterexample to the earlier candidate. -/
def rhoEx : Op QQ := xstate (3/8) (1/5) (1/20) (3/8) (1/4) (1/100)

/-- PDF p.16, S87: exact standard-optimal unnormalized noise. -/
def noiseEx : Op QQ := compressed true (1/20) (1/5)

/-- PDF p.17, S92: restricted-family candidate; chi has norm squared 5/4. -/
def noiseOld : Op QQ :=
  (3/20:ℂ) • (proj (((Real.sqrt 2)⁻¹:ℂ) • (QAlgorithms.ket (0,0)-QAlgorithms.ket (1,1))) +
    proj ((1/2:ℂ) • (2 • QAlgorithms.ket (0,1)+QAlgorithms.ket (1,0))))

/-- PDF p.17, S95: continuous feasible descent toward the certified optimum. -/
def descent (t : ℝ) : Op QQ := (1-t:ℂ) • noiseOld + (t:ℂ) • noiseEx

/-- PDF p.15: spin-flip on a two-qubit ket in the fixed computational basis. -/
def spinFlip (v : Vec QQ) : Vec QQ := WithLp.toLp 2 fun p =>
  if p=(0,0) then -conj (v (1,1)) else if p=(1,1) then -conj (v (0,0))
  else if p=(0,1) then conj (v (1,0)) else conj (v (0,1))

/-- PDF p.15, S74: a Wootters frame, with lambda labels not yet sorted. -/
def woottersFrame (rho : Op QQ) (lam : Fin 4 → ℝ) (v : Fin 4 → Vec QQ) : Prop :=
  rho = ∑ i, proj (v i) ∧ ∀ i j,
    inner ℂ (v i) (spinFlip (v j)) = if i=j then (lam i:ℂ) else 0

/-- PDF p.15, S75: the squared norm after Wootters rescaling. -/
def frameNorm (lam : Fin 4 → ℝ) (v : Fin 4 → Vec QQ) (i : Fin 4) : ℝ := ‖v i‖^2/lam i

/-- PDF p.15, S76: the candidate formula, deliberately not identified with robustness. -/
def oldCandidate (lam K : Fin 4 → ℝ) : ℝ :=
  max 0 (lam 0-lam 1-lam 2-lam 3)/2 *
    min (K 1+K 2) (min (K 1+K 3) (K 2+K 3))

/-- PDF p.18: positive one-based truncation weight. -/
def truncWeight (j : ℕ) : ℝ := (Real.sqrt (j+1) * Real.log (j+2))⁻¹

/-- PDF p.18: finite positive normalization c_N. -/
def truncC (N : ℕ) : ℝ := ∑ j : Fin N, truncWeight j.val ^ 2

/-- PDF p.18: the two explicit finite maximally correlated states. -/
def truncRho (N : ℕ) (plus : Bool) : Op (Fin N × Fin N) := fun x y =>
  if x.1=x.2 ∧ y.1=y.2 then
    ((truncC N)⁻¹ * truncWeight x.1.val * truncWeight y.1.val:ℂ) *
      (if x.1=y.1 then 1 else
        (if plus then Complex.I else -Complex.I) /
          ((Real.pi * ((x.1.val:ℝ)-(y.1.val:ℝ))):ℂ))
  else 0

/-- PDF p.18: explicit negativity sum (one-based indexing after shifting Fin coordinates). -/
def truncLower (N : ℕ) : ℝ :=
  (Real.pi * truncC N)⁻¹ * ∑ j : Fin N, ∑ k : Fin N,
    if j<k then truncWeight j.val * truncWeight k.val / ((k.val:ℝ)-(j.val:ℝ)) else 0

/-- PDF p.28, S158: computational basis of an arbitrary finite multipartite system. -/
abbrev Config {P : Type*} (d : P → ℕ) := (j : P) → Fin (d j)

/-- PDF p.28: tensor product of local pure kets, in a dependent product basis. -/
def productKet {P : Type*} [Fintype P] {d : P → ℕ}
    (v : (j : P) → Vec (Fin (d j))) : Vec (Config d) :=
  WithLp.toLp 2 fun x => ∏ j, v j (x j)

/-- PDF p.28, S158: full separability, the actual finite convex hull of unit product projectors. -/
def fs {P : Type*} [Fintype P] (d : P → ℕ) : Set (Op (Config d)) :=
  convexHull ℝ {X | ∃ v : (j : P) → Vec (Fin (d j)), (∀ j, ‖v j‖=1) ∧ X=proj (productKet v)}

/-- PDF p.28: generalized and standard full-separability robustness use the same free set. -/
def fsR {P : Type*} [Fintype P] (d : P → ℕ) (standard : Bool) (rho : Op (Config d)) : ℝ :=
  robust (fs d) standard rho

/-- PDF p.28: tensor a spectator without changing the displayed party partition. -/
def spectator {P L : Type*} [Fintype P] [Fintype L] {d : P → ℕ} {e : L → ℕ}
    (rho : Op (Config d)) (eta : Op (Config e)) : Op (Config (Sum.elim d e)) :=
  fun x y => rho (fun j => x (Sum.inl j)) (fun j => y (Sum.inl j)) *
    eta (fun j => x (Sum.inr j)) (fun j => y (Sum.inr j))

/-- PDF p.28: tensor of rectangular local isometries in the displayed product basis. -/
def localTensor {P : Type*} [Fintype P] {d e : P → ℕ}
    (V : (j : P) → Matrix (Fin (e j)) (Fin (d j)) ℂ) : Matrix (Config e) (Config d) ℂ :=
  fun x y => ∏ j, V j (x j) (y j)

/-- PDF p.29, S165: all-zero or all-one computational ket. -/
def constantKet (n : ℕ) (one : Bool) : Vec (Fin n → Fin 2) :=
  QAlgorithms.ket (fun _ => if one then 1 else 0)

/-- PDF p.29, S165: normalized GHZ ket (used only for n>=2). -/
def ghzKet (n : ℕ) (plus : Bool) : Vec (Fin n → Fin 2) :=
  ((Real.sqrt 2)⁻¹:ℂ) • (constantKet n false + (if plus then 1 else (-1:ℂ)) • constantKet n true)

/-- PDF p.29: GHZ density operator. -/
def ghz (n : ℕ) (plus : Bool) : Op (Fin n → Fin 2) := proj (ghzKet n plus)

/-- PDF p.29, S165: the extreme computational diagonal projector. -/
def ghzE (n : ℕ) : Op (Fin n → Fin 2) := proj (constantKet n false) + proj (constantKet n true)

/-- PDF p.29, S165: GHZ coherence operator. -/
def ghzC (n : ℕ) : Op (Fin n → Fin 2) := fun x y =>
  constantKet n false x * conj (constantKet n true y) +
  constantKet n true x * conj (constantKet n false y)

/-- PDF p.29: explicit fully separable phase mixtures. -/
def phaseMixture (n : ℕ) (plus : Bool) : Op (Fin n → Fin 2) :=
  ((2^n:ℝ)⁻¹:ℂ) • (1 + (if plus then 1 else (-1:ℂ)) • ghzC n)

/-- PDF p.29, S167: standard GHZ witness. -/
def ghzZ (n : ℕ) : Op (Fin n → Fin 2) :=
  (((2^n:ℝ)/(2*((2^n:ℝ)-2))):ℂ) • (1-ghzE n) - (((2^n:ℝ)/4):ℂ) • ghzC n

/-- PDF p.29, S167: generalized GHZ witness. -/
def ghzZg (n : ℕ) : Op (Fin n → Fin 2) := (((2^n:ℝ)/4)⁻¹:ℂ) • ghzZ n

/-- PDF p.30, S172: white noise has weight p, not 1-p. -/
def noisyGHZ (n : ℕ) (p : ℝ) : Op (Fin n → Fin 2) :=
  (1-p:ℂ) • ghz n true + ((p/(2^n:ℝ)):ℂ) • 1

/-- PDF p.27: grouped basis on one side of a fixed cut. -/
abbrev Side {P : Type*} (d : P → ℕ) (S : Finset P) := (j : {j // j ∈ S}) → Fin (d j)

/-- PDF pp.3,30: the same GHZ state on a fixed grouped bipartition. -/
def cutGHZ (n : ℕ) (S : Finset (Fin n)) : Op (Side (fun _ : Fin n => 2) S × Side (fun _ : Fin n => 2) Sᶜ) :=
  proj (WithLp.toLp 2 fun x =>
    if ((∀ j, x.1 j=0) ∧ (∀ j, x.2 j=0)) ∨ ((∀ j, x.1 j=1) ∧ (∀ j, x.2 j=1))
    then ((Real.sqrt 2)⁻¹:ℂ) else 0)

/-- PDF p.24, S129: success probability for one fixed POVM and ensemble. -/
def success {k m : ℕ} (p : Fin k → ℝ) (E : Fin k → QAlgorithms.Superop QQ (Fin m))
    (M : Fin k → Op (Fin m)) (rho : Op QQ) : ℝ :=
  ∑ i, p i * (M i * E i rho).trace.re

/-- PDF p.24, S130: general-channel advantage; numerator and denominator share one POVM. -/
def advantageGeneral (rho : Op QQ) : ℝ :=
  sSup {r : ℝ | ∃ k m : ℕ, ∃ p : Fin k → ℝ,
    ∃ E : Fin k → QAlgorithms.Superop QQ (Fin m), ∃ M : Fin k → Op (Fin m),
    (∀ i, 0 ≤ p i ∧ QAlgorithms.IsChannel (E i)) ∧ (∑ i,p i)=1 ∧ QAlgorithms.IsPOVM M ∧
    let denominator := sSup {s : ℝ | ∃ sigma : Op QQ, sep sigma ∧ s=success p E M sigma}
    0 < denominator ∧ r = success p E M rho / denominator}

/-- PDF p.24, S131: binary gain optimizes the measurement for each input separately. -/
def binaryGain {m : ℕ} (E : Fin 2 → QAlgorithms.Superop QQ (Fin m)) (rho : Op QQ) : ℝ :=
  sSup {s : ℝ | ∃ M : Fin 2 → Op (Fin m), QAlgorithms.IsPOVM M ∧
    s=success (fun _ => 1/2) E M rho} - 1/2

/-- PDF p.24, S132: positive-denominator ratio of binary gains, not success probabilities. -/
def advantageBinary (rho : Op QQ) : ℝ :=
  sSup {r : ℝ | ∃ m : ℕ, ∃ E : Fin 2 → QAlgorithms.Superop QQ (Fin m),
    (∀ i, QAlgorithms.IsChannel (E i)) ∧
    let denominator := sSup {s : ℝ | ∃ sigma : Op QQ, sep sigma ∧ s=binaryGain E sigma}
    0 < denominator ∧ r=binaryGain E rho/denominator}

/-- Sanity checks: Gamma acts on the second, not first, register and is an involution. -/
example {I J : Type*} (X : Op (I × J)) : pt (pt X)=X := rfl

example (X : Op QT) : pt X (0,1) (1,2) = X (0,2) (1,1) := rfl

example {I : Type*} (rho omega : Op I) : mix rho omega 0 = rho := by simp [mix]

example : schmidtSq (QAlgorithms.ket (0,0))=1 := by norm_num [schmidtSq, QAlgorithms.ket]

example (a b c d w z : ℝ) : xstate a b c d w z (0,0) (1,1)=(w:ℂ) := rfl

example : weights (1/5) (1/20) (1/4) = (1/20,1/5) := by norm_num [weights]

example : rhoStar (1,0) (1,0)=(17/40:ℂ) := by norm_num [rhoStar]

example : familyT 2 5 13 18=40 := by norm_num [familyT]

example : noiseOld (0,1) (0,1)=(3/20:ℂ) := by
  norm_num [noiseOld, proj, QAlgorithms.pureDensity, QAlgorithms.ket]

example : truncC 0=0 := by simp [truncC]

example : phaseMixture 2 true = (1/4:ℂ) • (1+ghzC 2) := by norm_num [phaseMixture]

/-- PDF pp.2,24: finite adaptive LOCC, with arbitrary intermediate local dimensions,
complete local Kraus instruments and outcome-dependent continuation. Local ancillas,
classical randomness and disposal are included by the rectangular Kraus operators.
Taking suprema permits limits of finite protocols, without claiming attainment. -/
inductive FiniteLOCC : {a b c d : ℕ} →
    QAlgorithms.Superop (Fin a × Fin b) (Fin c × Fin d) → Prop
  | identity (a b : ℕ) : FiniteLOCC (fun X : Op (Fin a × Fin b) => X)
  | alice {a b c d h k : ℕ} (E : Fin k → Matrix (Fin h) (Fin a) ℂ)
      (complete : QAlgorithms.IsKrausFamily E)
      (next : Fin k → QAlgorithms.Superop (Fin h × Fin b) (Fin c × Fin d))
      (valid : ∀ i, FiniteLOCC (next i)) :
      FiniteLOCC (fun (X : Op (Fin a × Fin b)) => ∑ i, next i
        ((Matrix.kronecker (E i) (1 : Op (Fin b)) * X :
            Matrix (Fin h × Fin b) (Fin a × Fin b) ℂ) *
          (Matrix.kronecker (E i) (1 : Op (Fin b)))ᴴ : Op (Fin h × Fin b)))
  | bob {a b c d h k : ℕ} (E : Fin k → Matrix (Fin h) (Fin b) ℂ)
      (complete : QAlgorithms.IsKrausFamily E)
      (next : Fin k → QAlgorithms.Superop (Fin a × Fin h) (Fin c × Fin d))
      (valid : ∀ i, FiniteLOCC (next i)) :
      FiniteLOCC (fun (X : Op (Fin a × Fin b)) => ∑ i, next i
        ((Matrix.kronecker (1 : Op (Fin a)) (E i) * X :
            Matrix (Fin a × Fin h) (Fin a × Fin b) ℂ) *
          (Matrix.kronecker (1 : Op (Fin a)) (E i))ᴴ : Op (Fin a × Fin h)))

/-- PDF p.24: optimized deterministic singlet fraction of the shared two-qubit state.
The Bell overlap is evaluated after an actual LOCC protocol, not a free scalar or arbitrary channel. -/
def singletFraction (rho : Op QQ) : ℝ :=
  sSup {f : ℝ | ∃ Phi : QAlgorithms.Superop QQ QQ, FiniteLOCC Phi ∧
    f=quad (Phi rho) (ghzKet 2 true |> fun v =>
      WithLp.toLp 2 fun p : QQ => v (fun j => if j=0 then p.1 else p.2))}

/-- PDF p.24: Bloch-sphere pure input for mean teleportation fidelity. -/
def blochKet (theta phi : ℝ) : Vec (Fin 2) := WithLp.toLp 2 fun j =>
  if j=0 then (Real.cos (theta/2):ℂ)
  else Complex.exp (Complex.I * (phi:ℂ)) * (Real.sin (theta/2):ℂ)

/-- PDF p.24: Alice initially holds the unknown input and her resource qubit.
Fin 4 is ordered input-major, so its quotient/remainder by 2 select those registers. -/
def teleportInput (rho : Op QQ) (input : Op (Fin 2)) : Op (Fin 4 × Fin 2) :=
  fun x y => input ⟨x.1.val/2, by omega⟩ ⟨y.1.val/2, by omega⟩ *
    rho (⟨x.1.val%2, by omega⟩,x.2) (⟨y.1.val%2, by omega⟩,y.2)

/-- PDF p.24: Haar-uniform qubit mean fidelity of a deterministic LOCC teleportation protocol.
The integrands are continuous for valid finite protocols, hence integrable. -/
def meanFidelity (rho : Op QQ)
    (Phi : QAlgorithms.Superop (Fin 4 × Fin 2) (Fin 1 × Fin 2)) : ℝ :=
  (4*Real.pi)⁻¹ * ∫ theta in (0:ℝ)..Real.pi,
    ∫ phi in (0:ℝ)..(2*Real.pi), Real.sin theta *
      quad (QAlgorithms.traceLeft (Phi (teleportInput rho (proj (blochKet theta phi)))))
        (blochKet theta phi)

/-- PDF p.24: optimized mean fidelity over actual deterministic teleportation protocols.
As for the singlet fraction, use the supremal finite-round value, allowing protocol limits. -/
def teleportFidelity (rho : Op QQ) : ℝ :=
  sSup {f : ℝ | ∃ Phi : QAlgorithms.Superop (Fin 4 × Fin 2) (Fin 1 × Fin 2),
    FiniteLOCC Phi ∧ f=meanFidelity rho Phi}

example : FiniteLOCC (fun X : Op QQ => X) := FiniteLOCC.identity 2 2

example : blochKet 0 0 = QAlgorithms.ket 0 := by
  ext j
  fin_cases j <;> simp [blochKet,QAlgorithms.ket]

end QAlgorithms.Papers.Independent.Information100.P21


