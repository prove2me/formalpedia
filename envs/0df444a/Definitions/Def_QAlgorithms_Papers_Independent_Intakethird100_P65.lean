-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P65
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P65
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T08:38:37.573867+00:00
-- url     : https://prove2.me/theorems/8a702f48-a0bd-4560-96eb-1df5a48e4e61
-- title:
--   Definitions for Quantum Channel Simulation and the Channel's Smooth Max-Information
-- statement:
--   The objects the formalized statements of *Quantum Channel Simulation and the Channel's Smooth Max-Information* (arXiv:1807.05354) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `StateBall`: PDF p.7: a subnormalized closed purified-distance ball.
--   - `maxInfo`: PDF p.7, Eq.(24): optimize normalized B, keeping the actual A marginal.
--   - `smoothInfo`: PDF p.10, Eq.(45): free smoothing, using each candidate's own marginal.
--   - `fixedSmoothInfo`: PDF p.10, Eq.(46): hatted smoothing fixes the entire reference marginal.
--   - `referenceSmoothInfo`: PDF p.19, Eq.(76): tilde smoothing fixes only the reference in Dmax.
--   - `maxEntangledInput`: PDF p.8: normalized maximally entangled state. Only nonempty A is used.
--   - `purify`: PDF pp.8,10: canonical purification of rho, without a full-rank restriction.
--   - `channelInfo`: PDF p.8, Definition 4: max-information of the normalized Choi state. For CPTP maps on positive-dimensional systems the extended value is finite.
--   - `halfDiamondDistance`: PDF p.3, Eq.(1): HALF the full diamond norm.
--   - `smoothChannelInfo`: PDF p.8, Definition 5: same-dimensional CPTP channel smoothing.
--   - `BipartiteNSOperation`: PDF pp.2--3: no-signalling is defined on the operation, independently of its Choi constraints. Both directional marginal maps are channels.
--   - `PPTCode`: PDF p.3: complete positivity of the transpose-conjugated operation.
--   - `EntCode`: PDF pp.2--3: entanglement-assisted local encoding and decoding with an arbitrary finite shared density. The body is the contraction of these local maps, not a no-signalling or entropy assumption.
--   - `SimulationAssistance`: Assistance classes in PDF pp.3,10.
--   - `AllowedSimulationCode`: Membership in the source's independently operational code classes.
--   - `wire`: PDF pp.2--3: connect Ao to Bi through N by matrix-unit expansion of the operations on arbitrary input X. This is independent of the Choi link formula.
--   - `minimumError`: PDF p.3, Eq.(1): optimize the half-diamond error over actual codes. On the source domain the feasible set is nonempty and errors lie in [0,1].
--   - `oneUseSimulationCost`: PDF p.4, Eq.(4): cost of one use of an integer-dimensional noiseless channel. Positive resource dimensions include m=1.
--   - `SimulationRate`: PDF pp.4,10: operational vanishing-error simulation rates, with rate slack before blocklength. No entropy formula enters this definition.
--   - `CommunicationRate`: PDF p.10: operational vanishing-error communication rates.
--   - `vanishingErrorSimulationCost`: PDF pp.4,10: infimum of operational simulation rates; extended at empty sets.
--   - `vanishingErrorQuantumCapacity`: PDF p.10: supremum of operational communication rates, independently defined.
--   - `zeroErrorCost`: PDF p.7, Eq.(20): zero error is fixed before the blocklength limit. The threshold-rate form avoids assigning a default value to a nonexistent limit.
--   - `channelMutualInfo`: PDF p.10, Eq.(43): optimize over ALL input densities, including singular ones.
--   - `IteratedLimit`: PDF pp.10--12: actual successive limits, with positive blocklength and right-hand epsilon limit. In particular no liminf or totalized limit is substituted.
--   - `Constant`: PDF p.9, Eq.(35): all constant channels, not only full-support outputs.
--   - `smoothChannelDmax`: PDF p.9, Eq.(37): smooth N over CPTP maps, with fixed reference M.
--   - `constantChannelRobustness`: PDF p.9, Eq.(38): independently defined generalized robustness. Mixing noise is arbitrary CPTP; only the resulting convex mixture must be constant.
--   - `smoothRobustness`: PDF p.10, Eq.(39): CPTP half-diamond smoothing of generalized robustness.
--   - `constantRelativeRadius`: PDF p.15, Eq.(68): all block constant references, including correlated outputs.
--   - `constantMaxRadius`: PDF p.15: smooth max-divergence radius over all constant references.
--   - `roundedInfoCost`: PDF pp.6,9: rounding is computed from the real information value.
--   - `roundingCorrection`: PDF p.9, Eq.(32): the least rounding correction, not a free variable.
--   - `roundedTraceCost`: PDF p.6, Eq.(17): root, then ceiling, then binary logarithm.
--   - `linkChoi`: PDF p.4, Eq.(6d): fully transposed resource Choi linked with code Choi; entries implement all tensor reorderings explicitly.
--   - `NSChoi`: PDF p.4, Eqs.(6e)--(6g): both NS marginals in the fixed register order.
--   - `codeBobTranspose`: PDF p.4: transpose Bob input AND output in the code Choi matrix.
--   - `generalErrorFeasible`: PDF p.4, SDP (6): a fully bound matrix-variable feasible set.
--   - `reducedErrorFeasible`: PDF p.5, SDP (9): noiseless reduction, with m=1 retained.
--   - `traceFeasible`: PDF p.6, SDP (17): optimize Tr V before rounding.
--   - `traceValue`: PDF p.6: real SDP value; the theorem domain has a nonempty, bounded-below feasible set with objective at least one.
--   - `zeroTraceValue`: PDF p.7, Eq.(19): independent zero-error primal objective.
--   - `basisDepolarizing`: PDF p.13: Depolarizing map extended linearly to all operators.
--   - `ZeroErrorWitnessPair`: PDF pp.13--14, Eqs.(57)--(62): explicit primal and dual feasibility, with both objectives equal to the independently defined zero-error primal optimum.
--   - `depolarizingPrimalWitness`: PDF p.13, Eq.(59): constructed depolarizing primal optimizer.
--   - `dampingPrimalWitness`: PDF p.14, Eq.(62): constructed damping primal optimizer; false/true are 0/1.
--   - `flaggedErasureChannel`: PDF p.14, Example 5: orthogonal flag none; some a are the data basis. The trace factor is required on non-normalized operators.
--   - `classicalMap`: PDF p.18: embed a classical stochastic channel as a quantum map.
--   - `classicalFeasible`: PDF p.18, LP (69): error constraints are for every input, not averaged.
--   - `classicalValue`: PDF p.18: classical LP trace objective.
--   - `depolarizingSectorSum`: PDF p.18, Eq.(70): Sector is a SUM, preserving binomial multiplicities.
--   - `sectorMatrix`: PDF p.18, Eq.(71): matrices constructed from the sector coefficients.
--   - `sectorWeight`: PDF p.18, Eq.(72): partial trace weights with k=0 and k=n included.
--   - `sectorEigenvalue`: PDF p.18: eigenvalue of the target Choi matrix on sector k.
--   - `depolarizingFeasible`: PDF p.18, LP (72): concrete finite coefficient feasible set.
--   - `depolarizingValue`: PDF p.18: objective d^n s, before square root and integer ceiling.
--   - `deFinetti`: PDF pp.11,20: the Haar pure-state n-th moment is the normalized symmetric projector on (AA')^n. The finite permutation formula constructs that projector, with rank choose(|A|^2+n-1,n). The same identity is stated in [43], arXiv:0809.3019v1, p.2, proof of Lemma 2.
--   - `deFinettiPurification`: PDF p.20: canonical purification of the constructed de Finetti state, regrouped as (R A^n) A'^n; all of R A^n is the untouched reference.
--   - `PermutationCovariantChannel`: PDF pp.11,20: covariance, equivalently inverse input conjugation. SOURCE NOTATION REPAIR: the printed same-forward pi on both sides does not fix tensor powers for a 3-cycle; the proof uses this covariance relation.
--   - `deFinettiK1`: PDF p.20, Eq.(85): independently constructed fixed-marginal state set.
--   - `deFinettiK2`: PDF p.20, Eq.(86): independently constructed image of covariant CPTP maps.
--   - `infoOnSet`: PDF p.20, Eq.(84): extended infimum on the displayed state set.
-- source:
--   Quantum Channel Simulation and the Channel's Smooth Max-Information, arXiv:1807.05354v2, https://arxiv.org/abs/1807.05354v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P09
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_QAlgorithms_Papers_Independent_Independent2_P01
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P06
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P71
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P39

/-! Fang--Wang--Tomamichel--Berta, arXiv:1807.05354v2.
Finite positive-dimensional systems with fixed computational bases. All logarithms
are binary. Exact accepted definitions are selectively imported; distinct simulation objects
have complete local bodies. Paper results have sorry proofs.
The three false printed assertions are recorded in HARD.md. Compilation and
independent moderation remain pending the batch handoff. -/

noncomputable section

open Filter QAlgorithms
open scoped BigOperators Matrix ComplexConjugate ComplexOrder Topology

namespace QAlgorithms.Papers.Independent.Intakethird100.P65

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P09 (transposeBob)
open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)
open QAlgorithms.Papers.Independent.Independent2.P01 (dampingKraus damping)
open QAlgorithms.Papers.Independent.Gap48.P33 (phaseFlipChannel)
open QAlgorithms.Papers.Independent.Information100.P06 (Below)
open QAlgorithms.Papers.Independent.Information100.P34 (choi)
open QAlgorithms.Papers.Independent.Information100.P62 (Stochastic)
open QAlgorithms.Papers.Independent.Information100.P63 (Mat)
open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized purifiedDistance)
open QAlgorithms.Papers.Independent.Information100.P69 (replacer permute)
open QAlgorithms.Papers.Independent.Information100.P71 (diamond channelPower channelRelative)
open QAlgorithms.Papers.Independent.Support50.P39 (quantumMutualInformation)

variable {A B C D R : Type} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]

/-- PDF p.7: a subnormalized closed purified-distance ball. -/
def StateBall (rho sigma : Mat A) (e : ℝ) : Prop :=
  IsSubnormalized sigma ∧ purifiedDistance rho sigma ≤ e

/-- PDF p.7, Eq.(24): optimize normalized B, keeping the actual A marginal. -/
def maxInfo (rho : Mat (A × B)) : EReal :=
  sInf {v : EReal | ∃ sigma : Mat B, IsDensityMatrix sigma ∧
    v = maxRelative rho (Matrix.kronecker (traceRight rho) sigma)}

/-- PDF p.10, Eq.(45): free smoothing, using each candidate's own marginal. -/
def smoothInfo (rho : Mat (A × B)) (e : ℝ) : EReal :=
  sInf {v : EReal | ∃ tau : Mat (A × B), StateBall rho tau e ∧ v = maxInfo tau}

/-- PDF p.10, Eq.(46): hatted smoothing fixes the entire reference marginal. -/
def fixedSmoothInfo (rho : Mat (A × B)) (e : ℝ) : EReal :=
  sInf {v : EReal | ∃ tau : Mat (A × B), StateBall rho tau e ∧
    traceRight tau = traceRight rho ∧ v = maxInfo tau}

/-- PDF p.19, Eq.(76): tilde smoothing fixes only the reference in Dmax. -/
def referenceSmoothInfo (rho : Mat (A × B)) (e : ℝ) : EReal :=
  sInf {v : EReal | ∃ tau : Mat (A × B), StateBall rho tau e ∧
    ∃ sigma : Mat B, IsDensityMatrix sigma ∧
      v = maxRelative tau (Matrix.kronecker (traceRight rho) sigma)}

/-- PDF p.8: normalized maximally entangled state. Only nonempty A is used. -/
def maxEntangledInput (A : Type) [Fintype A] [DecidableEq A] : Mat (A × A) :=
  fun x y => if x.1 = x.2 ∧ y.1 = y.2 then (Fintype.card A : ℂ)⁻¹ else 0

/-- PDF pp.8,10: canonical purification of rho, without a full-rank restriction. -/
def purify (rho : Mat A) : Mat (A × A) :=
  let v : A × A → ℂ := fun x => cfc Real.sqrt rho x.1 x.2
  fun x y => v x * conj (v y)

/-- PDF p.8, Definition 4: max-information of the normalized Choi state.
For CPTP maps on positive-dimensional systems the extended value is finite. -/
def channelInfo (N : Superop A B) : ℝ :=
  (maxInfo (idTensorSuperop (R := A) N (maxEntangledInput A))).toReal

/-- PDF p.3, Eq.(1): HALF the full diamond norm. -/
def halfDiamondDistance (N M : Superop A B) : ℝ := diamond (fun X => N X - M X) / 2

/-- PDF p.8, Definition 5: same-dimensional CPTP channel smoothing. -/
def smoothChannelInfo (N : Superop A B) (e : ℝ) : ℝ :=
  sInf {v : ℝ | ∃ M : Superop A B, IsChannel M ∧ halfDiamondDistance M N ≤ e ∧ v = channelInfo M}

/-- PDF pp.2--3: no-signalling is defined on the operation, independently of
its Choi constraints. Both directional marginal maps are channels. -/
def BipartiteNSOperation (P : Superop (A × C) (B × D)) : Prop :=
  IsChannel P ∧
  (∃ F : Superop A B, IsChannel F ∧ ∀ X, traceRight (P X) = F (traceRight X)) ∧
  (∃ G : Superop C D, IsChannel G ∧ ∀ X, traceLeft (P X) = G (traceLeft X))

/-- PDF p.3: complete positivity of the transpose-conjugated operation. -/
def PPTCode (P : Superop (A × C) (B × D)) : Prop :=
  IsChannel (fun X => transposeBob (P (transposeBob X)))

/-- PDF pp.2--3: entanglement-assisted local encoding and decoding with an
arbitrary finite shared density. The body is the contraction of these local maps,
not a no-signalling or entropy assumption. -/
def EntCode (P : Superop (A × C) (B × D)) : Prop :=
  ∃ e f : ℕ, 0 < e ∧ 0 < f ∧
  ∃ eta : Mat (Fin e × Fin f), IsDensityMatrix eta ∧
  ∃ E : Superop (A × Fin e) B, IsChannel E ∧
  ∃ F : Superop (C × Fin f) D, IsChannel F ∧
  ∀ X b d,
    P X b d = ∑ i, ∑ j, ∑ u, ∑ v, ∑ a, ∑ c, ∑ s, ∑ t,
      X (i, u) (j, v) * eta (a, s) (c, t) *
      E (Matrix.single (i, a) (j, c) 1) b.1 d.1 *
      F (Matrix.single (u, s) (v, t) 1) b.2 d.2

/-- Assistance classes in PDF pp.3,10. -/
inductive SimulationAssistance where
  | ns | nsPpt | ent
  deriving DecidableEq

/-- Membership in the source's independently operational code classes. -/
def AllowedSimulationCode (o : SimulationAssistance) (P : Superop (A × C) (B × D)) : Prop :=
  match o with
  | .ns => BipartiteNSOperation P
  | .nsPpt => BipartiteNSOperation P ∧ PPTCode P
  | .ent => EntCode P

/-- PDF pp.2--3: connect Ao to Bi through N by matrix-unit expansion of the
operations on arbitrary input X. This is independent of the Choi link formula. -/
def wire (N : Superop B C) (P : Superop (A × C) (B × D)) : Superop A D :=
  fun X b d => ∑ a, ∑ c, ∑ u, ∑ v,
    N (Matrix.single a c 1) u v *
      P (Matrix.kronecker X (Matrix.single u v 1)) (a, b) (c, d)

/-- PDF p.3, Eq.(1): optimize the half-diamond error over actual codes.
On the source domain the feasible set is nonempty and errors lie in [0,1]. -/
def minimumError (o : SimulationAssistance) (N : Superop B C) (M : Superop A D) : ℝ :=
  sInf {v : ℝ | ∃ P : Superop (A × C) (B × D), AllowedSimulationCode o P ∧
    v = halfDiamondDistance (wire N P) M}

/-- PDF p.4, Eq.(4): cost of one use of an integer-dimensional noiseless channel.
Positive resource dimensions include m=1. -/
def oneUseSimulationCost (o : SimulationAssistance) (N : Superop A B) (e : ℝ) : ℝ :=
  sInf {v : ℝ | ∃ m : ℕ, 0 < m ∧
    minimumError o (fun X : Mat (Fin m) => X) N ≤ e ∧ v = Real.logb 2 m}

/-- PDF pp.4,10: operational vanishing-error simulation rates, with rate slack
before blocklength. No entropy formula enters this definition. -/
def SimulationRate (o : SimulationAssistance) (N : Superop A B) (r : ℝ) : Prop :=
  0 ≤ r ∧ ∀ e : ℝ, 0 < e → ∀ slack : ℝ, 0 < slack →
    ∃ n0 : ℕ, ∀ n ≥ n0, 0 < n → ∃ m : ℕ, 0 < m ∧
      minimumError o (fun X : Mat (Fin m) => X) (channelPower N n) ≤ e ∧
      Real.logb 2 m ≤ (r + slack) * n

/-- PDF p.10: operational vanishing-error communication rates. -/
def CommunicationRate (o : SimulationAssistance) (N : Superop A B) (r : ℝ) : Prop :=
  0 ≤ r ∧ ∀ e : ℝ, 0 < e → ∀ slack : ℝ, 0 < slack →
    ∃ n0 : ℕ, ∀ n ≥ n0, 0 < n → ∃ m : ℕ, 0 < m ∧
      minimumError o (channelPower N n) (fun X : Mat (Fin m) => X) ≤ e ∧
      (r - slack) * n ≤ Real.logb 2 m

/-- PDF pp.4,10: infimum of operational simulation rates; extended at empty sets. -/
def vanishingErrorSimulationCost (o : SimulationAssistance) (N : Superop A B) : EReal :=
  sInf {v : EReal | ∃ r : ℝ, SimulationRate o N r ∧ v = (r : EReal)}

/-- PDF p.10: supremum of operational communication rates, independently defined. -/
def vanishingErrorQuantumCapacity (o : SimulationAssistance) (N : Superop A B) : EReal :=
  sSup {v : EReal | ∃ r : ℝ, CommunicationRate o N r ∧ v = (r : EReal)}

/-- PDF p.7, Eq.(20): zero error is fixed before the blocklength limit.
The threshold-rate form avoids assigning a default value to a nonexistent limit. -/
def zeroErrorCost (N : Superop A B) : ℝ :=
  sInf {r : ℝ | ∀ slack : ℝ, 0 < slack → ∃ n0 : ℕ, ∀ n ≥ n0, 0 < n →
    oneUseSimulationCost .ns (channelPower N n) 0 / n ≤ r + slack}

/-- PDF p.10, Eq.(43): optimize over ALL input densities, including singular ones. -/
def channelMutualInfo (N : Superop A B) : ℝ :=
  sSup {v : ℝ | ∃ rho : Mat A, IsDensityMatrix rho ∧
    v = quantumMutualInformation (idTensorSuperop N (purify rho))}

/-- PDF pp.10--12: actual successive limits, with positive blocklength and
right-hand epsilon limit. In particular no liminf or totalized limit is substituted. -/
def IteratedLimit (f : ℝ → ℕ → ℝ) (value : ℝ) : Prop :=
  ∃ L : ℝ → ℝ,
    (∀ e : ℝ, 0 < e → e < 1 → Tendsto (fun n => f e (n + 1)) atTop (nhds (L e))) ∧
    Tendsto L (nhdsWithin 0 (Set.Ioi 0)) (nhds value)

/-- PDF p.9, Eq.(35): all constant channels, not only full-support outputs. -/
def Constant (M : Superop A B) : Prop :=
  ∃ sigma : Mat B, IsDensityMatrix sigma ∧ M = replacer sigma

/-- PDF p.9, Eq.(37): smooth N over CPTP maps, with fixed reference M. -/
def smoothChannelDmax (N M : Superop A B) (e : ℝ) : EReal :=
  sInf {v : EReal | ∃ T : Superop A B, IsChannel T ∧
    halfDiamondDistance T N ≤ e ∧ v = maxRelative (choi T) (choi M)}

/-- PDF p.9, Eq.(38): independently defined generalized robustness. Mixing
noise is arbitrary CPTP; only the resulting convex mixture must be constant. -/
def constantChannelRobustness (N : Superop A B) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ ∃ M : Superop A B, IsChannel M ∧
    Constant (fun X => ((1 + t : ℝ)⁻¹ : ℂ) • (N X + (t : ℂ) • M X))}

/-- PDF p.10, Eq.(39): CPTP half-diamond smoothing of generalized robustness. -/
def smoothRobustness (N : Superop A B) (e : ℝ) : ℝ :=
  sInf {v : ℝ | ∃ T : Superop A B, IsChannel T ∧ halfDiamondDistance T N ≤ e ∧ v = constantChannelRobustness T}

/-- PDF p.15, Eq.(68): all block constant references, including correlated outputs. -/
def constantRelativeRadius (N : Superop A B) : EReal :=
  sInf {v : EReal | ∃ M : Superop A B, Constant M ∧ v = channelRelative N M}

/-- PDF p.15: smooth max-divergence radius over all constant references. -/
def constantMaxRadius (N : Superop A B) (e : ℝ) : EReal :=
  sInf {v : EReal | ∃ M : Superop A B, Constant M ∧ v = smoothChannelDmax N M e}

/-- PDF pp.6,9: rounding is computed from the real information value. -/
def roundedInfoCost (x : ℝ) : ℝ := Real.logb 2 (Nat.ceil ((2 : ℝ) ^ (x / 2)))

/-- PDF p.9, Eq.(32): the least rounding correction, not a free variable. -/
def roundingCorrection (x : ℝ) : ℝ := roundedInfoCost x - x / 2

/-- PDF p.6, Eq.(17): root, then ceiling, then binary logarithm. -/
def roundedTraceCost (t : ℝ) : ℝ := Real.logb 2 (Nat.ceil (Real.sqrt t))

/-- PDF p.4, Eq.(6d): fully transposed resource Choi linked with code Choi;
entries implement all tensor reorderings explicitly. -/
def linkChoi (J : Mat (B × C)) (Z : Mat ((A × C) × (B × D))) : Mat (A × D) :=
  fun x y => ∑ a, ∑ c, ∑ u, ∑ v,
    J (a, u) (c, v) * Z ((x.1, u), (a, x.2)) ((y.1, v), (c, y.2))

/-- PDF p.4, Eqs.(6e)--(6g): both NS marginals in the fixed register order. -/
def NSChoi (Z : Mat ((A × C) × (B × D))) : Prop :=
  Z.PosSemidef ∧
  (∀ i j u v, (∑ a, ∑ b, Z ((i,u),(a,b)) ((j,v),(a,b))) =
    if i = j ∧ u = v then 1 else 0) ∧
  (∀ i j u v b d, (∑ a, Z ((i,u),(a,b)) ((j,v),(a,d))) =
    if i = j then (Fintype.card A : ℂ)⁻¹ *
      ∑ k, ∑ a, Z ((k,u),(a,b)) ((k,v),(a,d)) else 0) ∧
  (∀ i j u v a c, (∑ b, Z ((i,u),(a,b)) ((j,v),(c,b))) =
    if u = v then (Fintype.card C : ℂ)⁻¹ *
      ∑ w, ∑ b, Z ((i,w),(a,b)) ((j,w),(c,b)) else 0)

/-- PDF p.4: transpose Bob input AND output in the code Choi matrix. -/
def codeBobTranspose (Z : Mat ((A × C) × (B × D))) : Mat ((A × C) × (B × D)) :=
  fun x y => Z ((x.1.1,y.1.2),(x.2.1,y.2.2)) ((y.1.1,x.1.2),(y.2.1,x.2.2))

/-- PDF p.4, SDP (6): a fully bound matrix-variable feasible set. -/
def generalErrorFeasible (ppt : Bool) (N : Superop B C) (M : Superop A D) (g : ℝ) : Prop :=
  ∃ Y : Mat (A × D), ∃ Z : Mat ((A × C) × (B × D)),
    NSChoi Z ∧ (ppt = true → (codeBobTranspose Z).PosSemidef) ∧
    Below (traceRight Y) ((g : ℂ) • (1 : Mat A)) ∧
    Below (linkChoi (choi N) Z - choi M) Y ∧ Y.PosSemidef

/-- PDF p.5, SDP (9): noiseless reduction, with m=1 retained. -/
def reducedErrorFeasible (ppt : Bool) (N : Superop A B) (m : ℕ) (g : ℝ) : Prop :=
  ∃ Y J : Mat (A × B), ∃ V : Mat B, V.IsHermitian ∧
    Below (traceRight Y) ((g : ℂ) • (1 : Mat A)) ∧ Below (J - choi N) Y ∧ Y.PosSemidef ∧
    J.PosSemidef ∧ traceRight J = 1 ∧ Below J (Matrix.kronecker (1 : Mat A) V) ∧
    V.trace.re = (m : ℝ)^2 ∧
    (ppt = true →
      Below (-Matrix.kronecker (1 : Mat A) V.transpose) ((m : ℂ) • transposeBob J) ∧
      Below ((m : ℂ) • transposeBob J) (Matrix.kronecker (1 : Mat A) V.transpose))

/-- PDF p.6, SDP (17): optimize Tr V before rounding. -/
def traceFeasible (N : Superop A B) (e : ℝ) (Y J : Mat (A × B)) (V : Mat B) : Prop :=
  V.IsHermitian ∧ Below (traceRight Y) ((e : ℂ) • (1 : Mat A)) ∧
  Below (J - choi N) Y ∧ Y.PosSemidef ∧ J.PosSemidef ∧ traceRight J = 1 ∧
  Below J (Matrix.kronecker (1 : Mat A) V)

/-- PDF p.6: real SDP value; the theorem domain has a nonempty, bounded-below
feasible set with objective at least one. -/
def traceValue (N : Superop A B) (e : ℝ) : ℝ :=
  sInf {t : ℝ | ∃ Y J : Mat (A × B), ∃ V : Mat B, traceFeasible N e Y J V ∧ t = V.trace.re}

/-- PDF p.7, Eq.(19): independent zero-error primal objective. -/
def zeroTraceValue (N : Superop A B) : ℝ :=
  sInf {t : ℝ | ∃ V : Mat B, V.IsHermitian ∧
    Below (choi N) (Matrix.kronecker (1 : Mat A) V) ∧ t = V.trace.re}

/-- PDF p.13: Depolarizing map extended linearly to all operators. -/
def basisDepolarizing (A : Type) [Fintype A] [DecidableEq A] (p : ℝ) : Superop A A :=
  fun X => ((1 - p : ℝ) : ℂ) • X + ((p : ℂ) * X.trace / Fintype.card A) • (1 : Mat A)

/-- PDF pp.13--14, Eqs.(57)--(62): explicit primal and dual feasibility,
with both objectives equal to the independently defined zero-error primal optimum. -/
def ZeroErrorWitnessPair (N : Superop A B) (V : Mat B) (X : Mat (A × B)) : Prop :=
  V.IsHermitian ∧ Below (choi N) (Matrix.kronecker (1 : Mat A) V) ∧
  X.PosSemidef ∧ Below (traceLeft X) (1 : Mat B) ∧
  V.trace.re = zeroTraceValue N ∧ ((choi N) * X).trace.re = zeroTraceValue N

/-- PDF p.13, Eq.(59): constructed depolarizing primal optimizer. -/
def depolarizingPrimalWitness (A : Type) [Fintype A] [DecidableEq A] (p : ℝ) : Mat A :=
  (((Fintype.card A : ℝ) * (1-p) + p / (Fintype.card A) : ℝ) : ℂ) • (1 : Mat A)

/-- PDF p.14, Eq.(62): constructed damping primal optimizer; false/true are 0/1. -/
def dampingPrimalWitness (r : ℝ) : Mat Bool :=
  Matrix.diagonal (fun b =>
    if b then ((Real.sqrt (1-r) + 1-r : ℝ) : ℂ)
    else ((1 + Real.sqrt (1-r) : ℝ) : ℂ))

/-- PDF p.14, Example 5: orthogonal flag none; some a are the data basis.
The trace factor is required on non-normalized operators. -/
def flaggedErasureChannel (A : Type) [Fintype A] (p : ℝ) : Superop A (Option A) :=
  fun X x y => match x, y with
  | some a, some b => ((1-p : ℝ) : ℂ) * X a b
  | none, none => (p : ℂ) * X.trace
  | _, _ => 0

/-- PDF p.18: embed a classical stochastic channel as a quantum map. -/
def classicalMap (W : A → B → ℝ) : Superop A B :=
  fun X => Matrix.diagonal (fun y => ∑ x, (W x y : ℂ) * X x x)

/-- PDF p.18, LP (69): error constraints are for every input, not averaged. -/
def classicalFeasible (W : A → B → ℝ) (e : ℝ) (Y T : A → B → ℝ) (V : B → ℝ) : Prop :=
  (∀ x y, T x y - W x y ≤ Y x y ∧ 0 ≤ Y x y ∧ 0 ≤ T x y ∧ T x y ≤ V y) ∧
  (∀ x, ∑ y, T x y = 1) ∧ (∀ x, ∑ y, Y x y ≤ e)

/-- PDF p.18: classical LP trace objective. -/
def classicalValue (W : A → B → ℝ) (e : ℝ) : ℝ :=
  sInf {t : ℝ | ∃ Y T : A → B → ℝ, ∃ V : B → ℝ,
    classicalFeasible W e Y T V ∧ t = ∑ y, V y}

/-- PDF p.18, Eq.(70): Sector is a SUM, preserving binomial multiplicities. -/
def depolarizingSectorSum (A : Type) [Fintype A] [DecidableEq A] (n k : ℕ) :
    Mat ((Fin n → A) × (Fin n → A)) :=
  ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
    fun x y => ∏ i : Fin n,
      (if i ∈ S then maxEntangledInput A (x.1 i,x.2 i) (y.1 i,y.2 i)
        else ((1 : Mat (A × A)) - maxEntangledInput A) (x.1 i,x.2 i) (y.1 i,y.2 i))

/-- PDF p.18, Eq.(71): matrices constructed from the sector coefficients. -/
def sectorMatrix (A : Type) [Fintype A] [DecidableEq A] (n : ℕ) (r : Fin (n+1) → ℝ) :
    Mat ((Fin n → A) × (Fin n → A)) :=
  ∑ k, (r k : ℂ) • depolarizingSectorSum A n k.val

/-- PDF p.18, Eq.(72): partial trace weights with k=0 and k=n included. -/
def sectorWeight (d n k : ℕ) : ℝ :=
  (n.choose k : ℝ) * (1 / (d : ℝ)) ^ k * ((d : ℝ) - 1 / d) ^ (n-k)

/-- PDF p.18: eigenvalue of the target Choi matrix on sector k. -/
def sectorEigenvalue (d n k : ℕ) (p : ℝ) : ℝ :=
  ((d : ℝ)*(1-p) + p/d)^k * (p/d)^(n-k)

/-- PDF p.18, LP (72): concrete finite coefficient feasible set. -/
def depolarizingFeasible (d n : ℕ) (p e s : ℝ) (y r : Fin (n+1) → ℝ) : Prop :=
  (∀ k, 0 ≤ y k - r k + sectorEigenvalue d n k.val p ∧ 0 ≤ y k ∧ 0 ≤ r k ∧ r k ≤ s) ∧
  (∑ k, sectorWeight d n k.val * r k) = 1 ∧
  (∑ k, sectorWeight d n k.val * y k) ≤ e

/-- PDF p.18: objective d^n s, before square root and integer ceiling. -/
def depolarizingValue (d n : ℕ) (p e : ℝ) : ℝ :=
  sInf {v : ℝ | ∃ s : ℝ, ∃ y r : Fin (n+1) → ℝ,
    depolarizingFeasible d n p e s y r ∧ v = (d : ℝ)^n * s}

/-- PDF pp.11,20: the Haar pure-state n-th moment is the normalized symmetric
projector on (AA')^n. The finite permutation formula constructs that projector,
with rank choose(|A|^2+n-1,n). The same identity is stated in [43],
arXiv:0809.3019v1, p.2, proof of Lemma 2. -/
def deFinetti (A : Type) [Fintype A] [DecidableEq A] (n : ℕ) : Mat (Fin n → A × A) :=
  fun x y =>
    (∑ p : Equiv.Perm (Fin n), if x = y ∘ p then (1 : ℂ) else 0) /
      ((n.factorial : ℂ) * (Nat.choose ((Fintype.card A)^2 + n - 1) n : ℂ))

/-- PDF p.20: canonical purification of the constructed de Finetti state,
regrouped as (R A^n) A'^n; all of R A^n is the untouched reference. -/
def deFinettiPurification (A : Type) [Fintype A] [DecidableEq A] (n : ℕ) :
    Mat (((Fin n → A × A) × (Fin n → A)) × (Fin n → A)) :=
  let v := fun x : ((Fin n → A × A) × (Fin n → A)) × (Fin n → A) =>
    cfc Real.sqrt (deFinetti A n) x.1.1 (fun i => (x.1.2 i, x.2 i))
  fun x y => v x * conj (v y)

/-- PDF pp.11,20: covariance, equivalently inverse input conjugation.
SOURCE NOTATION REPAIR: the printed same-forward pi on both sides does not
fix tensor powers for a 3-cycle; the proof uses this covariance relation. -/
def PermutationCovariantChannel {n : ℕ} (T : Superop (Fin n → A) (Fin n → B)) : Prop :=
  IsChannel T ∧ ∀ p : Equiv.Perm (Fin n), ∀ X, T (permute p X) = permute p (T X)

/-- PDF p.20, Eq.(85): independently constructed fixed-marginal state set. -/
def deFinettiK1 (N : Superop A B) (n : ℕ) (e : ℝ) :
    Set (Mat (((Fin n → A × A) × (Fin n → A)) × (Fin n → B))) :=
  {sigma | IsDensityMatrix sigma ∧
    purifiedDistance sigma (idTensorSuperop (channelPower N n) (deFinettiPurification A n)) ≤ e ∧
    traceRight sigma = traceRight (deFinettiPurification A n)}

/-- PDF p.20, Eq.(86): independently constructed image of covariant CPTP maps. -/
def deFinettiK2 (N : Superop A B) (n : ℕ) (e : ℝ) :
    Set (Mat (((Fin n → A × A) × (Fin n → A)) × (Fin n → B))) :=
  {sigma | ∃ T : Superop (Fin n → A) (Fin n → B), PermutationCovariantChannel T ∧
    sigma = idTensorSuperop T (deFinettiPurification A n) ∧
    purifiedDistance sigma (idTensorSuperop (channelPower N n) (deFinettiPurification A n)) ≤ e}

/-- PDF p.20, Eq.(84): extended infimum on the displayed state set. -/
def infoOnSet (S : Set (Mat (A × B))) : EReal :=
  sInf {v : EReal | ∃ sigma ∈ S, v = maxInfo sigma}

/-! Sanity examples pin local bodies without proving any paper result. -/

example (X : Mat A) : Below X X := by
  simp only [Below, sub_self]
  exact Matrix.PosSemidef.zero

example (sigma : Mat B) (X : Mat A) : replacer sigma X = X.trace • sigma := rfl

example (N : Superop A B) (a c : A) (b d : B) :
    choi N (a,b) (c,d) = N (Matrix.single a c 1) b d := rfl

example (X : Mat (A × B)) (a c : A) (b d : B) :
    transposeBob X (a,b) (c,d) = X (a,d) (c,b) := rfl

example (X : Mat A) : basisDepolarizing A 0 X = X := by simp [basisDepolarizing]

example (p : ℝ) (X : Mat A) : flaggedErasureChannel A p X none none = (p : ℂ) * X.trace := rfl

example : sectorWeight 2 1 0 = 3/2 ∧ sectorWeight 2 1 1 = 1/2 := by
  norm_num [sectorWeight]

example (p : ℝ) (x y : Fin 0 → A) : channelPower (basisDepolarizing A p) 0
    (1 : Mat (Fin 0 → A)) x y = 1 := by
  simp [channelPower, piSuperop, Matrix.one_apply]

example (x y : Fin 0 → A × A) : deFinetti A 0 x y = 1 := by
  have hxy : x = y := Subsingleton.elim _ _
  subst y
  have hp : ∀ p : Equiv.Perm (Fin 0), x = x ∘ p := fun _ => Subsingleton.elim _ _
  simp [deFinetti, hp]
  have hf : Finset.filter (fun (p : Equiv.Perm (Fin 0)) => x = x ∘ p)
      ({1} : Finset (Equiv.Perm (Fin 0))) = ({1} : Finset (Equiv.Perm (Fin 0))) :=
    Finset.filter_eq_self.mpr (fun p _ => hp p)
  simpa only [Finset.card_singleton] using congrArg Finset.card hf

example : depolarizingPrimalWitness (Fin 1) 0 = 1 := by
  norm_num [depolarizingPrimalWitness]

example : dampingPrimalWitness 1 = Matrix.diagonal (fun b : Bool => if b then 0 else 1) := by
  norm_num [dampingPrimalWitness]

/-! Theorem binders: every system is finite and nonempty. -/

variable [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] [Nonempty R]

end QAlgorithms.Papers.Independent.Intakethird100.P65


