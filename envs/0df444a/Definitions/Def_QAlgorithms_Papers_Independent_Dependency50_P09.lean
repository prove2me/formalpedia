-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P09
-- name    : QAlgorithms_Papers_Independent_Dependency50_P09
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T17:47:02.617993+00:00
-- url     : https://prove2.me/theorems/f907912c-84a3-4718-9863-526be1d9ddce
-- title:
--   Definitions for Bounding the forward classical capacity of bipartite quantum channels
-- statement:
--   The objects the formalized statements of *Bounding the forward classical capacity of bipartite quantum channels* (arXiv:2010.01058) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `HP`: Complex-linear Hermiticity-preserving maps (PDF pp.4,24).
--   - `tensorAction`: Heterogeneous tensor product on the full matrix-unit expansion, PDF pp.3,6.
--   - `stableMap`: Identity local extensions, regrouped by party; PDF pp.5-6.
--   - `transposeBob`: Partial transpose on the second factor, PDF p.3 (6).
--   - `transposeBobChoi`: Bob-input AND Bob-output transpose in input-first wire order, PDF p.4 (16).
--   - `ChoiNS`: No Alice-to-Bob signaling in Choi coordinates; PDF p.4 (16). The source's A,A',B,B' ordering is reindexed to (A,B),(A',B').
--   - `BetaFeasible`: The actual Choi feasible set, with both signs, PDF p.4 (16).
--   - `bipartiteBeta`: Extended infimum of the source Choi objective, PDF p.4 (16).
--   - `logExt`: Extended base-two logarithm: zero has value minus infinity, PDF p.4 (15).
--   - `cBeta`: C_beta on arbitrary CP maps, including zero, PDF p.4 (15).
--   - `pointMap`: Embed a point channel with trivial Bob input and Alice output, PDF p.10.
--   - `feedbackMap`: Classical feedback with trivial Alice input and Bob output, PDF p.6 (70).
--   - `comparator`: Computational comparator, PDF p.11 (198).
--   - `classicalPhi`: Maximally CLASSICALLY correlated density, PDF p.11 (196).
--   - `entangledPhi`: Normalized maximally entangled density, PDF p.3 (1)-(3).
--   - `pointBetaChoi`: Point-channel Choi program, without a trace bound on S, PDF pp.10-11 (187).
--   - `resetAlice`: Replacing Alice's input by the maximally mixed state, PDF p.3 (14).
--   - `discardAlice`: Discard Alice's output, PDF p.3 (14).
--   - `BetaMapFeasible`: The map feasible set, independently of the Choi program, PDF p.24 (364).
--   - `inducedTraceNorm`: Induced trace norm on feasible CP maps, PDF p.24 (359)-(362). This density supremum is the source's CP expression, not a diamond norm.
--   - `betaMapValue`: The independent map optimization, PDF p.24 (363)-(364).
--   - `pointBetaMap`: Point-map optimization with arbitrary PSD output S, PDF p.24 (368).
--   - `Divergence`: State divergences on normalized first arguments and arbitrary PSD comparisons, PDF p.9.
--   - `relativeD`: Umegaki entropy in BITS, retaining negative values for unnormalized sigma, PDF p.9 (148).
--   - `bsD`: Belavkin-Staszewski entropy, with support failure infinite, PDF p.9 (153).
--   - `petzD`: Petz entropy, with its below/above-one support conventions, PDF p.25 (398).
--   - `sandwichedD`: Sandwiched entropy, PDF p.9 (149)-(150), CORRECTED exponent (1-alpha)/(2 alpha). The printed extra minus contradicts (144),(152); at rho=sigma=I/d it gives -2 log2 d.
--   - `geometricD`: Regularized geometric entropy, PDF p.9 (154). The EReal liminf equals the printed limit on lawful arguments and preserves all support-failure values.
--   - `channelD`: Channel divergence with ALL finite reference dimensions and ALL density inputs, PDF p.9 (159); no pure-input reduction is presumed outside DPI ranges.
--   - `LawfulD`: Literal generalized-divergence axioms, PDF pp.8-9 (142)-(144). There is deliberately no scalar-zero nonnegativity axiom.
--   - `upsilon`: Upsilon minimizes over ALL CP comparisons, including zero, PDF p.9 (161).
--   - `pointUpsilon`: One-use point-channel Upsilon, via trivial ports, PDF p.11 (194).
--   - `regularizedD`: Positive-block regularization of EACH divergence, PDF p.16 (297). Use liminf of the normalized sequence, equal to the source limit for channel N, CP M.
--   - `upsilonReg`: Regularize before optimizing over a single-use CP comparison, PDF p.17 (301).
--   - `penalty`: Extended finite-error penalty; epsilon=1 has value +infinity, PDF pp.14-15.
--   - `Slot`: A bipartite channel slot; validity is imposed on the actual slots used by a code. Dimensions are natural numbers, with positivity required in AdaptiveCode.Valid (PDF pp.12-15).
--   - `Slot.Positive`: Positive-dimensional ports, PDF p.3.
--   - `fixedSlot`: Repeated-channel slot, PDF pp.12-14.
--   - `memoryCall`: A channel call acting on the two ports while preserving arbitrary local memories, including all their off-diagonal blocks, PDF p.13 (238)-(243).
--   - `AdaptiveCode`: The source adaptive code, PDF pp.12-13 (235)-(251). All operations are chosen before the message distribution. Extra indices beyond n are unused extensions. After each call local CPTP maps feed the next slot; after the last call they can prepare arbitrary dummy input ports before Bob's final decoder.
--   - `AdaptiveCode.Valid`: Lawful code: independent normalized Bob state, CPTP local operations, no initial shared resource, positive memories/ports, and exactly the first n calls (PDF pp.12-13).
--   - `AdaptiveCode.state`: The actual dependent state recurrence for each message, PDF p.13 (238)-(244).
--   - `AdaptiveCode.output`: Bob's conditional decoded density (Alice is discarded), PDF p.13 (244).
--   - `AdaptiveCode.cq`: Message/reference cq state, PDF p.12 (235), p.13 (248).
--   - `idealCQ`: Ideal message/reference correlation for the SAME distribution, PDF p.13 (246).
--   - `AdaptiveCode.error`: Trace-distance error, PDF p.13 (245),(257).
--   - `AdaptiveCode.ErrorAtMost`: Maximum error quantifies over p AFTER choosing P; RT fixes uniform p, PDF p.13.
--   - `codeCapacity`: Operational finite-use supremum, PDF p.13 (252),(259), p.15 (283). `calls` counts actual slots; `denom` counts forward calls when feedback slots are free.
--   - `finiteCapacity`: Finite-use bipartite classical/RT capacity, PDF p.13 (252),(259).
--   - `capacityOf`: inf-error liminf capacity, with positive n indexed by k+1, PDF pp.13-14.
--   - `strongCapacityOf`: sup-error limsup strong-converse capacity, PDF pp.13-14.
--   - `forwardCapacity`: Unassisted forward classical capacity, PDF p.13 (253).
--   - `randomnessCapacity`: Unassisted forward RT capacity, PDF p.14 (260).
--   - `classicalStrong`: Strong-converse classical capacity, PDF p.13 (254).
--   - `randomnessStrong`: Strong-converse RT capacity, PDF p.14 (261).
--   - `Backward`: A rectangular backward channel, PDF p.16, with trivial opposite ports.
--   - `Backward.slot`: Embed a backward channel in the bipartite model, PDF p.15.
--   - `feedbackSlots`: Alternating backward and forward slots, PDF p.15 (282). Zero-based even slots are backward; odd slots are forward.
--   - `classicalBackward`: Classical feedback alphabets may vary and are arbitrarily large but finite, PDF p.15.
--   - `feedbackFinite`: n forward uses with free classical feedback in n backward slots, PDF p.15 (283). The fixed code is selected before universally testing message distributions.
--   - `feedbackCapacity`: Feedback-assisted inf-error liminf capacity, PDF p.15 (284).
--   - `feedbackStrong`: Feedback-assisted sup-error limsup capacity, PDF p.15 (285).
--   - `Backward.IsEB`: Rectangular EB channels: reference can be any finite size, PDF p.16. CPTP is explicit; normalized separability follows from the output trace one.
--   - `ebFinite`: Operational capacity allowing arbitrary EB feedback in each slot, PDF p.16.
--   - `unitaryChannel`: Local unitary conjugations, PDF p.8 (134).
--   - `Representation`: Unitary representation laws, PDF p.17.
--   - `OneDesign`: Unitary one-design as equality on EVERY operator, PDF p.17 (305)-(306).
--   - `BiCovariant`: Covariance for fixed representations, distinct from the one-design condition, PDF p.17 (304). All equalities are on all operators.
--   - `inputTwirl`: Independent input twirl, PDF p.17 (308).
--   - `invariantInputD`: Restricted supremum over pure inputs with invariant MARGINAL (not invariant vector), PDF p.17 (307)-(308). Reference is input-sized.
--   - `symmetricUpsilon`: Same-representation comparator restriction; PDF p.17 (307).
--   - `choiUpsilon`: Choi-state version of the same comparator optimization, PDF p.17 (309). The normalized entangled state on AB purifies pi_A tensor pi_B.
--   - `HasBiDesign`: Existence of finite independent one-design symmetries, PDF pp.17-18. Every finite group can be relabeled onto Fin g; Group instances enforce nonemptiness.
--   - `HasPointDesign`: Point covariance with an input ONE-DESIGN, PDF pp.18-19 (332).
--   - `partialSwap`: Partial swap U_p=sqrt(1-p)I+i sqrt(p)Swap; PDF p.19 (335)-(338).
--   - `erasureFin`: Relabel the rectangular erasure output to Fin(d+1), retaining the distinguished orthogonal flag; PDF p.21 (350).
--   - `correlatedUnitary`: Continuous U tensor U action, PDF p.20 (339).
--   - `haarInput`: Normalized Haar state twirl, PDF p.20 (339). Matrix integrands are continuous on the compact unitary group, so they are integrable for the probability Haar law.
--   - `haarMap`: Normalized correlated map twirl; NOT an independent product-group twirl, PDF p.20 (341). For CP M linearity implies continuity of the integrand.
--   - `haarChoi`: Input conjugate U,U and output U,U Choi action in input-first order, PDF p.20 (342). Integration uses the normalized probability Haar law.
--   - `haarUpsilon`: The Haar-restricted minimax, PDF p.20 (339)-(342).
--   - `MapCoefficients`: Finite-dimensional coordinates for the topology of complex-linear maps, PDF p.28. Every coefficient is the image of an input matrix unit.
--   - `coeffMap`: Reconstruct the actual linear superoperator from its coefficients, PDF p.28.
--   - `ChannelPair`: Lawful channel/CP pair domain with the subspace finite-dimensional topology, PDF p.28, Lemma 37.
--   - `pairD`: Joint channel divergence on that domain, PDF p.28.
--   - `orderOne`: The positive-order two-sided punctured approach to one, PDF pp.25-28.
--   - `exp2Ext`: Extended base-two exponential, PDF p.26 (429).
--   - `geometricNu`: Extended geometric continuity parameter, PDF p.26 (429).
--   - `GeometricDelta`: The OPEN parameter domain, PDF p.26 (428). Infinite nu admits no positive delta; no toReal default at infinity is used to manufacture a finite threshold.
--   - `pointPhiInf`: Compare the fixed classical correlation against all beta-feasible CP outputs, PDF pp.11-12 (213)-(214).
-- source:
--   Bounding the forward classical capacity of bipartite quantum channels, arXiv:2010.01058v3, https://arxiv.org/abs/2010.01058v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P06
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P58
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P71

/-! Statements from Ding et al., arXiv:2010.01058v3. All pages are PDF pages.
Information100 imports are pinned accepted libraries. Selective opens reuse exact
operator, CP, Choi, spectral, trace, testing and example-channel interfaces.
Distinct paper-specific objects remain local; ASSESSMENT.json records the matches.
The printed extra minus in (149)-(150) is corrected to (1-alpha)/(2 alpha).
Source-ambiguous nodes are listed separately in HARD.md; no substitute theorem is asserted.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.Elementwise
open Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P09

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open QAlgorithms.Papers.Independent.Information100.P69 (CP)
open QAlgorithms.Papers.Independent.Information100.P34 (choi)
open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)
open QAlgorithms.Papers.Independent.Information100.P06 (traceOutput)
open QAlgorithms.Papers.Independent.Information100.P58 (testingD singleErasure)
open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)
open QAlgorithms.Papers.Independent.Information100.P04 (werner)

/-- Complex-linear Hermiticity-preserving maps (PDF pp.4,24). -/
def HP {I J : Type} [Fintype I] [Fintype J] (M : Superop I J) : Prop :=
  (∃ L : Op I →ₗ[ℂ] Op J, ∀ X, M X = L X) ∧
    ∀ X, X.IsHermitian → (M X).IsHermitian

/-- Heterogeneous tensor product on the full matrix-unit expansion, PDF pp.3,6. -/
def tensorAction {A B C D : Type} [Fintype A] [Fintype B]
    (E : Superop A C) (F : Superop B D) : Superop (A × B) (C × D) :=
  fun X p q => ∑ a, ∑ aa, ∑ b, ∑ bb,
    X (a,b) (aa,bb) * E (Matrix.single a aa 1) p.1 q.1 *
      F (Matrix.single b bb 1) p.2 q.2

/-- Identity local extensions, regrouped by party; PDF pp.5-6. -/
def stableMap {A B C D E F : Type} (M : Superop (A × B) (C × D)) :
    Superop ((E × A) × (B × F)) ((E × C) × (D × F)) :=
  fun X p q => M (fun u v => X ((p.1.1,u.1),(u.2,p.2.2))
    ((q.1.1,v.1),(v.2,q.2.2))) (p.1.2,p.2.1) (q.1.2,q.2.1)

/-- Partial transpose on the second factor, PDF p.3 (6). -/
def transposeBob {A B : Type} (X : Op (A × B)) : Op (A × B) :=
  fun p q => X (p.1,q.2) (q.1,p.2)

/-- Bob-input AND Bob-output transpose in input-first wire order, PDF p.4 (16). -/
def transposeBobChoi {A B C D : Type} (X : Op ((A × B) × (C × D))) :
    Op ((A × B) × (C × D)) :=
  fun p q => X ((p.1.1,q.1.2),(p.2.1,q.2.2))
    ((q.1.1,p.1.2),(q.2.1,p.2.2))

/-- No Alice-to-Bob signaling in Choi coordinates; PDF p.4 (16).
The source's A,A',B,B' ordering is reindexed to (A,B),(A',B'). -/
def ChoiNS {A B C D : Type} [Fintype A] [Fintype C]
    (S : Op ((A × B) × (C × D))) : Prop :=
  ∀ a aa b bb d dd,
    (∑ c, S ((a,b),(c,d)) ((aa,bb),(c,dd))) =
      (if a = aa then (Fintype.card A : ℂ)⁻¹ else 0) *
        ∑ x : A, ∑ c : C, S ((x,b),(c,d)) ((x,bb),(c,dd))

/-- The actual Choi feasible set, with both signs, PDF p.4 (16). -/
def BetaFeasible {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (M : Superop (A × B) (C × D)) (S V : Op ((A × B) × (C × D))) : Prop :=
  S.IsHermitian ∧ V.IsHermitian ∧
  (transposeBobChoi (V + choi M)).PosSemidef ∧
  (transposeBobChoi (V - choi M)).PosSemidef ∧
  (S + V).PosSemidef ∧ (S - V).PosSemidef ∧ ChoiNS S

/-- Extended infimum of the source Choi objective, PDF p.4 (16). -/
def bipartiteBeta {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (M : Superop (A × B) (C × D)) : EReal :=
  sInf {r | ∃ S V, BetaFeasible M S V ∧ r = (specNorm (traceOutput S) : EReal)}

/-- Extended base-two logarithm: zero has value minus infinity, PDF p.4 (15). -/
def logExt (x : EReal) : EReal :=
  if x = ⊤ then ⊤ else if x ≤ 0 then ⊥ else (Real.logb 2 x.toReal : EReal)

/-- C_beta on arbitrary CP maps, including zero, PDF p.4 (15). -/
def cBeta {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (M : Superop (A × B) (C × D)) : EReal := logExt (bipartiteBeta M)

/-- Embed a point channel with trivial Bob input and Alice output, PDF p.10. -/
def pointMap {A D : Type} (M : Superop A D) :
    Superop (A × Fin 1) (Fin 1 × D) :=
  fun X p q => M (fun i j => X (i,0) (j,0)) p.2 q.2

/-- Classical feedback with trivial Alice input and Bob output, PDF p.6 (70). -/
def feedbackMap (d : ℕ) : Superop (Fin 1 × Fin d) (Fin d × Fin 1) :=
  fun X p q => if p.1 = q.1 then X (0,p.1) (0,p.1) else 0

/-- Computational comparator, PDF p.11 (198). -/
def comparator {I : Type} : Op (I × I) :=
  fun p q => if p = q ∧ p.1 = p.2 then 1 else 0

/-- Maximally CLASSICALLY correlated density, PDF p.11 (196). -/
def classicalPhi (I : Type) [Fintype I] : Op (I × I) :=
  (Fintype.card I : ℂ)⁻¹ • comparator

/-- Normalized maximally entangled density, PDF p.3 (1)-(3). -/
def entangledPhi (I : Type) [Fintype I] : Op (I × I) :=
  fun p q => if p.1 = p.2 ∧ q.1 = q.2 then (Fintype.card I : ℂ)⁻¹ else 0

/-- Point-channel Choi program, without a trace bound on S, PDF pp.10-11 (187). -/
def pointBetaChoi {A D : Type} [Fintype A] [Fintype D]
    (M : Superop A D) : EReal :=
  sInf {r | ∃ S : Op D, ∃ V : Op (A × D),
    S.IsHermitian ∧ V.IsHermitian ∧
    (transposeBob (V + choi M)).PosSemidef ∧
    (transposeBob (V - choi M)).PosSemidef ∧
    (Matrix.kronecker (1 : Op A) S + V).PosSemidef ∧
    (Matrix.kronecker (1 : Op A) S - V).PosSemidef ∧ r = (S.trace.re : EReal)}

/-- Replacing Alice's input by the maximally mixed state, PDF p.3 (14). -/
def resetAlice {A B : Type} [Fintype A] (X : Op (A × B)) : Op (A × B) :=
  fun p q => (if p.1 = q.1 then (Fintype.card A : ℂ)⁻¹ else 0) *
    ∑ a : A, X (a,p.2) (a,q.2)

/-- Discard Alice's output, PDF p.3 (14). -/
def discardAlice {A B : Type} [Fintype A] (X : Op (A × B)) : Op B :=
  fun b bb => ∑ a : A, X (a,b) (a,bb)

/-- The map feasible set, independently of the Choi program, PDF p.24 (364). -/
def BetaMapFeasible {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (M S V : Superop (A × B) (C × D)) : Prop :=
  HP S ∧ HP V ∧
  CP (fun X => transposeBob (V (transposeBob X) + M (transposeBob X))) ∧
  CP (fun X => transposeBob (V (transposeBob X) - M (transposeBob X))) ∧
  CP (fun X => S X + V X) ∧ CP (fun X => S X - V X) ∧
  ∀ X, discardAlice (S X) = discardAlice (S (resetAlice X))

/-- Induced trace norm on feasible CP maps, PDF p.24 (359)-(362).
This density supremum is the source's CP expression, not a diamond norm. -/
def inducedTraceNorm {I J : Type} [Fintype I] [Fintype J]
    (S : Superop I J) : EReal :=
  sSup {r | ∃ rho : Op I, IsDensityMatrix rho ∧ r = ((S rho).trace.re : EReal)}

/-- The independent map optimization, PDF p.24 (363)-(364). -/
def betaMapValue {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (M : Superop (A × B) (C × D)) : EReal :=
  sInf {r | ∃ S V, BetaMapFeasible M S V ∧ r = inducedTraceNorm S}

/-- Point-map optimization with arbitrary PSD output S, PDF p.24 (368). -/
def pointBetaMap {A D : Type} [Fintype A] [Fintype D] (M : Superop A D) : EReal :=
  sInf {r | ∃ S : Op D, ∃ V : Superop A D,
    S.PosSemidef ∧ HP V ∧
    CP (fun X => (V X + M X).transpose) ∧
    CP (fun X => (V X - M X).transpose) ∧
    CP (fun X => X.trace • S + V X) ∧ CP (fun X => X.trace • S - V X) ∧
    r = (S.trace.re : EReal)}

example : logExt 0 = ⊥ := by simp [logExt]

example (d : ℕ) (X : Op (Fin 1 × Fin d)) (i : Fin d) :
    feedbackMap d X (i,0) (i,0) = X (0,i) (0,i) := by simp [feedbackMap]

example : classicalPhi (Fin 2) (0,0) (1,1) = 0 := by
  simp [classicalPhi, comparator]

example {A B : Type} (X : Op (A × B)) : transposeBob (transposeBob X) = X := rfl

/-- State divergences on normalized first arguments and arbitrary PSD comparisons, PDF p.9. -/
abbrev Divergence := ∀ {I : Type} [Fintype I] [DecidableEq I], Op I → Op I → EReal

/-- Umegaki entropy in BITS, retaining negative values for unnormalized sigma, PDF p.9 (148). -/
def relativeD : Divergence := fun rho sigma =>
  if SupportIncluded rho sigma then
    (((cfc (fun x : ℝ => x * Real.logb 2 x) rho -
      rho * cfc (Real.logb 2) sigma).trace.re : ℝ) : EReal)
  else ⊤

/-- Belavkin-Staszewski entropy, with support failure infinite, PDF p.9 (153). -/
def bsD : Divergence := fun rho sigma =>
  if SupportIncluded rho sigma then
    let R := supportPower rho (1/2 : ℝ)
    ((rho * cfc (Real.logb 2) (R * supportPower sigma (-1) * R)).trace.re : EReal)
  else ⊤

/-- Petz entropy, with its below/above-one support conventions, PDF p.25 (398). -/
def petzD (alpha : ℝ) : Divergence := fun rho sigma =>
  if 1 < alpha ∧ ¬ SupportIncluded rho sigma then ⊤ else
    ((1 / (alpha - 1) : ℝ) : EReal) *
      logExt (((supportPower rho alpha * supportPower sigma (1-alpha)).trace.re : ℝ) : EReal)

/-- Sandwiched entropy, PDF p.9 (149)-(150), CORRECTED exponent (1-alpha)/(2 alpha).
The printed extra minus contradicts (144),(152); at rho=sigma=I/d it gives -2 log2 d. -/
def sandwichedD (alpha : ℝ) : Divergence := fun rho sigma =>
  if 1 < alpha ∧ ¬ SupportIncluded rho sigma then ⊤ else
    let S := supportPower sigma ((1-alpha)/(2*alpha))
    ((1 / (alpha-1) : ℝ) : EReal) *
      logExt (((supportPower (S * rho * S) alpha).trace.re : ℝ) : EReal)

/-- Regularized geometric entropy, PDF p.9 (154). The EReal liminf equals the printed
limit on lawful arguments and preserves all support-failure values. -/
def geometricD (alpha : ℝ) : Divergence := fun rho sigma =>
  Filter.liminf (fun e : ℝ =>
    let T := sigma + (e : ℂ) • 1
    let S := supportPower T (-1/2 : ℝ)
    ((1 / (alpha-1) : ℝ) : EReal) *
      logExt (((T * supportPower (S * rho * S) alpha).trace.re : ℝ) : EReal))
    (𝓝[>] (0 : ℝ))

/-- Channel divergence with ALL finite reference dimensions and ALL density inputs,
PDF p.9 (159); no pure-input reduction is presumed outside DPI ranges. -/
def channelD {I J : Type} [Fintype I] [Fintype J]
    (D : Divergence) (N M : Superop I J) : EReal :=
  ⨆ r : ℕ, ⨆ rho : {X : Op (Fin r × I) // IsDensityMatrix X},
    D (idTensorSuperop N rho.1) (idTensorSuperop M rho.1)

/-- Literal generalized-divergence axioms, PDF pp.8-9 (142)-(144).
There is deliberately no scalar-zero nonnegativity axiom. -/
def LawfulD (D : Divergence) : Prop :=
  (∀ {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J],
    ∀ (rho sigma : Op I) (N : Superop I J),
    IsDensityMatrix rho → sigma.PosSemidef → IsChannel N → D (N rho) (N sigma) ≤ D rho sigma) ∧
  (∀ c : ℝ, 0 < c → c ≤ 1 →
    0 ≤ D (1 : Op (Fin 1)) ((c : ℂ) • 1)) ∧
  (∀ {I : Type} [Fintype I] [DecidableEq I], ∀ rho : Op I,
    IsDensityMatrix rho → D rho rho = 0)

/-- Upsilon minimizes over ALL CP comparisons, including zero, PDF p.9 (161). -/
def upsilon {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (div : Divergence) (N : Superop (A × B) (C × D)) : EReal :=
  sInf {r | ∃ M, CP M ∧ bipartiteBeta M ≤ 1 ∧ r = channelD div N M}

/-- One-use point-channel Upsilon, via trivial ports, PDF p.11 (194). -/
def pointUpsilon {I J : Type} [Fintype I] [Fintype J]
    (div : Divergence) (N : Superop I J) : EReal := upsilon div (pointMap N)

/-- Positive-block regularization of EACH divergence, PDF p.16 (297).
Use liminf of the normalized sequence, equal to the source limit for channel N, CP M. -/
def regularizedD {I J : Type} [Fintype I] [Fintype J]
    (div : Divergence) (N M : Superop I J) : EReal :=
  Filter.liminf (fun k : ℕ => (((1 : ℝ)/(k+1 : ℕ) : ℝ) : EReal) *
    channelD div (piSuperop (fun _ : Fin (k+1) => N))
      (piSuperop (fun _ : Fin (k+1) => M))) atTop

/-- Regularize before optimizing over a single-use CP comparison, PDF p.17 (301). -/
def upsilonReg {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (div : Divergence) (N : Superop (A × B) (C × D)) : EReal :=
  sInf {r | ∃ M, CP M ∧ bipartiteBeta M ≤ 1 ∧ r = regularizedD div N M}

/-- Extended finite-error penalty; epsilon=1 has value +infinity, PDF pp.14-15. -/
def penalty (alpha epsilon : ℝ) : EReal :=
  ((alpha/(alpha-1) : ℝ) : EReal) * (- logExt ((1-epsilon : ℝ) : EReal))

example : penalty 2 1 = ⊤ := by
  norm_num [penalty, logExt]
  exact EReal.coe_mul_top_of_pos (by norm_num)

example {I : Type} [Fintype I] (rho sigma : Op I)
    (h : ¬ SupportIncluded rho sigma) : relativeD rho sigma = ⊤ := by
  simp [relativeD, h]

/-- A bipartite channel slot; validity is imposed on the actual slots used by a code.
Dimensions are natural numbers, with positivity required in AdaptiveCode.Valid (PDF pp.12-15). -/
structure Slot where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  map : Superop (Fin a × Fin b) (Fin c × Fin d)

/-- Positive-dimensional ports, PDF p.3. -/
def Slot.Positive (s : Slot) : Prop := 0 < s.a ∧ 0 < s.b ∧ 0 < s.c ∧ 0 < s.d

/-- Repeated-channel slot, PDF pp.12-14. -/
def fixedSlot {a b c d : ℕ} (N : Superop (Fin a × Fin b) (Fin c × Fin d)) : Slot :=
  ⟨a,b,c,d,N⟩

/-- A channel call acting on the two ports while preserving arbitrary local memories,
including all their off-diagonal blocks, PDF p.13 (238)-(243). -/
def memoryCall {A B C D E F : Type} (N : Superop (A × B) (C × D)) :
    Superop ((E × A) × (F × B)) ((E × C) × (F × D)) :=
  fun X p q => N (fun u v => X ((p.1.1,u.1),(p.2.1,u.2))
    ((q.1.1,v.1),(q.2.1,v.2))) (p.1.2,p.2.2) (q.1.2,q.2.2)

/-- The source adaptive code, PDF pp.12-13 (235)-(251). All operations are chosen
before the message distribution. Extra indices beyond n are unused extensions.
After each call local CPTP maps feed the next slot; after the last call they can
prepare arbitrary dummy input ports before Bob's final decoder. -/
structure AdaptiveCode (slots : ℕ → Slot) (n M : ℕ) where
  ma : ℕ → ℕ
  mb : ℕ → ℕ
  encode : Superop (Fin M) (Fin (ma 0) × Fin (slots 0).a)
  bobInitial : Op (Fin (mb 0) × Fin (slots 0).b)
  alice : (j : ℕ) → Superop (Fin (ma j) × Fin (slots j).c)
    (Fin (ma (j+1)) × Fin (slots (j+1)).a)
  bob : (j : ℕ) → Superop (Fin (mb j) × Fin (slots j).d)
    (Fin (mb (j+1)) × Fin (slots (j+1)).b)
  decode : Superop (Fin (mb n) × Fin (slots n).b) (Fin M)

/-- Lawful code: independent normalized Bob state, CPTP local operations, no initial
shared resource, positive memories/ports, and exactly the first n calls (PDF pp.12-13). -/
def AdaptiveCode.Valid {s : ℕ → Slot} {n M : ℕ} (P : AdaptiveCode s n M) : Prop :=
  (∀ j ≤ n, 0 < P.ma j ∧ 0 < P.mb j ∧ (s j).Positive) ∧
  IsChannel P.encode ∧ IsDensityMatrix P.bobInitial ∧ IsChannel P.decode ∧
  ∀ j < n, IsChannel (s j).map ∧ IsChannel (P.alice j) ∧ IsChannel (P.bob j)

/-- The actual dependent state recurrence for each message, PDF p.13 (238)-(244). -/
def AdaptiveCode.state {s : ℕ → Slot} {n M : ℕ} (P : AdaptiveCode s n M) (m : Fin M) :
    (j : ℕ) → Op ((Fin (P.ma j) × Fin (s j).a) × (Fin (P.mb j) × Fin (s j).b))
  | 0 => Matrix.kronecker (P.encode (Matrix.single m m 1)) P.bobInitial
  | j+1 => tensorAction (P.alice j) (P.bob j) (memoryCall (s j).map (P.state m j))

/-- Bob's conditional decoded density (Alice is discarded), PDF p.13 (244). -/
def AdaptiveCode.output {s : ℕ → Slot} {n M : ℕ} (P : AdaptiveCode s n M) (m : Fin M) : Op (Fin M) :=
  P.decode (discardAlice (P.state m n))

/-- Message/reference cq state, PDF p.12 (235), p.13 (248). -/
def AdaptiveCode.cq {s : ℕ → Slot} {n M : ℕ} (P : AdaptiveCode s n M) (p : Fin M → ℝ) :
    Op (Fin M × Fin M) :=
  ∑ m, (p m : ℂ) • Matrix.kronecker (Matrix.single m m 1) (P.output m)

/-- Ideal message/reference correlation for the SAME distribution, PDF p.13 (246). -/
def idealCQ {M : ℕ} (p : Fin M → ℝ) : Op (Fin M × Fin M) :=
  ∑ m, (p m : ℂ) • Matrix.kronecker (Matrix.single m m 1) (Matrix.single m m 1)

/-- Trace-distance error, PDF p.13 (245),(257). -/
def AdaptiveCode.error {s : ℕ → Slot} {n M : ℕ} (P : AdaptiveCode s n M) (p : Fin M → ℝ) : ℝ :=
  traceNorm (P.cq p - idealCQ p) / 2

/-- Maximum error quantifies over p AFTER choosing P; RT fixes uniform p, PDF p.13. -/
def AdaptiveCode.ErrorAtMost {s : ℕ → Slot} {n M : ℕ} (P : AdaptiveCode s n M)
    (epsilon : ℝ) (rt : Bool) : Prop :=
  if rt then P.error (fun _ => (M : ℝ)⁻¹) ≤ epsilon else
    ∀ p : Fin M → ℝ, (∀ m, 0 ≤ p m) → (∑ m, p m) = 1 → P.error p ≤ epsilon

/-- Operational finite-use supremum, PDF p.13 (252),(259), p.15 (283).
`calls` counts actual slots; `denom` counts forward calls when feedback slots are free. -/
def codeCapacity (s : ℕ → Slot) (calls denom : ℕ) (epsilon : ℝ) (rt : Bool) : EReal :=
  sSup {r | ∃ M : ℕ, 0 < M ∧ ∃ P : AdaptiveCode s calls M,
    P.Valid ∧ P.ErrorAtMost epsilon rt ∧ r = ((Real.logb 2 M / denom : ℝ) : EReal)}

/-- Finite-use bipartite classical/RT capacity, PDF p.13 (252),(259). -/
def finiteCapacity {a b c d : ℕ} (N : Superop (Fin a × Fin b) (Fin c × Fin d))
    (n : ℕ) (epsilon : ℝ) (rt : Bool) : EReal :=
  codeCapacity (fun _ => fixedSlot N) n n epsilon rt

/-- inf-error liminf capacity, with positive n indexed by k+1, PDF pp.13-14. -/
def capacityOf (f : ℕ → ℝ → EReal) : EReal :=
  ⨅ e : {x : ℝ // 0 < x ∧ x < 1},
    Filter.liminf (fun k : ℕ => f (k+1) e.1) atTop

/-- sup-error limsup strong-converse capacity, PDF pp.13-14. -/
def strongCapacityOf (f : ℕ → ℝ → EReal) : EReal :=
  ⨆ e : {x : ℝ // 0 < x ∧ x < 1},
    Filter.limsup (fun k : ℕ => f (k+1) e.1) atTop

/-- Unassisted forward classical capacity, PDF p.13 (253). -/
def forwardCapacity {a b c d : ℕ} (N : Superop (Fin a × Fin b) (Fin c × Fin d)) : EReal :=
  capacityOf (fun n e => finiteCapacity N n e false)

/-- Unassisted forward RT capacity, PDF p.14 (260). -/
def randomnessCapacity {a b c d : ℕ} (N : Superop (Fin a × Fin b) (Fin c × Fin d)) : EReal :=
  capacityOf (fun n e => finiteCapacity N n e true)

/-- Strong-converse classical capacity, PDF p.13 (254). -/
def classicalStrong {a b c d : ℕ} (N : Superop (Fin a × Fin b) (Fin c × Fin d)) : EReal :=
  strongCapacityOf (fun n e => finiteCapacity N n e false)

/-- Strong-converse RT capacity, PDF p.14 (261). -/
def randomnessStrong {a b c d : ℕ} (N : Superop (Fin a × Fin b) (Fin c × Fin d)) : EReal :=
  strongCapacityOf (fun n e => finiteCapacity N n e true)

/-- A rectangular backward channel, PDF p.16, with trivial opposite ports. -/
structure Backward where
  input : ℕ
  output : ℕ
  map : Superop (Fin input) (Fin output)

/-- Embed a backward channel in the bipartite model, PDF p.15. -/
def Backward.slot (F : Backward) : Slot :=
  ⟨1,F.input,F.output,1,fun X p q => F.map (fun i j => X (0,i) (0,j)) p.1 q.1⟩

/-- Alternating backward and forward slots, PDF p.15 (282).
Zero-based even slots are backward; odd slots are forward. -/
def feedbackSlots {a d : ℕ} (N : Superop (Fin a) (Fin d)) (F : ℕ → Backward) : ℕ → Slot :=
  fun j => if j % 2 = 0 then (F (j/2)).slot else fixedSlot (pointMap N)

/-- Classical feedback alphabets may vary and are arbitrarily large but finite, PDF p.15. -/
def classicalBackward (k : ℕ) : Backward :=
  ⟨k,k,fun X => Matrix.diagonal fun i => X i i⟩

/-- n forward uses with free classical feedback in n backward slots, PDF p.15 (283).
The fixed code is selected before universally testing message distributions. -/
def feedbackFinite {a d : ℕ} (N : Superop (Fin a) (Fin d))
    (n : ℕ) (epsilon : ℝ) : EReal :=
  sSup {r | ∃ k : ℕ → ℕ, (∀ j < n, 0 < k j) ∧
    r = codeCapacity (feedbackSlots N (fun j => classicalBackward (k j))) (2*n) n epsilon false}

/-- Feedback-assisted inf-error liminf capacity, PDF p.15 (284). -/
def feedbackCapacity {a d : ℕ} (N : Superop (Fin a) (Fin d)) : EReal :=
  capacityOf (feedbackFinite N)

/-- Feedback-assisted sup-error limsup capacity, PDF p.15 (285). -/
def feedbackStrong {a d : ℕ} (N : Superop (Fin a) (Fin d)) : EReal :=
  strongCapacityOf (feedbackFinite N)

/-- Rectangular EB channels: reference can be any finite size, PDF p.16.
CPTP is explicit; normalized separability follows from the output trace one. -/
def Backward.IsEB (F : Backward) : Prop :=
  0 < F.input ∧ 0 < F.output ∧ IsChannel F.map ∧
  ∀ r : ℕ, ∀ X : Op (Fin r × Fin F.input), IsDensityMatrix X →
    Entanglement.IsSeparablePositive (idTensorSuperop F.map X)

/-- Operational capacity allowing arbitrary EB feedback in each slot, PDF p.16. -/
def ebFinite {a d : ℕ} (N : Superop (Fin a) (Fin d)) (n : ℕ) (epsilon : ℝ) : EReal :=
  sSup {r | ∃ F : ℕ → Backward, (∀ j < n, (F j).IsEB) ∧
    r = codeCapacity (feedbackSlots N F) (2*n) n epsilon false}

example {s : ℕ → Slot} {n M : ℕ} (P : AdaptiveCode s n M) (m : Fin M) :
    P.state m 0 = Matrix.kronecker (P.encode (Matrix.single m m 1)) P.bobInitial := rfl

example {s : ℕ → Slot} {n M : ℕ} (P : AdaptiveCode s n M) (e : ℝ) :
    P.ErrorAtMost e true ↔ P.error (fun _ => (M : ℝ)⁻¹) ≤ e := by rfl

/-- Local unitary conjugations, PDF p.8 (134). -/
def unitaryChannel {I : Type} [Fintype I] (U : Matrix.unitaryGroup I ℂ) : Superop I I :=
  conjSuperop (U : Op I)

/-- Unitary representation laws, PDF p.17. -/
def Representation {G I : Type} [Group G] [Fintype I]
    (U : G → Matrix.unitaryGroup I ℂ) : Prop := U 1 = 1 ∧ ∀ g h, U (g*h) = U g * U h

/-- Unitary one-design as equality on EVERY operator, PDF p.17 (305)-(306). -/
def OneDesign {G I : Type} [Fintype G] [Fintype I]
    (U : G → Matrix.unitaryGroup I ℂ) : Prop :=
  ∀ X : Op I, (Fintype.card G : ℂ)⁻¹ • (∑ g, unitaryChannel (U g) X) =
    X.trace • ((Fintype.card I : ℂ)⁻¹ • (1 : Op I))

/-- Covariance for fixed representations, distinct from the one-design condition,
PDF p.17 (304). All equalities are on all operators. -/
def BiCovariant {G H A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (U : G → Matrix.unitaryGroup A ℂ) (V : H → Matrix.unitaryGroup B ℂ)
    (W : G × H → Matrix.unitaryGroup C ℂ) (Y : G × H → Matrix.unitaryGroup D ℂ)
    (N : Superop (A × B) (C × D)) : Prop :=
  ∀ g h X, N (tensorAction (unitaryChannel (U g)) (unitaryChannel (V h)) X) =
    tensorAction (unitaryChannel (W (g,h))) (unitaryChannel (Y (g,h))) (N X)

/-- Independent input twirl, PDF p.17 (308). -/
def inputTwirl {G H A B : Type} [Fintype G] [Fintype H] [Fintype A] [Fintype B]
    (U : G → Matrix.unitaryGroup A ℂ) (V : H → Matrix.unitaryGroup B ℂ)
    (rho : Op (A × B)) : Op (A × B) :=
  ((Fintype.card G * Fintype.card H : ℕ) : ℂ)⁻¹ •
    ∑ g, ∑ h, tensorAction (unitaryChannel (U g)) (unitaryChannel (V h)) rho

/-- Restricted supremum over pure inputs with invariant MARGINAL (not invariant vector),
PDF p.17 (307)-(308). Reference is input-sized. -/
def invariantInputD {G H A B C D : Type} [Fintype G] [Fintype H]
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (div : Divergence) (U : G → Matrix.unitaryGroup A ℂ) (V : H → Matrix.unitaryGroup B ℂ)
    (N M : Superop (A × B) (C × D)) : EReal :=
  sSup {r | ∃ psi : EuclideanSpace ℂ ((A × B) × (A × B)), IsState psi ∧
    discardAlice (pureDensity psi) = inputTwirl U V (discardAlice (pureDensity psi)) ∧
    r = div (idTensorSuperop N (pureDensity psi)) (idTensorSuperop M (pureDensity psi))}

/-- Same-representation comparator restriction; PDF p.17 (307). -/
def symmetricUpsilon {G H A B C D : Type} [Fintype G] [Fintype H]
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (div : Divergence) (U : G → Matrix.unitaryGroup A ℂ) (V : H → Matrix.unitaryGroup B ℂ)
    (W : G × H → Matrix.unitaryGroup C ℂ) (Y : G × H → Matrix.unitaryGroup D ℂ)
    (N : Superop (A × B) (C × D)) : EReal :=
  sInf {r | ∃ M, CP M ∧ bipartiteBeta M ≤ 1 ∧ BiCovariant U V W Y M ∧
    r = invariantInputD div U V N M}

/-- Choi-state version of the same comparator optimization, PDF p.17 (309).
The normalized entangled state on AB purifies pi_A tensor pi_B. -/
def choiUpsilon {G H A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (div : Divergence) (U : G → Matrix.unitaryGroup A ℂ) (V : H → Matrix.unitaryGroup B ℂ)
    (W : G × H → Matrix.unitaryGroup C ℂ) (Y : G × H → Matrix.unitaryGroup D ℂ)
    (N : Superop (A × B) (C × D)) : EReal :=
  sInf {r | ∃ M, CP M ∧ bipartiteBeta M ≤ 1 ∧ BiCovariant U V W Y M ∧
    r = div (idTensorSuperop N (entangledPhi (A × B)))
      (idTensorSuperop M (entangledPhi (A × B)))}

/-- Existence of finite independent one-design symmetries, PDF pp.17-18.
Every finite group can be relabeled onto Fin g; Group instances enforce nonemptiness. -/
def HasBiDesign {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (N : Superop (A × B) (C × D)) : Prop :=
  ∃ g h : ℕ, ∃ gg : Group (Fin g), ∃ hh : Group (Fin h),
    letI := gg
    letI := hh
    ∃ U : Fin g → Matrix.unitaryGroup A ℂ, ∃ V : Fin h → Matrix.unitaryGroup B ℂ,
    ∃ W : Fin g × Fin h → Matrix.unitaryGroup C ℂ,
    ∃ Y : Fin g × Fin h → Matrix.unitaryGroup D ℂ,
      Representation U ∧ Representation V ∧ Representation W ∧ Representation Y ∧
      OneDesign U ∧ OneDesign V ∧ BiCovariant U V W Y N

/-- Point covariance with an input ONE-DESIGN, PDF pp.18-19 (332). -/
def HasPointDesign {A D : Type} [Fintype A] [Fintype D] (N : Superop A D) : Prop :=
  ∃ g : ℕ, ∃ gg : Group (Fin g),
    letI := gg
    ∃ U : Fin g → Matrix.unitaryGroup A ℂ, ∃ V : Fin g → Matrix.unitaryGroup D ℂ,
      Representation U ∧ Representation V ∧ OneDesign U ∧
      ∀ g X, N (unitaryChannel (U g) X) = unitaryChannel (V g) (N X)

/-- Partial swap U_p=sqrt(1-p)I+i sqrt(p)Swap; PDF p.19 (335)-(338). -/
def partialSwap (d : ℕ) (p : ℝ) : Superop (Fin d × Fin d) (Fin d × Fin d) :=
  let S : Op (Fin d × Fin d) := fun x y => if x = (y.2,y.1) then 1 else 0
  conjSuperop ((Real.sqrt (1-p) : ℂ) • 1 + (Complex.I * (Real.sqrt p : ℂ)) • S)

/-- Relabel the rectangular erasure output to Fin(d+1), retaining the distinguished
orthogonal flag; PDF p.21 (350). -/
def erasureFin (d : ℕ) (p : ℝ) : Superop (Fin d) (Fin (d+1)) :=
  fun X u v => if hu : u.val < d then
    if hv : v.val < d then (1-(p : ℂ)) * X ⟨u.val,hu⟩ ⟨v.val,hv⟩ else 0
  else if v.val < d then 0 else (p : ℂ) * X.trace

example (d : ℕ) (X : Op (Fin d)) : singleErasure d 1 X none none = X.trace := by simp [singleErasure]

example (d : ℕ) (X : Op (Fin d)) : depolarizing d 0 X = X := by simp [depolarizing]

/-- Continuous U tensor U action, PDF p.20 (339). -/
def correlatedUnitary {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) : Op (Fin d × Fin d) :=
  Matrix.kronecker (U : Op (Fin d)) (U : Op (Fin d))

/-- Normalized Haar state twirl, PDF p.20 (339). Matrix integrands are continuous
on the compact unitary group, so they are integrable for the probability Haar law. -/
def haarInput {d : ℕ} (rho : Op (Fin d × Fin d)) : Op (Fin d × Fin d) :=
  ∫ U : Matrix.unitaryGroup (Fin d) ℂ,
    conjSuperop (correlatedUnitary U) rho ∂(Schur.unitaryHaar d)

/-- Normalized correlated map twirl; NOT an independent product-group twirl,
PDF p.20 (341). For CP M linearity implies continuity of the integrand. -/
def haarMap {d : ℕ} (M : Superop (Fin d × Fin d) (Fin d × Fin d)) :
    Superop (Fin d × Fin d) (Fin d × Fin d) :=
  fun X => ∫ U : Matrix.unitaryGroup (Fin d) ℂ,
    conjSuperop ((correlatedUnitary U)ᴴ) (M (conjSuperop (correlatedUnitary U) X))
    ∂(Schur.unitaryHaar d)

/-- Input conjugate U,U and output U,U Choi action in input-first order,
PDF p.20 (342). Integration uses the normalized probability Haar law. -/
def haarChoi {d : ℕ} (J : Op ((Fin d × Fin d) × (Fin d × Fin d))) :
    Op ((Fin d × Fin d) × (Fin d × Fin d)) :=
  ∫ U : Matrix.unitaryGroup (Fin d) ℂ,
    conjSuperop (Matrix.kronecker ((correlatedUnitary U).map star) (correlatedUnitary U)) J
    ∂(Schur.unitaryHaar d)

/-- The Haar-restricted minimax, PDF p.20 (339)-(342). -/
def haarUpsilon {d : ℕ} (div : Divergence)
    (N : Superop (Fin d × Fin d) (Fin d × Fin d)) : EReal :=
  sInf {r | ∃ M, CP M ∧ bipartiteBeta M ≤ 1 ∧ (∀ X, M X = haarMap M X) ∧
    r = sSup {v | ∃ psi : EuclideanSpace ℂ ((Fin d × Fin d) × (Fin d × Fin d)),
      IsState psi ∧ discardAlice (pureDensity psi) = haarInput (discardAlice (pureDensity psi)) ∧
      v = div (idTensorSuperop N (pureDensity psi)) (idTensorSuperop M (pureDensity psi))}}

/-- Finite-dimensional coordinates for the topology of complex-linear maps,
PDF p.28. Every coefficient is the image of an input matrix unit. -/
abbrev MapCoefficients (I J : Type) := I → I → Op J

/-- Reconstruct the actual linear superoperator from its coefficients, PDF p.28. -/
def coeffMap {I J : Type} [Fintype I] (K : MapCoefficients I J) : Superop I J :=
  fun X => ∑ i, ∑ j, X i j • K i j

/-- Lawful channel/CP pair domain with the subspace finite-dimensional topology,
PDF p.28, Lemma 37. -/
abbrev ChannelPair (I J : Type) [Fintype I] [Fintype J] :=
  {p : MapCoefficients I J × MapCoefficients I J // IsChannel (coeffMap p.1) ∧ CP (coeffMap p.2)}

/-- Joint channel divergence on that domain, PDF p.28. -/
def pairD {I J : Type} [Fintype I] [Fintype J] (div : Divergence)
    (p : ChannelPair I J) : EReal := channelD div (coeffMap p.1.1) (coeffMap p.1.2)

/-- The positive-order two-sided punctured approach to one, PDF pp.25-28. -/
def orderOne : Filter ℝ := 𝓝[ {x : ℝ | 0 < x ∧ x ≠ 1} ] (1 : ℝ)

/-- Extended base-two exponential, PDF p.26 (429). -/
def exp2Ext (x : EReal) : EReal :=
  if x = ⊤ then ⊤ else if x = ⊥ then 0 else ((Real.rpow 2 x.toReal : ℝ) : EReal)

/-- Extended geometric continuity parameter, PDF p.26 (429). -/
def geometricNu {I : Type} [Fintype I] (rho sigma : Op I) : EReal :=
  exp2Ext (((1/2 : ℝ) : EReal) * geometricD (3/2) rho sigma) +
    exp2Ext (((-1/2 : ℝ) : EReal) * geometricD (1/2) rho sigma) + 1

/-- The OPEN parameter domain, PDF p.26 (428). Infinite nu admits no positive delta;
no toReal default at infinity is used to manufacture a finite threshold. -/
def GeometricDelta {I : Type} [Fintype I] (rho sigma : Op I) (delta : ℝ) : Prop :=
  geometricNu rho sigma ≠ ⊤ ∧ geometricNu rho sigma ≠ ⊥ ∧ 0 < delta ∧
    delta < Real.log 3 / (4 * Real.log (geometricNu rho sigma).toReal)

example {I J : Type} [Fintype I] : coeffMap (0 : MapCoefficients I J) = 0 := by
  funext X; simp [coeffMap]

example {d : ℕ} : haarInput (0 : Op (Fin d × Fin d)) = 0 := by
  simp [haarInput, conjSuperop]

/-- Compare the fixed classical correlation against all beta-feasible CP outputs,
PDF pp.11-12 (213)-(214). -/
def pointPhiInf {I : Type} [Fintype I] (div : Divergence) (N : Superop I I) : EReal :=
  sInf {r | ∃ M : Superop I I, CP M ∧ bipartiteBeta (pointMap M) ≤ 1 ∧
    r = div (idTensorSuperop N (classicalPhi I)) (idTensorSuperop M (classicalPhi I))}

/-- Sanity: zero is an allowed completely positive comparison, PDF pp.4,9. -/
example {I J : Type} [Fintype I] [Fintype J] : CP (0 : Superop I J) := by
  refine ⟨0, (fun _ => 0), ?_⟩
  intro X
  simp [krausApply]

/-- Sanity: entangled Phi has coherence absent from classical Phi, PDF pp.3,11. -/
example : entangledPhi (Fin 2) (0,0) (1,1) = (1/2 : ℂ) := by
  norm_num [entangledPhi]

/-- Sanity: memoryCall applies no operation to spectator memories, PDF p.13. -/
example {A B E F : Type} (X : Op ((E × A) × (F × B))) :
    memoryCall (fun Y : Op (A × B) => Y) X = X := rfl

/-- Sanity: the first feedback slot is backward, PDF p.15. -/
example {a d : ℕ} (N : Superop (Fin a) (Fin d)) (F : ℕ → Backward) :
    feedbackSlots N F 0 = (F 0).slot := by simp [feedbackSlots]

/-- Sanity: the rectangular channel's last output is the erasure flag, PDF p.21. -/
example (d : ℕ) (X : Op (Fin d)) :
    erasureFin d 1 X ⟨d, by omega⟩ ⟨d, by omega⟩ = X.trace := by
  simp [erasureFin]

/-- Sanity: infinite geometric parameter cannot create a finite positive threshold,
PDF p.26. -/
example {I : Type} [Fintype I] (rho sigma : Op I) (delta : ℝ)
    (h : geometricNu rho sigma = ⊤) : ¬ GeometricDelta rho sigma delta := by
  simp [GeometricDelta, h]

/-! ### Source results -/

end QAlgorithms.Papers.Independent.Dependency50.P09


