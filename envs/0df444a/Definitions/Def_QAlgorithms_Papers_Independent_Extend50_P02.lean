-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P02
-- name    : QAlgorithms_Papers_Independent_Extend50_P02
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T12:35:23.642812+00:00
-- url     : https://prove2.me/theorems/70d883e2-107a-4a16-86a6-8cc96afbe9e3
-- title:
--   Definitions for Quantifying the performance of approximate teleportation and quantum error correction via symmetric two-PPT-extendibility
-- statement:
--   The objects the formalized statements of *Quantifying the performance of approximate teleportation and quantum error correction via symmetric two-PPT-extendibility* (arXiv:2207.06931) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `HasFiniteKraus`: PDF p.4: completely positive maps, in finite Kraus form.
--   - `tensorSuperopAction`: PDF p.4: tensor product on arbitrary, possibly entangled, operators.
--   - `IsAliceToBobLOCC`: PDF p.4, (7): Alice's instrument and Bob's conditional channels.
--   - `IsLOCR`: PDF p.4, (8), and p.11, (128): local CPTP maps with common randomness.
--   - `stabilizedHalfTraceDistance`: PDF pp.6–7, (43)–(48): half the stabilized trace distance. For channels the input-sized reference and density matrices suffice.
--   - `worstCaseSquaredFidelity`: PDF p.7, (50)–(52): worst-case squared Uhlmann fidelity on normalized reference-assisted inputs.
--   - `Criterion`: PDF pp.7,13: the two error criteria.
--   - `simulationErrorFor`: PDF pp.7,13, (60),(62),(168),(170).
--   - `infimumSimulationError`: PDF pp.7,13: optimize over a specified physical simulation class. In all theorem uses this set is nonempty and its errors belong to [0,1].
--   - `BiOp`: PDF pp.4–5: index order (Alice input,Bob input;Alice output,Bob output).
--   - `ExtOp`: PDF p.5, (14)–(17): two Bob inputs and two Bob outputs.
--   - `swapExtension`: PDF p.5, (14): simultaneous Bob input/output swap.
--   - `averagedBobExtensionMarginal`: PDF p.9, (87), and p.14, (185): maximally-mixed-input marginal. This is a computed partial trace, never an independent matrix variable.
--   - `transposeBob2`: PDF p.5, (33): transpose second Bob input and output.
--   - `transposeAlice`: PDF p.5, (34): transpose Alice's input and output.
--   - `IsSymmetricBobChannelExtension`: PDF p.5, (14)–(17): PSD, TP, covariance, and exact marginal extension.
--   - `ExtensionNS`: PDF p.12, (146): extra non-signaling from Alice to both Bobs, on the extension.
--   - `HasExtension`: PDF pp.5,12: two-extendibility, with optional PPT and extra NS constraints.
--   - `BobToAliceNS`: PDF p.5, (18): Choi form of the Bob-to-Alice non-signaling equation (12).
--   - `appendResourceAndApply`: PDF p.6, (42): append the fixed resource state.
--   - `teleportBipartite`: PDF p.6: trivial Alice output displayed for bipartite notation.
--   - `teleportSet`: PDF pp.7–9: none = one-way LOCC; some false = two-extendible; some true = two-PPT-extendible. Protocols are fixed before the input.
--   - `teleportError`: PDF pp.7–9, (61),(63),(72),(88).
--   - `wireChoi`: PDF p.11, (122): component form of the fully-transposed Choi link.
--   - `wire`: PDF p.11, (122): physical superchannel output reconstructed from its Choi.
--   - `CorrectionClass`: PDF pp.12–14: distinct assisted and unassisted classes.
--   - `AllowedCorrection`: PDF pp.11–14: product = one encoder and one decoder; LOCR allows shared randomness; the extra NS condition is required only when ns=true.
--   - `correctionError`: PDF pp.12–14, (148),(150),(155),(157),(169),(171),(172),(218).
--   - `nonidentityWeylAverage`: PDF p.8, (69): the nonidentity Weyl average, using the full Weyl sum identity d Tr(X) I. Used only when card A >= 2.
--   - `entFidelity`: PDF p.13, (165): normalized Phi, with reference identity explicit.
--   - `isotropicTeleport`: PDF p.8, (68): the identity/nonidentityWeylAverage map controlled by K and L.
--   - `HasDecoderEffect`: PDF p.8, (70): POVM/conditional-decoder representation of K.
--   - `teleportOneWaySuccess`: PDF p.8, (67)–(68): full variational objective including one-way implementability.
--   - `contractResource`: PDF p.9, (81): contract the transposed resource against the marginal. The component formula includes the transpose through the contracted index order.
--   - `TeleportSDP`: PDF p.9, (79)–(86): unreduced teleportation SDP.
--   - `CorrectionSDP`: PDF p.14, (175)–(183): unreduced correction SDP; TP traces H,B1,B2.
--   - `TwoBobCoefficients`: PDF pp.9–10,14–15: the six reduced operator variables on H,J1,J2.
--   - `realOperatorScale`: Real scalar multiplication of an operator; all denominators below are real.
--   - `twoByTwoPauliOperator`: PDF p.9, (91): the two-by-two block test, with the printed i signs.
--   - `swapReduced`: PDF p.9, (93)–(94): swap J1 and J2.
--   - `transposeH`: PDF pp.9–10, (97)–(103): partial transpose H.
--   - `transposeHJ1`: PDF pp.9–10, (104)–(110): partial transpose H,J1.
--   - `HasMixedSecondBobFactor`: PDF p.9, (95), or p.14, (192)–(193): decouple J2 by partial trace.
--   - `reducedP`: PDF p.9, (96), and p.14, (194): P, not a free variable.
--   - `reducedQ`: PDF p.15, (195): Q, which cannot be eliminated for correction.
--   - `ReducedCommon`: PDF pp.9,14: CP and permutation covariance constraints, common to both SDPs.
--   - `reducedL`: PDF p.10, (111)–(113), or p.15, (210)–(212): the constructed L operators.
--   - `reducedG`: PDF p.9, (100)–(103), or p.15, (199)–(202): the constructed G operators.
--   - `reducedE`: PDF p.10, (107)–(110), or p.15, (206)–(209): the constructed E operators.
--   - `ReducedPPT`: PDF pp.9–10, (97)–(106), or pp.14–15, (196)–(205). The plus sign in (104)/(203) follows p.9,p.15 and (C268)-(C269) p.37; the frozen PLAN summary mistakenly places a minus there. The minus in (105)/(204) is retained. At d=2 the minus sector is zero and BOTH d-2 denominator constraints are absent. SOURCE CORRECTION: Appendix C8 p.38 says remove (97); pp.10 and the preceding sector calculation require removing (98). The present definition follows p.10.
--   - `ReducedNS`: PDF p.15, (213)–(217): NS on the extension transported to the reduced variables. At d=2 (214) is removed. The factors 1/2 in (215),(216) are retained.
--   - `ReducedTeleportFeasible`: PDF p.9, (90)–(106), and Remark 5 p.10: teleportation reduced feasible set.
--   - `ReducedCorrectionFeasible`: PDF pp.14–15, (187)–(217), Remarks 11–12: correction reduced feasible set. Dropping extra NS leaves both P and Q marginal constraints in place.
--   - `reducedObjective`: PDF p.9, (90), and p.14, (187): Re Tr[(T^T tensor I) P]/dim J.
--   - `reducedTeleportBound`: PDF p.9, (90), including every constraint of the selected relaxation.
--   - `reducedCorrectionBound`: PDF p.14, (187), including every constraint of the selected relaxation.
--   - `transposeJ`: PDF p.16, (220),(223): transpose only the Bob register.
--   - `pptTeleportBound`: PDF p.16, (220): the PPT-only teleportation program.
--   - `pptCorrectionBound`: PDF pp.16–17, (223): PPT correction program, with exactly one optional NS equality.
-- source:
--   Quantifying the performance of approximate teleportation and quantum error correction via symmetric two-PPT-extendibility, arXiv:2207.06931v4, https://arxiv.org/abs/2207.06931v4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34

/-! Holdsworth–Singh–Wilde, arXiv:2207.06931v4. Computational bases are fixed.
Choi operators are unnormalized and input first. Loewner inequalities are expressed
by `PosSemidef` of differences. Paper-local definitions implement only this paper. The accepted matrix and
Choi primitives are imported from the pinned library; no accepted theorem is assumed. -/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Extend50.P02

open QAlgorithms.Papers.Independent.Information100.P32 (Op)
open QAlgorithms.Papers.Independent.Information100.P34 (choi fromChoi)

variable {A B C D H J : Type*}
variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype H] [Fintype J]

/-- PDF p.4: completely positive maps, in finite Kraus form. -/
def HasFiniteKraus (E : Superop A B) : Prop :=
  ∃ m : ℕ, ∃ K : Fin m → Matrix B A ℂ, ∀ X, E X = krausApply K X

/-- PDF p.4: tensor product on arbitrary, possibly entangled, operators. -/
def tensorSuperopAction (E : Superop A C) (F : Superop B D) : Superop (A × B) (C × D) :=
  fun X p q => ∑ a, ∑ a', ∑ b, ∑ b',
    X (a,b) (a',b') * E (Matrix.single a a' 1) p.1 q.1 *
      F (Matrix.single b b' 1) p.2 q.2

/-- PDF p.4, (7): Alice's instrument and Bob's conditional channels. -/
def IsAliceToBobLOCC (P : Superop (A × B) (C × D)) : Prop :=
  ∃ m : ℕ, ∃ E : Fin m → Superop A C, ∃ F : Fin m → Superop B D,
    (∀ y, HasFiniteKraus (E y)) ∧ IsChannel (fun X => ∑ y, E y X) ∧
    (∀ y, IsChannel (F y)) ∧ ∀ X, P X = ∑ y, tensorSuperopAction (E y) (F y) X

/-- PDF p.4, (8), and p.11, (128): local CPTP maps with common randomness. -/
def IsLOCR (P : Superop (A × B) (C × D)) : Prop :=
  ∃ m : ℕ, ∃ p : Fin m → ℝ, ∃ E : Fin m → Superop A C,
    ∃ F : Fin m → Superop B D,
    (∀ y, 0 ≤ p y) ∧ (∑ y, p y) = 1 ∧
    (∀ y, IsChannel (E y) ∧ IsChannel (F y)) ∧
    ∀ X, P X = ∑ y, (p y : ℂ) • tensorSuperopAction (E y) (F y) X

/-- PDF pp.6–7, (43)–(48): half the stabilized trace distance.
For channels the input-sized reference and density matrices suffice. -/
def stabilizedHalfTraceDistance [Nonempty A] (N M : Superop A B) : ℝ :=
  sSup {v | ∃ rho : Op (A × A), IsDensityMatrix rho ∧
    v = traceNorm (idTensorSuperop N rho - idTensorSuperop M rho) / 2}

/-- PDF p.7, (50)–(52): worst-case squared Uhlmann fidelity on normalized
reference-assisted inputs. -/
def worstCaseSquaredFidelity [Nonempty A] (N M : Superop A B) : ℝ :=
  sInf {v | ∃ rho : Op (A × A), IsDensityMatrix rho ∧
    v = rootFidelity (idTensorSuperop N rho) (idTensorSuperop M rho) ^ 2}

/-- PDF pp.7,13: the two error criteria. -/
inductive Criterion where
  | diamond
  | infidelity
  deriving DecidableEq

/-- PDF pp.7,13, (60),(62),(168),(170). -/
def simulationErrorFor [Nonempty A] (c : Criterion) (N M : Superop A B) : ℝ :=
  match c with
  | .diamond => stabilizedHalfTraceDistance N M
  | .infidelity => 1 - worstCaseSquaredFidelity N M

/-- PDF pp.7,13: optimize over a specified physical simulation class.
In all theorem uses this set is nonempty and its errors belong to [0,1]. -/
def infimumSimulationError [Nonempty A] (c : Criterion) (N : Superop A B)
    (S : Set (Superop A B)) : ℝ := sInf {v | ∃ M ∈ S, v = simulationErrorFor c N M}

/-- PDF pp.4–5: index order (Alice input,Bob input;Alice output,Bob output). -/
abbrev BiOp (A B C D : Type*) := Op ((A × B) × (C × D))

/-- PDF p.5, (14)–(17): two Bob inputs and two Bob outputs. -/
abbrev ExtOp (A B C D : Type*) := BiOp A (B × B) C (D × D)

/-- PDF p.5, (14): simultaneous Bob input/output swap. -/
def swapExtension (M : ExtOp A B C D) : ExtOp A B C D :=
  fun p q => M ((p.1.1,(p.1.2.2,p.1.2.1)),(p.2.1,(p.2.2.2,p.2.2.1)))
    ((q.1.1,(q.1.2.2,q.1.2.1)),(q.2.1,(q.2.2.2,q.2.2.1)))

/-- PDF p.9, (87), and p.14, (185): maximally-mixed-input marginal.
This is a computed partial trace, never an independent matrix variable. -/
def averagedBobExtensionMarginal (M : ExtOp A B C D) : BiOp A B C D :=
  fun p q => (Fintype.card B : ℂ)⁻¹ * ∑ b, ∑ d,
    M ((p.1.1,(p.1.2,b)),(p.2.1,(p.2.2,d)))
      ((q.1.1,(q.1.2,b)),(q.2.1,(q.2.2,d)))

/-- PDF p.5, (33): transpose second Bob input and output. -/
def transposeBob2 (M : ExtOp A B C D) : ExtOp A B C D :=
  fun p q => M ((p.1.1,(p.1.2.1,q.1.2.2)),(p.2.1,(p.2.2.1,q.2.2.2)))
    ((q.1.1,(q.1.2.1,p.1.2.2)),(q.2.1,(q.2.2.1,p.2.2.2)))

/-- PDF p.5, (34): transpose Alice's input and output. -/
def transposeAlice (M : ExtOp A B C D) : ExtOp A B C D :=
  fun p q => M ((q.1.1,p.1.2),(q.2.1,p.2.2)) ((p.1.1,q.1.2),(p.2.1,q.2.2))

/-- PDF p.5, (14)–(17): PSD, TP, covariance, and exact marginal extension. -/
def IsSymmetricBobChannelExtension (W : BiOp A B C D) (M : ExtOp A B C D) : Prop :=
  M.PosSemidef ∧ traceRight M = 1 ∧ swapExtension M = M ∧
  ∀ a a' b b' e e' c c' d d',
    (∑ f, M ((a,(b,e)),(c,(d,f))) ((a',(b',e')),(c',(d',f)))) =
      W ((a,b),(c,d)) ((a',b'),(c',d')) * (if e = e' then 1 else 0)

/-- PDF p.12, (146): extra non-signaling from Alice to both Bobs, on the extension. -/
def ExtensionNS (M : ExtOp A B C D) : Prop :=
  ∀ a a' b b' e e' d d' f f',
    (∑ c, M ((a,(b,e)),(c,(d,f))) ((a',(b',e')),(c,(d',f')))) =
      (if a = a' then 1 else 0) * (Fintype.card A : ℂ)⁻¹ *
        ∑ a0, ∑ c, M ((a0,(b,e)),(c,(d,f))) ((a0,(b',e')),(c,(d',f')))

/-- PDF pp.5,12: two-extendibility, with optional PPT and extra NS constraints. -/
def HasExtension (ppt ns : Bool) (W : BiOp A B C D) : Prop :=
  ∃ M : ExtOp A B C D, IsSymmetricBobChannelExtension W M ∧
    (ppt = true → (transposeAlice M).PosSemidef ∧ (transposeBob2 M).PosSemidef) ∧
    (ns = true → ExtensionNS M)

/-- PDF p.5, (18): Choi form of the Bob-to-Alice non-signaling equation (12). -/
def BobToAliceNS (W : BiOp A B C D) : Prop :=
  ∀ a a' b b' c c',
    (∑ d, W ((a,b),(c,d)) ((a',b'),(c',d))) =
      (if b = b' then 1 else 0) * (Fintype.card B : ℂ)⁻¹ *
        ∑ b0, ∑ d, W ((a,b0),(c,d)) ((a',b0),(c',d))

/-- PDF p.6, (42): append the fixed resource state. -/
def appendResourceAndApply (rho : Op (H × J)) (L : Superop ((A × H) × J) B) : Superop A B :=
  fun X => L (fun p q => X p.1.1 q.1.1 * rho (p.1.2,p.2) (q.1.2,q.2))

/-- PDF p.6: trivial Alice output displayed for bipartite notation. -/
def teleportBipartite (L : Superop ((A × H) × J) B) :
    Superop ((A × H) × J) (Unit × B) := fun X p q => L X p.2 q.2

/-- PDF pp.7–9: none = one-way LOCC; some false = two-extendible;
some true = two-PPT-extendible. Protocols are fixed before the input. -/
def teleportSet (kind : Option Bool) (rho : Op (H × J)) : Set (Superop A B) :=
  {S | ∃ L : Superop ((A × H) × J) B, IsChannel L ∧
    (match kind with
    | none => IsAliceToBobLOCC (teleportBipartite L)
    | some ppt => HasExtension ppt false (choi (teleportBipartite L))) ∧
    S = appendResourceAndApply rho L}

/-- PDF pp.7–9, (61),(63),(72),(88). -/
def teleportError [Nonempty A] (c : Criterion) (kind : Option Bool)
    (N : Superop A B) (rho : Op (H × J)) : ℝ := infimumSimulationError c N (teleportSet kind rho)

/-- PDF p.11, (122): component form of the fully-transposed Choi link. -/
def wireChoi (N : Superop H J) (W : BiOp A J H B) : Op (A × B) :=
  fun p q => ∑ h, ∑ h', ∑ j, ∑ j',
    choi N (h,j) (h',j') * W ((p.1,j),(h,p.2)) ((q.1,j'),(h',q.2))

/-- PDF p.11, (122): physical superchannel output reconstructed from its Choi. -/
def wire (N : Superop H J) (P : Superop (A × J) (H × B)) : Superop A B :=
  fromChoi (wireChoi N (choi P))

/-- PDF pp.12–14: distinct assisted and unassisted classes. -/
inductive CorrectionClass where
  | product
  | locr
  | oneWay
  | extendible (ppt ns : Bool)

/-- PDF pp.11–14: product = one encoder and one decoder; LOCR allows
shared randomness; the extra NS condition is required only when ns=true. -/
def AllowedCorrection (kind : CorrectionClass) (P : Superop (A × J) (H × B)) : Prop :=
  IsChannel P ∧ match kind with
  | .product => ∃ E : Superop A H, ∃ F : Superop J B,
      IsChannel E ∧ IsChannel F ∧ P = tensorSuperopAction E F
  | .locr => IsLOCR P
  | .oneWay => IsAliceToBobLOCC P
  | .extendible ppt ns => HasExtension ppt ns (choi P)

/-- PDF pp.12–14, (148),(150),(155),(157),(169),(171),(172),(218). -/
def correctionError [Nonempty A] (c : Criterion) (kind : CorrectionClass)
    (O : Superop A B) (N : Superop H J) : ℝ :=
  infimumSimulationError c O {S | ∃ P, AllowedCorrection kind P ∧ S = wire N P}

/-- PDF p.8, (69): the nonidentity Weyl average, using the full Weyl
sum identity d Tr(X) I. Used only when card A >= 2. -/
def nonidentityWeylAverage (X : Op A) : Op A :=
  ((Fintype.card A : ℂ)^2 - 1)⁻¹ • ((Fintype.card A : ℂ) • (X.trace • 1) - X)

/-- PDF p.13, (165): normalized Phi, with reference identity explicit. -/
def entFidelity [Nonempty A] (S : Superop A A) : ℝ :=
  effectProb (pureDensity (finiteMaxEntangled A))
    (idTensorSuperop S (pureDensity (finiteMaxEntangled A)))

/-- PDF p.8, (68): the identity/nonidentityWeylAverage map controlled by K and L. -/
def isotropicTeleport (K L : Op (H × J)) : Superop ((A × H) × J) A :=
  fun X =>
    (show Op A from fun a a' => ∑ h, ∑ j, ∑ h', ∑ j',
      K (h,j) (h',j') * X ((a,h'),j') ((a',h),j)) +
    nonidentityWeylAverage (fun a a' => ∑ h, ∑ j, ∑ h', ∑ j',
      L (h,j) (h',j') * X ((a,h'),j') ((a',h),j))

/-- PDF p.8, (70): POVM/conditional-decoder representation of K. -/
def HasDecoderEffect (K : Op (H × J)) (A : Type*) [Fintype A] : Prop :=
  ∃ m : ℕ, ∃ V : Fin m → Op (A × H), ∃ F : Fin m → Superop J A,
    (∀ y, (V y).PosSemidef) ∧ (∑ y, V y) = 1 ∧ (∀ y, IsChannel (F y)) ∧
    K = fun p q => (Fintype.card A : ℂ)⁻¹ ^ 2 * ∑ y, ∑ b, ∑ b',
      V y (b,p.1) (b',q.1) * choi (F y) (p.2,b) (q.2,b')

/-- PDF p.8, (67)–(68): full variational objective including one-way implementability. -/
def teleportOneWaySuccess (rho : Op (H × J)) (A : Type*) [Fintype A] : ℝ :=
  sSup {v | ∃ K L : Op (H × J), K.PosSemidef ∧ L.PosSemidef ∧ K + L = 1 ∧
    IsAliceToBobLOCC (teleportBipartite (isotropicTeleport (A := A) K L)) ∧ v = effectProb K rho}

/-- PDF p.9, (81): contract the transposed resource against the marginal.
The component formula includes the transpose through the contracted index order. -/
def contractResource (T : Op (H × J)) (W : BiOp (A × H) J Unit B) : Op (A × B) :=
  fun p q => ∑ h, ∑ h', ∑ j, ∑ j', T (h,j) (h',j') *
    W (((p.1,h),j),((),p.2)) (((q.1,h'),j'),((),q.2))

/-- PDF p.9, (79)–(86): unreduced teleportation SDP. -/
def TeleportSDP (N : Superop A B) (rho : Op (H × J)) (mu : ℝ)
    (Z : Op (A × B)) (M : ExtOp (A × H) J Unit B) : Prop :=
  0 ≤ mu ∧ Z.PosSemidef ∧ (((mu : ℂ) • (1 : Op A)) - traceRight Z).PosSemidef ∧
  (Z - choi N + contractResource rho (averagedBobExtensionMarginal M)).PosSemidef ∧
  IsSymmetricBobChannelExtension (averagedBobExtensionMarginal M) M ∧
  (transposeAlice M).PosSemidef ∧ (transposeBob2 M).PosSemidef

/-- PDF p.14, (175)–(183): unreduced correction SDP; TP traces H,B1,B2. -/
def CorrectionSDP (O : Superop A B) (N : Superop H J) (mu : ℝ)
    (Z : Op (A × B)) (M : ExtOp A J H B) : Prop :=
  0 ≤ mu ∧ Z.PosSemidef ∧ (((mu : ℂ) • (1 : Op A)) - traceRight Z).PosSemidef ∧
  (Z - choi O + wireChoi N (averagedBobExtensionMarginal M)).PosSemidef ∧
  IsSymmetricBobChannelExtension (averagedBobExtensionMarginal M) M ∧
  (transposeAlice M).PosSemidef ∧ (transposeBob2 M).PosSemidef ∧ ExtensionNS M

/-- PDF pp.9–10,14–15: the six reduced operator variables on H,J1,J2. -/
structure TwoBobCoefficients (H J : Type*) where
  plus : Op (H × (J × J))
  minus : Op (H × (J × J))
  zero : Op (H × (J × J))
  one : Op (H × (J × J))
  two : Op (H × (J × J))
  three : Op (H × (J × J))

/-- Real scalar multiplication of an operator; all denominators below are real. -/
def realOperatorScale {I : Type*} (r : ℝ) (X : Op I) : Op I := (r : ℂ) • X

/-- PDF p.9, (91): the two-by-two block test, with the printed i signs. -/
def twoByTwoPauliOperator {I : Type*} (z x y w : Op I) : Op (I ⊕ I) :=
  Matrix.fromBlocks (z + w) (x - Complex.I • y) (x + Complex.I • y) (z - w)

/-- PDF p.9, (93)–(94): swap J1 and J2. -/
def swapReduced (X : Op (H × (J × J))) : Op (H × (J × J)) :=
  fun p q => X (p.1,(p.2.2,p.2.1)) (q.1,(q.2.2,q.2.1))

/-- PDF pp.9–10, (97)–(103): partial transpose H. -/
def transposeH (X : Op (H × (J × J))) : Op (H × (J × J)) :=
  fun p q => X (q.1,p.2) (p.1,q.2)

/-- PDF pp.9–10, (104)–(110): partial transpose H,J1. -/
def transposeHJ1 (X : Op (H × (J × J))) : Op (H × (J × J)) :=
  fun p q => X (q.1,(q.2.1,p.2.2)) (p.1,(p.2.1,q.2.2))

/-- PDF p.9, (95), or p.14, (192)–(193): decouple J2 by partial trace. -/
def HasMixedSecondBobFactor (X : Op (H × (J × J))) : Prop :=
  ∀ h h' j j' k k', X (h,(j,k)) (h',(j',k')) =
    (Fintype.card J : ℂ)⁻¹ * (∑ t, X (h,(j,t)) (h',(j',t))) *
      (if k = k' then 1 else 0)

/-- PDF p.9, (96), and p.14, (194): P, not a free variable. -/
def reducedP (d : ℕ) (M : TwoBobCoefficients H J) : Op (H × (J × J)) :=
  realOperatorScale (1 / (2 * (d : ℝ)))
    (realOperatorScale d M.zero + M.one + realOperatorScale (Real.sqrt ((d : ℝ)^2 - 1)) M.two)

/-- PDF p.15, (195): Q, which cannot be eliminated for correction. -/
def reducedQ (d : ℕ) (M : TwoBobCoefficients H J) : Op (H × (J × J)) :=
  realOperatorScale (1 / (2 * (d : ℝ)))
    (realOperatorScale (2*d) (M.plus + M.minus) + realOperatorScale d M.zero - M.one -
      realOperatorScale (Real.sqrt ((d : ℝ)^2 - 1)) M.two)

/-- PDF pp.9,14: CP and permutation covariance constraints, common to both SDPs. -/
def ReducedCommon (M : TwoBobCoefficients H J) : Prop :=
  M.plus.PosSemidef ∧ M.minus.PosSemidef ∧ M.zero.PosSemidef ∧
  (twoByTwoPauliOperator M.zero M.one M.two M.three).PosSemidef ∧
  swapReduced M.plus = M.plus ∧ swapReduced M.minus = M.minus ∧
  swapReduced M.zero = M.zero ∧ swapReduced M.one = M.one ∧
  swapReduced M.two = -M.two ∧ swapReduced M.three = -M.three

/-- PDF p.10, (111)–(113), or p.15, (210)–(212): the constructed L operators. -/
def reducedL (d : ℕ) (M : TwoBobCoefficients H J) : Fin 3 → Op (H × (J × J)) :=
  ![realOperatorScale ((d : ℝ)^2 - 2) M.zero + realOperatorScale d M.one +
      realOperatorScale ((d : ℝ) * Real.sqrt ((d : ℝ)^2 - 1)) M.two,
    realOperatorScale d M.zero + realOperatorScale (2*(d : ℝ)^2 - 3) M.one -
      realOperatorScale (Real.sqrt ((d : ℝ)^2 - 1)) M.two,
    M.one - realOperatorScale d M.zero - realOperatorScale (Real.sqrt ((d : ℝ)^2 - 1)) M.two]

/-- PDF p.9, (100)–(103), or p.15, (199)–(202): the constructed G operators. -/
def reducedG (d : ℕ) (M : TwoBobCoefficients H J) : Fin 4 → Op (H × (J × J)) :=
  ![transposeH (M.plus + M.minus + realOperatorScale (1/2) (M.zero - realOperatorScale d M.one)),
    transposeH (M.plus - M.minus + realOperatorScale (1/2) (M.one - realOperatorScale d M.zero)),
    realOperatorScale (Real.sqrt (3*((d : ℝ)^2 - 1))/2) (transposeH M.two),
    realOperatorScale (Real.sqrt (3*((d : ℝ)^2 - 1))/2) (transposeH M.three)]

/-- PDF p.10, (107)–(110), or p.15, (206)–(209): the constructed E operators. -/
def reducedE (d : ℕ) (M : TwoBobCoefficients H J) : Fin 4 → Op (H × (J × J)) :=
  let L := reducedL d M
  ![realOperatorScale (1/((d : ℝ)^2 - 1))
      (transposeHJ1 (realOperatorScale d (M.plus - M.minus) + realOperatorScale (1/2) (L 0))),
    realOperatorScale (1/((d : ℝ)^2 - 1))
      (transposeHJ1 (-M.plus + M.minus + realOperatorScale (1/2) (L 1))),
    realOperatorScale (1/Real.sqrt ((d : ℝ)^2 - 1))
      (transposeHJ1 (M.plus - M.minus + realOperatorScale (1/2) (L 2))),
    transposeHJ1 M.three]

/-- PDF pp.9–10, (97)–(106), or pp.14–15, (196)–(205).
The plus sign in (104)/(203) follows p.9,p.15 and (C268)-(C269) p.37;
the frozen PLAN summary mistakenly places a minus there. The minus in (105)/(204) is retained.
At d=2 the minus sector is zero and BOTH d-2 denominator constraints are absent.
SOURCE CORRECTION: Appendix C8 p.38 says remove (97); pp.10 and the preceding
sector calculation require removing (98). The present definition follows p.10. -/
def ReducedPPT (d : ℕ) (M : TwoBobCoefficients H J) : Prop :=
  (transposeH (realOperatorScale (2/((d : ℝ)+2)) M.plus + M.zero + M.one)).PosSemidef ∧
  (if d = 2 then M.minus = 0 else
    (transposeH (realOperatorScale (2/((d : ℝ)-2)) M.minus + M.one - M.zero)).PosSemidef ∧
    (transposeHJ1 (M.plus + realOperatorScale ((d : ℝ)/((d : ℝ)-2)) M.minus -
      realOperatorScale (1/2) (realOperatorScale d M.zero - M.one -
        realOperatorScale (Real.sqrt ((d : ℝ)^2-1)) M.two))).PosSemidef) ∧
  (twoByTwoPauliOperator (reducedG d M 0) (reducedG d M 1)
    (reducedG d M 2) (reducedG d M 3)).PosSemidef ∧
  (transposeHJ1 (realOperatorScale ((d : ℝ)/((d : ℝ)+2)) M.plus + M.minus +
    realOperatorScale (1/2) (realOperatorScale d M.zero - M.one -
      realOperatorScale (Real.sqrt ((d : ℝ)^2-1)) M.two))).PosSemidef ∧
  (twoByTwoPauliOperator (reducedE d M 0) (reducedE d M 1)
    (reducedE d M 2) (reducedE d M 3)).PosSemidef

/-- PDF p.15, (213)–(217): NS on the extension transported to the reduced variables.
At d=2 (214) is removed. The factors 1/2 in (215),(216) are retained. -/
def ReducedNS (d : ℕ) (M : TwoBobCoefficients H J) : Prop :=
  realOperatorScale (1/(((d : ℝ)+2)*((d : ℝ)-1))) (traceLeft (realOperatorScale 2 M.plus)) =
    realOperatorScale (1/((d : ℝ)*((d : ℝ)+1))) (traceLeft (realOperatorScale 2 M.plus + M.zero + M.one)) ∧
  (d ≠ 2 →
    realOperatorScale (1/(((d : ℝ)-2)*((d : ℝ)+1))) (traceLeft (realOperatorScale 2 M.minus)) =
    realOperatorScale (1/((d : ℝ)*((d : ℝ)-1))) (traceLeft (realOperatorScale 2 M.minus + M.zero - M.one))) ∧
  realOperatorScale (1/2) (traceLeft M.zero) =
    realOperatorScale (1/((d : ℝ)*((d : ℝ)^2-1)))
      (realOperatorScale d (1 : Op (J × J)) + traceLeft (M.minus - M.plus - M.one)) ∧
  realOperatorScale (1/2) (traceLeft M.one) =
    realOperatorScale (1/((d : ℝ)*((d : ℝ)^2-1)))
      (-(1 : Op (J × J)) + realOperatorScale d (traceLeft (M.plus - M.minus + M.one))) ∧
  traceLeft M.two = 0 ∧ traceLeft M.three = 0

/-- PDF p.9, (90)–(106), and Remark 5 p.10: teleportation reduced feasible set. -/
def ReducedTeleportFeasible (ppt : Bool) (d : ℕ) (M : TwoBobCoefficients H J) : Prop :=
  ReducedCommon M ∧ M.plus + M.minus + M.zero = 1 ∧
  HasMixedSecondBobFactor (reducedP d M) ∧ (d = 2 → M.minus = 0) ∧
  (ppt = true → ReducedPPT d M)

/-- PDF pp.14–15, (187)–(217), Remarks 11–12: correction reduced feasible set.
Dropping extra NS leaves both P and Q marginal constraints in place. -/
def ReducedCorrectionFeasible (ppt ns : Bool) (d : ℕ) (M : TwoBobCoefficients H J) : Prop :=
  ReducedCommon M ∧ traceLeft (M.plus + M.minus + M.zero) = 1 ∧
  HasMixedSecondBobFactor (reducedP d M) ∧ HasMixedSecondBobFactor (reducedQ d M) ∧
  (d = 2 → M.minus = 0) ∧ (ppt = true → ReducedPPT d M) ∧
  (ns = true → ReducedNS d M)

/-- PDF p.9, (90), and p.14, (187): Re Tr[(T^T tensor I) P]/dim J. -/
def reducedObjective (T : Op (H × J)) (P : Op (H × (J × J))) : ℝ :=
  (∑ h, ∑ h', ∑ j, ∑ j', ∑ k,
    T (h,j) (h',j') * P (h,(j,k)) (h',(j',k))).re / Fintype.card J

/-- PDF p.9, (90), including every constraint of the selected relaxation. -/
def reducedTeleportBound (ppt : Bool) (d : ℕ) (rho : Op (H × J)) : ℝ :=
  1 - sSup {v | ∃ M : TwoBobCoefficients H J, ReducedTeleportFeasible ppt d M ∧
    v = reducedObjective rho (reducedP d M)}

/-- PDF p.14, (187), including every constraint of the selected relaxation. -/
def reducedCorrectionBound (ppt ns : Bool) (d : ℕ) (N : Superop H J) : ℝ :=
  1 - sSup {v | ∃ M : TwoBobCoefficients H J, ReducedCorrectionFeasible ppt ns d M ∧
    v = reducedObjective (choi N) (reducedP d M)}

/-- PDF p.16, (220),(223): transpose only the Bob register. -/
def transposeJ (X : Op (H × J)) : Op (H × J) :=
  fun p q => X (p.1,q.2) (q.1,p.2)

/-- PDF p.16, (220): the PPT-only teleportation program. -/
def pptTeleportBound (d : ℕ) (rho : Op (H × J)) : ℝ :=
  1 - sSup {v | ∃ K : Op (H × J), K.PosSemidef ∧ (1-K).PosSemidef ∧
    (1 + realOperatorScale d (transposeJ K)).PosSemidef ∧
    (1 - realOperatorScale d (transposeJ K)).PosSemidef ∧ v = effectProb K rho}

/-- PDF pp.16–17, (223): PPT correction program, with exactly one optional NS equality. -/
def pptCorrectionBound (ns : Bool) (d : ℕ) (N : Superop H J) : ℝ :=
  1 - sSup {v | ∃ K : Op (H × J), ∃ sigma : Op H,
    K.PosSemidef ∧ IsDensityMatrix sigma ∧
    (Matrix.kronecker sigma (1 : Op J) - K).PosSemidef ∧
    (ns = true → realOperatorScale ((d : ℝ)^2) (traceLeft K) = 1) ∧
    (Matrix.kronecker sigma (1 : Op J) + realOperatorScale d (transposeJ K)).PosSemidef ∧
    (Matrix.kronecker sigma (1 : Op J) - realOperatorScale d (transposeJ K)).PosSemidef ∧
    v = effectProb K (choi N)}

/-! Sanity examples for the local definitions. These are normalization and register
checks, not proofs of the paper's results. -/

example : choi (id : Superop Unit Unit) ((),()) ((),()) = 1 := by
  simp [choi, Matrix.single]

example : averagedBobExtensionMarginal (1 : ExtOp Unit Unit Unit Unit) = 1 := by
  ext p q
  simp [averagedBobExtensionMarginal, Matrix.one_apply]
  exact Subsingleton.elim _ _

example (M : ExtOp A B C D) : transposeAlice (transposeAlice M) = M := by
  ext p q
  rfl

example (M : ExtOp A B C D) : transposeBob2 (transposeBob2 M) = M := by
  ext p q
  rfl

example (M : ExtOp A B C D) : swapExtension (swapExtension M) = M := by
  ext p q
  rfl

example (X : Op (H × (J × J))) : transposeHJ1 (transposeHJ1 X) = X := by
  ext p q
  rfl

example (X : Op (H × J)) : transposeJ (transposeJ X) = X := by
  ext p q
  rfl

example : nonidentityWeylAverage (1 : Op (Fin 2)) = (1 : Op (Fin 2)) := by
  ext i j
  simp [nonidentityWeylAverage, Matrix.one_apply, Matrix.trace] <;> split_ifs <;> norm_num

example : entFidelity (id : Superop Unit Unit) = 1 := by
  simp [entFidelity, finiteMaxEntangled, effectProb, pureDensity, idTensorSuperop,
    Matrix.mul_apply, Matrix.trace]

end QAlgorithms.Papers.Independent.Extend50.P02


