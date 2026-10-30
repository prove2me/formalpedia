-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P47
-- name    : QAlgorithms_Papers_Independent_Bridge50_P47
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T08:43:40.891295+00:00
-- url     : https://prove2.me/theorems/936ef13f-1040-4ea4-8343-d4bb6849bc0a
-- title:
--   Definitions for "Pretty strong" converse for the quantum capacity of degradable channels
-- statement:
--   The objects the formalized statements of *"Pretty strong" converse for the quantum capacity of degradable channels* (arXiv:1301.4927) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `transmissionGood`: Section II, PDF p.2: worst purified error, including all finite reference systems. The imported TransmissionCode carries positive rank and CPTP encoder/decoder fields.
--   - `EntanglementCode`: Section II, PDF p.2: entanglement-generation data; mixed joint inputs are allowed.
--   - `EntanglementCode.output`: Section II, PDF p.2: actual decoded entanglement-generating state.
--   - `EntanglementCode.error`: Section II, PDF p.2: root-fidelity purified error from the normalized entangled target.
--   - `EntanglementCode.Valid`: Section II, PDF p.2: physical validity is independent of the error tolerance.
--   - `logTransmissionSize`: Section II, PDF p.2: log of the optimal transmission dimension. Used only for CPTP N on nonzero systems and 0≤epsilon<1; then this real supremum is nonempty, bounded, and equals the logarithm of the maximum dimension. Outside that domain no operational interpretation of this total helper is asserted.
--   - `logEntanglementSize`: Section II, PDF p.2: log of the optimal entanglement-generation dimension. The real supremum is used only for CPTP N, nonzero systems and 0≤epsilon<1; there the dimension set is nonempty and bounded.
--   - `logN`: Section II, PDF p.2: log N(n,epsilon).
--   - `logNE`: Section II, PDF p.2: log N_E(n,epsilon).
--   - `StrongConverse`: Section III, PDF p.3: strong converse, equivalently the optimal fixed-error entanglement-generation limsup rate is at most Q for every error<1.
--   - `decodingMarginal`: Section VI, PDF p.8: the actual XX-hat marginal, tracing only the environment.
--   - `privacyMarginal`: Section VI, PDF p.8: XE marginal, tracing the decoded message.
--   - `privacyTarget`: Section VI, PDF p.8: uniform X tensor a common normalized environment state.
--   - `PrivateGood`: Section VI, PDF p.8: separate averaged error/privacy criteria. The common privacy witness is optimized independently of the decoding marginal.
--   - `logM`: Section VI, PDF p.8: log M(n,epsilon,delta). For an isometric finite channel and 0≤epsilon,delta<1 the feasible positive message numbers are nonempty and bounded, so this real supremum is the logarithm of their maximum.
--   - `individualError`: Section VI, PDF pp.8–9: individual error of message m in purified distance.
--   - `IndividualGood`: Section VI, PDF pp.8–9: the same sigma must work for every individual message.
--   - `RandomizedFrom`: Section VI, PDF pp.8–9: randomized encoding using distributions on the original messages. New signal states are actual convex combinations of old ones.
--   - `IsDegradingDilation`: Section IV, PDF p.4: V actually dilates a degrading map for the fixed U.
--   - `swapSign`: Section VII, PDF p.10: the two possible global phases.
--   - `IsTypeIFactorization`: Definition 16, PDF p.10: type-I witnesses, using the well-typed VU. Both the symmetric and the antisymmetric range are allowed.
--   - `IsTypeI`: Definition 16, PDF p.10: existential degrading dilation, whose environment need not be minimal. Fin f represents every finite physical degrading environment.
--   - `testKet`: Lemmas 1 and 18, PDF pp.4,11: test vector after VU, grouped as AF:E'E. The E' factor precedes E; these are identified copies and the swap is unchanged.
--   - `supportDimension`: Lemma 18, PDF p.11: dimension of G, the actual support of psi_0^{AF}.
--   - `Associated`: Lemma 18, PDF p.11: W is associated to the specified full-rank test vector. J identifies Fin(dim G) with the actual AF support; chi0 is its chosen purification. No factorization for subsequent test vectors is a premise.
--   - `ExponentProfile`: Section VII, PDF p.12: one profile on [0,infinity), continuous and nondecreasing there, with value zero at zero. Values at negative c are unused.
--   - `exponentialRate`: Section VII, PDF p.12: the exact error 1-2^(-cn), in purified distance.
--   - `SymmetricIndex`: Section VII, PDF p.12: an explicit orthonormal basis of Sym^2(C^d).
--   - `universalSymmetricDilation`: Section VII, PDF p.12: the actual inclusion Sym^2(E) into E tensor E, in its standard diagonal/off-diagonal orthonormal basis.
--   - `halfErasure`: Section IX, PDF p.13: free 50%-50% erasure side channel of arbitrary positive input dimension m, with a flag orthogonal to every input basis state.
--   - `erasureSideCode`: Section IX, PDF p.13: explicit side-assisted construction. The original channel is fed a fixed pure state. Half of Phi_m enters the free erasure channel; the erasure branch is decoded to |0><0| after discarding the original output.
-- source:
--   "Pretty strong" converse for the quantum capacity of degradable channels, arXiv:1301.4927v3, https://arxiv.org/abs/1301.4927v3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P80

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder
open Filter

namespace QAlgorithms.Papers.Independent.Bridge50.P47

open QAlgorithms.Papers.Independent.Information100

variable {A B E F R I O : Type*}
variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]
variable [Fintype R] [DecidableEq R] [Fintype I] [DecidableEq I]
variable [Fintype O] [DecidableEq O]

/-- Section II, PDF p.2: worst purified error, including all finite reference systems.
The imported TransmissionCode carries positive rank and CPTP encoder/decoder fields. -/
def transmissionGood (N : Superop I O) (code : P80.TransmissionCode I O)
    (epsilon : ℝ) : Prop :=
  ∀ r : ℕ, 0 < r →
    ∀ rho : Matrix (Fin r × Fin code.M) (Fin r × Fin code.M) ℂ,
      IsDensityMatrix rho → P67.purifiedDistance rho
        (idTensorSuperop (code.decoder ∘ N ∘ code.encoder) rho) ≤ epsilon

/-- Section II, PDF p.2: entanglement-generation data; mixed joint inputs are allowed. -/
structure EntanglementCode (I O : Type*) where
  dimension : ℕ
  input : Matrix (Fin dimension × I) (Fin dimension × I) ℂ
  decoder : Superop O (Fin dimension)

/-- Section II, PDF p.2: actual decoded entanglement-generating state. -/
def EntanglementCode.output (N : Superop I O) (code : EntanglementCode I O) :=
  idTensorSuperop code.decoder (idTensorSuperop N code.input)

/-- Section II, PDF p.2: root-fidelity purified error from the normalized entangled target. -/
def EntanglementCode.error (N : Superop I O) (code : EntanglementCode I O) : ℝ :=
  P67.purifiedDistance (code.output N)
    (pureDensity (P67.maximallyEntangledKey code.dimension))

/-- Section II, PDF p.2: physical validity is independent of the error tolerance. -/
def EntanglementCode.Valid (code : EntanglementCode I O) : Prop :=
  0 < code.dimension ∧ IsDensityMatrix code.input ∧ IsChannel code.decoder

/-- Section II, PDF p.2: log of the optimal transmission dimension.
Used only for CPTP N on nonzero systems and 0≤epsilon<1; then this real
supremum is nonempty, bounded, and equals the logarithm of the maximum dimension.
Outside that domain no operational interpretation of this total helper is asserted. -/
def logTransmissionSize (N : Superop I O) (epsilon : ℝ) : ℝ :=
  sSup {z | ∃ code : P80.TransmissionCode I O, transmissionGood N code epsilon ∧
    z = Real.logb 2 code.M}

/-- Section II, PDF p.2: log of the optimal entanglement-generation dimension.
The real supremum is used only for CPTP N, nonzero systems and 0≤epsilon<1;
there the dimension set is nonempty and bounded. -/
def logEntanglementSize (N : Superop I O) (epsilon : ℝ) : ℝ :=
  sSup {z | ∃ code : EntanglementCode I O, code.Valid ∧ code.error N ≤ epsilon ∧
    z = Real.logb 2 code.dimension}

/-- Section II, PDF p.2: log N(n,epsilon). -/
def logN (U : Matrix (B × E) A ℂ) (n : ℕ) (epsilon : ℝ) : ℝ :=
  logTransmissionSize (P67.receiverChannel (P67.dilationPower U n)) epsilon

/-- Section II, PDF p.2: log N_E(n,epsilon). -/
def logNE (U : Matrix (B × E) A ℂ) (n : ℕ) (epsilon : ℝ) : ℝ :=
  logEntanglementSize (P67.receiverChannel (P67.dilationPower U n)) epsilon

/-- Section III, PDF p.3: strong converse, equivalently the optimal
fixed-error entanglement-generation limsup rate is at most Q for every error<1. -/
def StrongConverse (U : Matrix (B × E) A ℂ) : Prop :=
  ∀ epsilon : ℝ, 0 ≤ epsilon → epsilon < 1 →
    limsup (fun n : ℕ => logNE U n epsilon / (n : ℝ)) atTop ≤ P80.quantumCapacity (P67.receiverChannel U)

/-- Section VI, PDF p.8: the actual XX-hat marginal, tracing only the environment. -/
def decodingMarginal (U : Matrix (B × E) A ℂ) {n : ℕ}
    (code : P67.PrivateCode A B n) :
    Matrix (Fin code.M × Fin code.M) (Fin code.M × Fin code.M) ℂ :=
  fun x y => ∑ e : Fin n → E,
    P67.jointOutput U code (x.1, x.2, e) (y.1, y.2, e)

/-- Section VI, PDF p.8: XE marginal, tracing the decoded message. -/
def privacyMarginal (U : Matrix (B × E) A ℂ) {n : ℕ}
    (code : P67.PrivateCode A B n) :
    Matrix (Fin code.M × (Fin n → E)) (Fin code.M × (Fin n → E)) ℂ :=
  fun x y => ∑ j : Fin code.M,
    P67.jointOutput U code (x.1, j, x.2) (y.1, j, y.2)

/-- Section VI, PDF p.8: uniform X tensor a common normalized environment state. -/
def privacyTarget (m : ℕ) (sigma : Matrix E E ℂ) :
    Matrix (Fin m × E) (Fin m × E) ℂ :=
  fun x y => if x.1 = y.1 then (m : ℂ)⁻¹ * sigma x.2 y.2 else 0

/-- Section VI, PDF p.8: separate averaged error/privacy criteria. The common
privacy witness is optimized independently of the decoding marginal. -/
def PrivateGood (U : Matrix (B × E) A ℂ) {n : ℕ}
    (code : P67.PrivateCode A B n) (epsilon delta : ℝ) : Prop :=
  code.Valid ∧
  P67.purifiedDistance (decodingMarginal U code) (P67.idealClassicalKey code.M)
    ≤ epsilon ∧
  ∃ sigma : Matrix (Fin n → E) (Fin n → E) ℂ, IsDensityMatrix sigma ∧
    P67.purifiedDistance (privacyMarginal U code) (privacyTarget code.M sigma) ≤ delta

/-- Section VI, PDF p.8: log M(n,epsilon,delta). For an isometric finite
channel and 0≤epsilon,delta<1 the feasible positive message numbers are nonempty
and bounded, so this real supremum is the logarithm of their maximum. -/
def logM (U : Matrix (B × E) A ℂ) (n : ℕ) (epsilon delta : ℝ) : ℝ :=
  sSup {z | ∃ code : P67.PrivateCode A B n, PrivateGood U code epsilon delta ∧
    z = Real.logb 2 code.M}

/-- Section VI, PDF pp.8–9: individual error of message m in purified distance. -/
def individualError (U : Matrix (B × E) A ℂ) {n : ℕ}
    (code : P67.PrivateCode A B n) (m : Fin code.M) : ℝ :=
  Real.sqrt (1 - effectProb (code.measurement m) (P67.receiverChannel (P67.dilationPower U n) (code.messages m)))

/-- Section VI, PDF pp.8–9: the same sigma must work for every individual message. -/
def IndividualGood (U : Matrix (B × E) A ℂ) {n : ℕ}
    (code : P67.PrivateCode A B n) (epsilon delta : ℝ) : Prop :=
  code.Valid ∧ ∃ sigma : Matrix (Fin n → E) (Fin n → E) ℂ,
    IsDensityMatrix sigma ∧ ∀ m : Fin code.M,
      individualError U code m < epsilon ∧
      P67.purifiedDistance
        (P67.complementaryChannel (P67.dilationPower U n) (code.messages m))
        sigma < delta

/-- Section VI, PDF pp.8–9: randomized encoding using distributions on the
original messages. New signal states are actual convex combinations of old ones. -/
def RandomizedFrom {n : ℕ} (oldCode newCode : P67.PrivateCode A B n) : Prop :=
  ∃ weights : Fin newCode.M → Fin oldCode.M → ℝ,
    (∀ m i, 0 ≤ weights m i) ∧ (∀ m, ∑ i, weights m i = 1) ∧
    (∀ m, newCode.messages m = ∑ i, (weights m i : ℂ) • oldCode.messages i)

/-- Section IV, PDF p.4: V actually dilates a degrading map for the fixed U. -/
def IsDegradingDilation (U : Matrix (B × E) A ℂ) (V : Matrix (F × E) B ℂ) : Prop :=
  P67.IsIsometry V ∧
    ∀ rho, traceLeft (V * P67.receiverChannel U rho * Vᴴ) =
      P67.complementaryChannel U rho

/-- Section VII, PDF p.10: the two possible global phases. -/
def swapSign (negative : Bool) : ℂ := if negative then -1 else 1

/-- Definition 16, PDF p.10: type-I witnesses, using the well-typed VU.
Both the symmetric and the antisymmetric range are allowed. -/
def IsTypeIFactorization (U : Matrix (B × E) A ℂ)
    (V : Matrix (F × E) B ℂ) (negative : Bool) : Prop :=
  P67.IsIsometry U ∧ IsDegradingDilation U V ∧
    Matrix.kronecker (1 : Matrix F F ℂ) (P67.environmentSwap (E := E)) *
      P67.symmetricDilation U V = swapSign negative • P67.symmetricDilation U V

/-- Definition 16, PDF p.10: existential degrading dilation, whose environment
need not be minimal. Fin f represents every finite physical degrading environment. -/
def IsTypeI (U : Matrix (B × E) A ℂ) : Prop :=
  ∃ f : ℕ, 0 < f ∧ ∃ V : Matrix (Fin f × E) B ℂ,
    ∃ negative : Bool, IsTypeIFactorization U V negative

/-- Lemmas 1 and 18, PDF pp.4,11: test vector after VU, grouped as AF:E'E.
The E' factor precedes E; these are identified copies and the swap is unchanged. -/
def testKet (U : Matrix (B × E) A ℂ) (V : Matrix (F × E) B ℂ)
    (phi : EuclideanSpace ℂ (R × A)) : EuclideanSpace ℂ ((R × F) × (E × E)) :=
  WithLp.toLp 2 (fun x => ∑ a : A,
    P67.symmetricDilation U V (x.1.2, x.2.1, x.2.2) a * phi (x.1.1, a))

/-- Lemma 18, PDF p.11: dimension of G, the actual support of psi_0^{AF}. -/
def supportDimension (U : Matrix (B × E) A ℂ) (V : Matrix (F × E) B ℂ)
    (phi0 : EuclideanSpace ℂ (A × A)) : ℕ :=
  Matrix.rank (traceRight (pureDensity (testKet U V phi0)))

/-- Lemma 18, PDF p.11: W is associated to the specified full-rank test
vector. J identifies Fin(dim G) with the actual AF support; chi0 is its chosen
purification. No factorization for subsequent test vectors is a premise. -/
def Associated (U : Matrix (B × E) A ℂ) (V : Matrix (F × E) B ℂ)
    (phi0 : EuclideanSpace ℂ (A × A))
    (W : Matrix (E × E) (Fin (supportDimension U V phi0)) ℂ) : Prop :=
  let k := supportDimension U V phi0
  ∃ J : Matrix (A × F) (Fin k) ℂ, P67.IsIsometry J ∧
    J * Jᴴ * traceRight (pureDensity (testKet U V phi0)) =
      traceRight (pureDensity (testKet U V phi0)) ∧
    ∃ chi0 : EuclideanSpace ℂ (Fin k × Fin k), ‖chi0‖ = 1 ∧
      testKet U V phi0 = WithLp.toLp 2 ((Matrix.kronecker J W).mulVec chi0)

/-- Section VII, PDF p.12: one profile on [0,infinity), continuous and
nondecreasing there, with value zero at zero. Values at negative c are unused. -/
def ExponentProfile (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Set.Ici 0) ∧ MonotoneOn f (Set.Ici 0) ∧ f 0 = 0

/-- Section VII, PDF p.12: the exact error 1-2^(-cn), in purified distance. -/
def exponentialRate (U : Matrix (B × E) A ℂ) (c : ℝ) (n : ℕ) : ℝ :=
  logNE U n (1 - Real.rpow 2 (-c * (n : ℝ))) / (n : ℝ)

/-- Section VII, PDF p.12: an explicit orthonormal basis of Sym^2(C^d). -/
abbrev SymmetricIndex (d : ℕ) := {p : Fin d × Fin d // p.1 ≤ p.2}

/-- Section VII, PDF p.12: the actual inclusion Sym^2(E) into E tensor E,
in its standard diagonal/off-diagonal orthonormal basis. -/
def universalSymmetricDilation (d : ℕ) :
    Matrix (Fin d × Fin d) (SymmetricIndex d) ℂ :=
  fun x y => if y.1.1 = y.1.2 then
    (if x = y.1 then 1 else 0)
  else if x = y.1 ∨ x = (y.1.2, y.1.1) then ((Real.sqrt 2)⁻¹ : ℂ) else 0

/-- Section IX, PDF p.13: free 50%-50% erasure side channel of arbitrary
positive input dimension m, with a flag orthogonal to every input basis state. -/
def halfErasure (m : ℕ) : Superop (Fin m) (Option (Fin m)) :=
  P67.receiverChannel (P67.erasureDilation (A := Fin m) (1 / 2))

/-- Section IX, PDF p.13: explicit side-assisted construction. The original
channel is fed a fixed pure state. Half of Phi_m enters the free erasure channel;
the erasure branch is decoded to |0><0| after discarding the original output. -/
def erasureSideCode [Nonempty A] (n m : ℕ) (hm : 0 < m) :
    EntanglementCode ((Fin n → A) × Fin m) ((Fin n → B) × Option (Fin m)) where
  dimension := m
  input := fun x y =>
    if x.2.1 = (fun _ => Classical.choice (inferInstance : Nonempty A)) ∧
      y.2.1 = (fun _ => Classical.choice (inferInstance : Nonempty A)) then
      pureDensity (P67.maximallyEntangledKey m) (x.1, x.2.2) (y.1, y.2.2)
    else 0
  decoder := fun rho i j =>
    traceLeft rho (some i) (some j) +
      if i = (⟨0, hm⟩ : Fin m) ∧ j = (⟨0, hm⟩ : Fin m) then
        traceLeft rho none none else 0

/-- Sanity: the side-assisted code has exactly its prescribed rank. -/
example [Nonempty A] (n m : ℕ) (hm : 0 < m) :
    (erasureSideCode (A := A) (B := B) n m hm).dimension = m := rfl

/-- Sanity: validity excludes empty entanglement and private codes. -/
example (code : EntanglementCode I O) (h : code.Valid) : 0 < code.dimension := h.1

/-- Sanity: the zero environment matrix gives the zero privacy target. -/
example (m : ℕ) : privacyTarget m (0 : Matrix E E ℂ) = 0 := by
  ext x y
  simp [privacyTarget]

/-- Sanity: applying the two dilations to the zero vector gives zero. -/
example (U : Matrix (B × E) A ℂ) (V : Matrix (F × E) B ℂ) :
    testKet U V (0 : EuclideanSpace ℂ (R × A)) = 0 := by
  ext x
  simp [testKet]

/-- Sanity: zero input remains zero under the actual block channel. -/
example (U : Matrix (B × E) A ℂ) (n : ℕ) : P67.receiverChannel (P67.dilationPower U n) 0 = 0 := by
  ext x y
  simp [P67.receiverChannel, traceRight]

/-- Sanity: one-component mixtures preserve their input density exactly. -/
example (rho : Matrix A A ℂ) : (∑ _i : Fin 1, (1 : ℂ) • rho) = rho := by simp

/-- Sanity: the universal symmetric inclusion in dimension one is identity. -/
example (x : Fin 1 × Fin 1) (y : SymmetricIndex 1) :
    universalSymmetricDilation 1 x y = 1 := by
  simp [universalSymmetricDilation, Subsingleton.elim x y.1,
    Subsingleton.elim y.1.1 y.1.2]

/-- Sanity: the two type-I phases include the antisymmetric sign. -/
example : swapSign true = -1 ∧ swapSign false = 1 := by simp [swapSign]

end QAlgorithms.Papers.Independent.Bridge50.P47


