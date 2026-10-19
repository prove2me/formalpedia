-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Information100_P06
-- name    : QAlgorithms_Papers_Independent_Information100_P06
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T09:26:13.183994+00:00
-- url     : https://prove2.me/theorems/a1a05fb9-3cc5-420d-82ea-81a7771ea851
-- title:
--   Definitions for Universal Improvement of Channel Fidelity via Entanglement Assistance
-- statement:
--   The objects the formalized statements of *Universal Improvement of Channel Fidelity via Entanglement Assistance* (arXiv:2610.05669) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Choi`: PDF pp.12–13, Eqs.66–72: operators representing normalized Choi matrices.
--   - `Below`: PDF p.14, Eq.80: positive-semidefinite ordering.
--   - `traceOutput`: PDF p.12: trace over the output factor, retaining all input coherences.
--   - `IsChannelChoi`: PDF pp.12–13: the normalized Choi characterization of a CPTP channel. All systems in the statements below have strictly positive dimension.
--   - `IsOperationChoi`: PDF p.13, Definition 3: the normalized Choi characterization of a CPTNI map.
--   - `amplify`: PDF p.13, Definition 3: identity supermap on the arbitrary ancilla R0 → R1, tensored with the normalized-Choi action D, with factors regrouped.
--   - `Superinstrument`: PDF p.13, Definition 3: the full physical two-outcome superinstrument. Both branches are completely CP preserving and completely CPTNI preserving; their sum is completely CPTP preserving. These are laws, not output-fidelity hypotheses.
--   - `FreeSet`: PDF pp.8,13: a nonempty set of free CPTP channels on one dynamical system.
--   - `IsRNG`: PDF pp.8,13–14: successful RNG branches preserve the nonnegative free cone. In particular, zero is permitted without any division by its trace.
--   - `projectiveRobustness`: PDF p.14, Eq.80: projective robustness. An empty feasible set gives +∞, not the real-number default zero. Both sandwich multipliers are nonnegative.
--   - `freeOverlap`: PDF p.14, Eq.84: free-channel overlap support value. On the source's intended closed free sets this is its maximum. Using the supremum also makes the numeric quantity well-defined without silently assuming attainment.
--   - `fidelityCeiling`: PDF p.14, Eq.84, with the endpoint conventions obtained from its CP sandwich: infinity gives ceiling one; finite robustness and zero free overlap give zero. The free-overlap-one case has ceiling one.
--   - `tensorChoi`: PDF pp.14–15: tensor product of normalized Choi matrices, regrouped as (input1,input2) followed by (output1,output2).
--   - `supportProjection`: PDF p.15: support projection of a positive Choi matrix via spectral functional calculus. The spectrum is finite, so this function is continuous on that spectrum, including when zero is an eigenvalue.
--   - `supportValue`: PDF p.15, below Eq.91: free overlap with the target's support projection.
--   - `sdpBase`: PDF p.15, Eqs.89,100: common SDP constraints, retaining d = input system dimension and a normalized input density matrix sigma.
--   - `exactFeasible`: PDF p.15, Eqs.88–91: exact-conversion feasible region.
--   - `xiExact`: PDF p.15, Eq.88: objective value of the exact-conversion SDP.
--   - `approximateFeasible`: PDF pp.15–16, Eqs.99–102: approximate pure-target feasible region. The equality uses the requested fidelity threshold, not an achieved output as an extra parameter.
--   - `xiApproximate`: PDF p.15, Eq.99: objective is Tr(Z J_N), with Phi entering through v. This corrects the printed label Xi_epsilon(N,V_F(Nprime)^(-1)).
--   - `Transition`: PDF pp.6–7: classical transition probabilities, output label first.
--   - `IsClassicalChannel`: PDF p.6, Eq.35: nonnegative conditional probabilities summing to one.
--   - `classicalFidelity`: PDF p.6, Eq.36: minimum correct-transmission probability. This is not reference-assisted quantum fidelity of the dephasing embedding.
--   - `IdentityBiased`: PDF p.6: strict diagonal bias in each input column.
--   - `agreementSuccess`: PDF p.6, Eqs.37,40: probability that all received symbols agree, averaged over the uniformly random transmitted label.
--   - `agreementBranch`: PDF p.6, protocol and Eq.38, extended to n uses. Share a uniform symbol r. On input k encode a = r-k in every register. Accept only a common received symbol b and decode r-b = k+a-b. This finite sum is the actual successful branch of that shared-randomness algorithm, before conditioning.
--   - `agreementOutput`: PDF p.6, Eq.38: condition the constructed branch on its success event.
--   - `classicalTwirl`: PDF p.7, Eq.44: average conjugation by all label permutations. Replacing permutations by their inverses gives the same finite average.
--   - `symmetricChannel`: PDF p.7, Eq.45: d-ary symmetric channel, with fidelity parameter f.
--   - `classicalAverage`: PDF p.7, below Eq.45: average correct-transmission probability.
--   - `symmetricSuccess`: PDF p.7, Eq.46 (and quantum Eqs.25–26 with m=d²): the common agreement denominator and the conditional correct-transmission fraction.
-- source:
--   Universal Improvement of Channel Fidelity via Entanglement Assistance, arXiv:2610.05669v1, https://arxiv.org/abs/2610.05669v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity
import Definitions.Def_QAlgorithms_Defs_Information

/-!
Statements from Chen and Chitambar, arXiv:2610.05669v1.
Paper-local definitions use normalized Choi matrices, with input index first.
The complete superinstrument conditions quantify over both input and output
ancillas. No condition on a particular channel substitutes for physicality.
-/

noncomputable section

open scoped Matrix ComplexOrder ENNReal Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Information100.P06

/-- PDF pp.12–13, Eqs.66–72: operators representing normalized Choi matrices. -/
abbrev Choi (I O : Type) := Matrix (I × O) (I × O) ℂ

/-- PDF p.14, Eq.80: positive-semidefinite ordering. -/
def Below {I : Type} [Fintype I] (X Y : Matrix I I ℂ) : Prop :=
  (Y - X).PosSemidef

/-- PDF p.12: trace over the output factor, retaining all input coherences. -/
def traceOutput {I O : Type} [Fintype O] (X : Choi I O) : Matrix I I ℂ :=
  fun i j => ∑ o, X (i,o) (j,o)

/-- PDF pp.12–13: the normalized Choi characterization of a CPTP channel.
All systems in the statements below have strictly positive dimension. -/
def IsChannelChoi {I O : Type} [Fintype I] [Fintype O] [DecidableEq I]
    (X : Choi I O) : Prop :=
  X.PosSemidef ∧ traceOutput X = ((Fintype.card I : ℂ)⁻¹) • 1

/-- PDF p.13, Definition 3: the normalized Choi characterization of a CPTNI map. -/
def IsOperationChoi {I O : Type} [Fintype I] [Fintype O] [DecidableEq I]
    (X : Choi I O) : Prop :=
  X.PosSemidef ∧ Below (traceOutput X) (((Fintype.card I : ℂ)⁻¹) • 1)

/-- PDF p.13, Definition 3: identity supermap on the arbitrary ancilla
R0 → R1, tensored with the normalized-Choi action D, with factors regrouped. -/
def amplify {A0 A1 B0 B1 : Type}
    (D : Choi A0 A1 →ₗ[ℂ] Choi B0 B1) (r s : ℕ)
    (X : Choi (Fin r × A0) (Fin s × A1)) : Choi (Fin r × B0) (Fin s × B1) :=
  fun p q =>
    D (fun a b => X ((p.1.1,a.1),(p.2.1,a.2))
      ((q.1.1,b.1),(q.2.1,b.2))) (p.1.2,p.2.2) (q.1.2,q.2.2)

/-- PDF p.13, Definition 3: the full physical two-outcome superinstrument.
Both branches are completely CP preserving and completely CPTNI preserving;
their sum is completely CPTP preserving. These are laws, not output-fidelity
hypotheses. -/
structure Superinstrument (A0 A1 B0 B1 : Type)
    [Fintype A0] [Fintype A1] [Fintype B0] [Fintype B1]
    [DecidableEq A0] [DecidableEq B0] where
  success : Choi A0 A1 →ₗ[ℂ] Choi B0 B1
  failure : Choi A0 A1 →ₗ[ℂ] Choi B0 B1
  successCP : QAlgorithms.Entanglement.IsCompletelyPositive success
  failureCP : QAlgorithms.Entanglement.IsCompletelyPositive failure
  successComplete : ∀ r s : ℕ, 0 < r → 0 < s →
    ∀ X : Choi (Fin r × A0) (Fin s × A1), IsChannelChoi X →
      IsOperationChoi (amplify success r s X)
  failureComplete : ∀ r s : ℕ, 0 < r → 0 < s →
    ∀ X : Choi (Fin r × A0) (Fin s × A1), IsChannelChoi X →
      IsOperationChoi (amplify failure r s X)
  totalComplete : ∀ r s : ℕ, 0 < r → 0 < s →
    ∀ X : Choi (Fin r × A0) (Fin s × A1), IsChannelChoi X →
      IsChannelChoi (amplify success r s X + amplify failure r s X)

/-- PDF pp.8,13: a nonempty set of free CPTP channels on one dynamical system. -/
structure FreeSet (I O : Type) [Fintype I] [Fintype O] [DecidableEq I] where
  carrier : Set (Choi I O)
  nonempty : carrier.Nonempty
  channels : ∀ X ∈ carrier, IsChannelChoi X

/-- PDF pp.8,13–14: successful RNG branches preserve the nonnegative free
cone. In particular, zero is permitted without any division by its trace. -/
def IsRNG {A0 A1 B0 B1 : Type}
    [Fintype A0] [Fintype A1] [Fintype B0] [Fintype B1]
    [DecidableEq A0] [DecidableEq B0]
    (F : FreeSet A0 A1) (G : FreeSet B0 B1)
    (D : Choi A0 A1 →ₗ[ℂ] Choi B0 B1) : Prop :=
  ∀ M ∈ F.carrier, ∃ t : ℝ, 0 ≤ t ∧
    ∃ Mout ∈ G.carrier, D M = (t : ℂ) • Mout

/-- PDF p.14, Eq.80: projective robustness. An empty feasible set gives +∞,
not the real-number default zero. Both sandwich multipliers are nonnegative. -/
def projectiveRobustness {I O : Type} [Fintype I] [Fintype O] [DecidableEq I]
    (F : FreeSet I O) (N : Choi I O) : ℝ≥0∞ :=
  sInf {g : ℝ≥0∞ | ∃ gamma lambda : NNReal, g = (gamma : ℝ≥0∞) ∧
    ∃ M ∈ F.carrier, Below N ((lambda : ℂ) • M) ∧
      Below ((lambda : ℂ) • M) ((gamma : ℂ) • N)}

/-- PDF p.14, Eq.84: free-channel overlap support value. On the source's
intended closed free sets this is its maximum. Using the supremum also makes
the numeric quantity well-defined without silently assuming attainment. -/
def freeOverlap {I O : Type} [Fintype I] [Fintype O] [DecidableEq I]
    (F : FreeSet I O) (Phi : Choi I O) : ℝ :=
  sSup {v : ℝ | ∃ M ∈ F.carrier, v = QAlgorithms.effectProb M Phi}

/-- PDF p.14, Eq.84, with the endpoint conventions obtained from its CP
sandwich: infinity gives ceiling one; finite robustness and zero free overlap
give zero. The free-overlap-one case has ceiling one. -/
def fidelityCeiling (omega : ℝ≥0∞) (fc : ℝ) : ℝ :=
  if omega = ⊤ then 1 else if fc = 1 then 1 else
    omega.toReal * fc / (omega.toReal * fc + 1 - fc)

/-- PDF pp.14–15: tensor product of normalized Choi matrices, regrouped
as (input1,input2) followed by (output1,output2). -/
def tensorChoi {I1 O1 I2 O2 : Type}
    (X : Choi I1 O1) (Y : Choi I2 O2) : Choi (I1 × I2) (O1 × O2) :=
  fun p q => X (p.1.1,p.2.1) (q.1.1,q.2.1) *
    Y (p.1.2,p.2.2) (q.1.2,q.2.2)

/-- PDF p.15: support projection of a positive Choi matrix via spectral
functional calculus. The spectrum is finite, so this function is continuous
on that spectrum, including when zero is an eigenvalue. -/
def supportProjection {I : Type} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) : Matrix I I ℂ :=
  cfc (fun t : ℝ => if t = 0 then 0 else 1) X

/-- PDF p.15, below Eq.91: free overlap with the target's support projection. -/
def supportValue {I O : Type} [Fintype I] [Fintype O] [DecidableEq I]
    [DecidableEq O] (F : FreeSet I O) (N : Choi I O) : ℝ :=
  freeOverlap F (supportProjection N)

/-- PDF p.15, Eqs.89,100: common SDP constraints, retaining d = input
system dimension and a normalized input density matrix sigma. -/
def sdpBase {I O : Type} [Fintype I] [Fintype O] [DecidableEq I]
    [DecidableEq O] (W Z : Choi I O) : Prop :=
  ∃ sigma : Matrix I I ℂ, QAlgorithms.IsDensityMatrix sigma ∧
    W.PosSemidef ∧ Below W Z ∧
    Below Z ((Fintype.card I : ℂ) •
      Matrix.kronecker sigma (1 : Matrix O O ℂ))

/-- PDF p.15, Eqs.88–91: exact-conversion feasible region. -/
def exactFeasible {I O : Type} [Fintype I] [Fintype O] [DecidableEq I]
    [DecidableEq O] (F : FreeSet I O) (N : Choi I O) (v : ℝ)
    (W Z : Choi I O) : Prop :=
  sdpBase W Z ∧ QAlgorithms.effectProb W N = QAlgorithms.effectProb Z N ∧
    ∀ M ∈ F.carrier, QAlgorithms.effectProb W M ≤ v * QAlgorithms.effectProb Z M

/-- PDF p.15, Eq.88: objective value of the exact-conversion SDP. -/
def xiExact {I O : Type} [Fintype I] [Fintype O] [DecidableEq I]
    [DecidableEq O] (F : FreeSet I O) (N : Choi I O) (v : ℝ) : ℝ :=
  sSup {q : ℝ | ∃ W Z, exactFeasible F N v W Z ∧ q = QAlgorithms.effectProb W N}

/-- PDF pp.15–16, Eqs.99–102: approximate pure-target feasible region.
The equality uses the requested fidelity threshold, not an achieved output
as an extra parameter. -/
def approximateFeasible {I O : Type} [Fintype I] [Fintype O] [DecidableEq I]
    [DecidableEq O] (F : FreeSet I O) (N : Choi I O) (f v : ℝ)
    (W Z : Choi I O) : Prop :=
  sdpBase W Z ∧ QAlgorithms.effectProb W N = f * QAlgorithms.effectProb Z N ∧
    ∀ M ∈ F.carrier, QAlgorithms.effectProb W M ≤ v * QAlgorithms.effectProb Z M

/-- PDF p.15, Eq.99: objective is Tr(Z J_N), with Phi entering through v.
This corrects the printed label Xi_epsilon(N,V_F(Nprime)^(-1)). -/
def xiApproximate {I O : Type} [Fintype I] [Fintype O] [DecidableEq I]
    [DecidableEq O] (F : FreeSet I O) (N : Choi I O) (f v : ℝ) : ℝ :=
  sSup {q : ℝ | ∃ W Z, approximateFeasible F N f v W Z ∧ q = QAlgorithms.effectProb Z N}

/-- Sanity: the order predicate includes the zero cone endpoint. -/
example {I : Type} [Fintype I] (X : Matrix I I ℂ) : Below X X := by
  simp only [Below, sub_self]
  exact Matrix.PosSemidef.zero

/-- Sanity: a zero successful branch is RNG, without normalization by zero. -/
example {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]
    [DecidableEq I] [DecidableEq J] (F : FreeSet I O) (G : FreeSet J K) :
    IsRNG F G (0 : Choi I O →ₗ[ℂ] Choi J K) := by
  intro M hM
  obtain ⟨Mout,hMout⟩ := G.nonempty
  exact ⟨0, le_rfl, Mout, hMout, by simp⟩

/-- Sanity: infinite robustness never invokes infinity/infinity. -/
example (fc : ℝ) : fidelityCeiling ⊤ fc = 1 := by
  simp [fidelityCeiling]

/-- Sanity: finite robustness and zero free overlap give a zero ceiling. -/
example (omega : ℝ≥0∞) (h : omega ≠ ⊤) : fidelityCeiling omega 0 = 0 := by
  simp [fidelityCeiling, h]

/-- PDF pp.6–7: classical transition probabilities, output label first. -/
abbrev Transition (d : ℕ) := ZMod d → ZMod d → ℝ

/-- PDF p.6, Eq.35: nonnegative conditional probabilities summing to one. -/
def IsClassicalChannel {d : ℕ} [NeZero d] (P : Transition d) : Prop :=
  (∀ b a, 0 ≤ P b a) ∧ ∀ a, ∑ b, P b a = 1

/-- PDF p.6, Eq.36: minimum correct-transmission probability. This is not
reference-assisted quantum fidelity of the dephasing embedding. -/
def classicalFidelity {d : ℕ} [NeZero d] (P : Transition d) : ℝ :=
  sInf (Set.range fun a => P a a)

/-- PDF p.6: strict diagonal bias in each input column. -/
def IdentityBiased {d : ℕ} (P : Transition d) : Prop :=
  ∀ a b, b ≠ a → P b a < P a a

/-- PDF p.6, Eqs.37,40: probability that all received symbols agree,
averaged over the uniformly random transmitted label. -/
def agreementSuccess {d n : ℕ} [NeZero d] (P : Fin n → Transition d) : ℝ :=
  (d : ℝ)⁻¹ * ∑ a, ∑ b, ∏ i, P i b a

/-- PDF p.6, protocol and Eq.38, extended to n uses. Share a uniform symbol
r. On input k encode a = r-k in every register. Accept only a common received
symbol b and decode r-b = k+a-b. This finite sum is the actual successful
branch of that shared-randomness algorithm, before conditioning. -/
def agreementBranch {d n : ℕ} [NeZero d] (P : Fin n → Transition d) : Transition d :=
  fun j k => (d : ℝ)⁻¹ * ∑ a, ∑ b,
    if j = k + a - b then ∏ i, P i b a else 0

/-- PDF p.6, Eq.38: condition the constructed branch on its success event. -/
def agreementOutput {d n : ℕ} [NeZero d] (P : Fin n → Transition d) : Transition d :=
  fun j k => agreementBranch P j k / agreementSuccess P

/-- PDF p.7, Eq.44: average conjugation by all label permutations.
Replacing permutations by their inverses gives the same finite average. -/
def classicalTwirl {d : ℕ} [NeZero d] (P : Transition d) : Transition d :=
  fun b a => ((Nat.factorial d : ℝ)⁻¹) *
    ∑ sigma : Equiv.Perm (ZMod d), P (sigma b) (sigma a)

/-- PDF p.7, Eq.45: d-ary symmetric channel, with fidelity parameter f. -/
def symmetricChannel (d : ℕ) (f : ℝ) : Transition d :=
  fun b a => if b = a then f else (1 - f) / ((d : ℝ) - 1)

/-- PDF p.7, below Eq.45: average correct-transmission probability. -/
def classicalAverage {d : ℕ} [NeZero d] (P : Transition d) : ℝ :=
  (d : ℝ)⁻¹ * ∑ a, P a a

/-- PDF p.7, Eq.46 (and quantum Eqs.25–26 with m=d²): the common
agreement denominator and the conditional correct-transmission fraction. -/
def symmetricSuccess {n : ℕ} (m : ℝ) (f : Fin n → ℝ) : ℝ :=
  (∏ i, f i) + (1 / (m - 1)) ^ (n - 1) * ∏ i, (1 - f i)

/-- Sanity: the symmetric classical channel keeps the fidelity parameter
on its diagonal; it is not a depolarizing noise-rate parameter. -/
example (f : ℝ) : symmetricChannel 2 f (0 : ZMod 2) 0 = f := by
  simp [symmetricChannel]

/-- Sanity: completely random binary inputs succeed with probability 1/2
for two channels; this pins the agreement normalization. -/
example : symmetricSuccess (n := 2) 2 (fun _ => (1 / 2 : ℝ)) = 1 / 2 := by
  norm_num [symmetricSuccess, Fin.prod_univ_two]

end QAlgorithms.Papers.Independent.Information100.P06


