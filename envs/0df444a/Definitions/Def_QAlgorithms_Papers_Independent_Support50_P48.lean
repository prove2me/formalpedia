-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support50_P48
-- name    : QAlgorithms_Papers_Independent_Support50_P48
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-24T00:00:53.26901+00:00
-- url     : https://prove2.me/theorems/8cfeff1f-cef4-4f55-ae81-8ebe36f4a180
-- title:
--   Definitions for Unconstrained distillation capacities of a pure-loss bosonic broadcast channel
-- statement:
--   The objects the formalized statements of *Unconstrained distillation capacities of a pure-loss bosonic broadcast channel* (arXiv:1601.05563) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `portWeight`: PDF pp.2,6: `none` is the environment; `some i` is receiver i. The nonnegative subtraction agrees with real subtraction by total_le_one.
--   - `vacuumAmplitude`: PDF pp.2,6: the vacuum splitting isometry on the entire number basis. This is the normalized multinomial expansion of the input creation operator; there is no global photon cutoff. All output signal phases are positive.
--   - `tmsvWeight`: PDF p.3, (7): geometric Schmidt probabilities, with finite mean N.
--   - `ResourceMode`: Full mode labels: `none` is Alice, `some none` is the environment, and `some (some i)` is receiver i; PDF pp.3,6, (11),(29).
--   - `resourceAmplitude`: PDF pp.3,6, (7),(11),(29): the actual purified TMSV channel-output amplitude, obtained by applying the vacuum splitting isometry to the input half.
--   - `purifiedResource`: PDF pp.3,6, (11),(29): rank-one purified resource coefficients, before tracing the environment. Normalization is a conclusion of the entropy theorem.
--   - `subsystem`: PDF pp.3,6: actual partial trace over the complementary modes. On all resource states used here the diagonal trace series is convergent.
--   - `receiverModes`: The selected receiver modes in the purified resource, PDF p.6.
--   - `aliceWith`: Alice together with selected receivers; PDF pp.3,6.
--   - `environmentWith`: Environment together with selected receivers; PDF pp.3,6.
--   - `resourceEntropyBits`: PDF pp.3,6: spectral von Neumann entropy of an actual reduced resource, converted from the accepted extended entropy in nats to bits.
--   - `reverseCutYield`: PDF pp.3,6: negative conditional entropy, computed from actual marginals. The entropy theorem supplies finiteness before either toReal is interpreted.
--   - `extendedCutBound`: PDF pp.2,6, (4)-(6),(27): extended endpoint interpretation of the cut bound, inferred from the finite-energy entropy limit. A zero selected signal has bound zero even when the environmental weight is zero.
--   - `cutOccupation`: PDF pp.3,6: reconstruct the full occupation at the T : A complement(T) cut, including the environment that will be traced out.
--   - `resourceCut`: PDF pp.4,6: the actual resource after tracing E, grouped across the selected receiver cut. The right factor includes Alice and all other receivers.
--   - `relativeEntanglementBits`: PDF p.3, (14): infimum of actual extended relative entropy over all normal separable states, using trace-norm closed separability; measured in bits. Arbitrary shields are not bounded and the infimum is extended, not real.
--   - `residualIntensity`: PDF p.6, (30): remaining input intensity before zero-based stage j. The ordering permutes all m+1 ports, including the environment.
--   - `emittedPhotons`: Number of photons already emitted before stage j, PDF p.6, Fig.3.
--   - `sequentialAmplitude`: PDF p.6, Fig.3,(30): the full vacuum network amplitude, with m actual splitters. Each factor is the normalized binomial vacuum splitting amplitude; the final remaining port is fixed by total photon conservation.
--   - `referencedVacuumOutput`: PDF pp.2,6: the full referenced output of a photon-conserving vacuum isometry. Input number indices are fixed by total output photon numbers, so no formal infinite matrix product is used.
-- source:
--   Unconstrained distillation capacities of a pure-loss bosonic broadcast channel, arXiv:1601.05563v3, https://arxiv.org/abs/1601.05563v3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P30
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07

/-!
# Pure-loss bosonic broadcast channels (arXiv:1601.05563v3)

The unrestricted operational capacity and merging/simulation interfaces are
explicitly deferred in HARD.md. The three statements here concern actual
number-basis resource states, their entropies/REE, and vacuum network equality.
No capacity is defined to equal a scalar bound. Compilation is pending.

All signal amplitudes use a positive output phase convention. Fixed local phase
rotations recover the minus signs of (1)-(3); these do not change any entropy or
bipartite REE. Occupations run over all natural numbers, without truncation.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P48

open Filter
open scoped BigOperators ENNReal NNReal Topology
open QAlgorithms.Papers.Independent.Dependency50.P30
  (PureLossBroadcastParameters thermalEntropyBits)
open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsSeparable)
open QAlgorithms.Papers.Independent.Frontier18.P07
  (extendedEntropyNats extendedRelativeEntropyNats)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.2,6: `none` is the environment; `some i` is receiver i.
The nonnegative subtraction agrees with real subtraction by total_le_one. -/
def portWeight {m : ℕ} (p : PureLossBroadcastParameters m) : Option (Fin m) → ℝ≥0
  | none => 1 - ∑ i, p.transmissivity i
  | some i => p.transmissivity i

/-- PDF pp.2,6: the vacuum splitting isometry on the entire number basis.
This is the normalized multinomial expansion of the input creation operator;
there is no global photon cutoff. All output signal phases are positive. -/
def vacuumAmplitude {J : Type} [Fintype J] (eta : J → ℝ≥0)
    (out : J → ℕ) (n : ℕ) : ℝ :=
  if (∑ i, out i) = n then
    Real.sqrt ((Nat.factorial n : ℝ) / ∏ i, (Nat.factorial (out i) : ℝ)) *
      ∏ i, Real.sqrt (eta i : ℝ) ^ out i
  else 0

/-- PDF p.3, (7): geometric Schmidt probabilities, with finite mean N. -/
def tmsvWeight (N : ℝ≥0) (n : ℕ) : ℝ :=
  (N : ℝ) ^ n / ((N : ℝ) + 1) ^ (n + 1)

/-- Full mode labels: `none` is Alice, `some none` is the environment,
and `some (some i)` is receiver i; PDF pp.3,6, (11),(29). -/
abbrev ResourceMode (m : ℕ) := Option (Option (Fin m))

/-- PDF pp.3,6, (7),(11),(29): the actual purified TMSV channel-output
amplitude, obtained by applying the vacuum splitting isometry to the input half. -/
def resourceAmplitude {m : ℕ} (p : PureLossBroadcastParameters m) (N : ℝ≥0)
    (out : ResourceMode m → ℕ) : ℝ :=
  Real.sqrt (tmsvWeight N (out none)) *
    vacuumAmplitude (portWeight p) (fun j => out (some j)) (out none)

/-- PDF pp.3,6, (11),(29): rank-one purified resource coefficients, before
tracing the environment. Normalization is a conclusion of the entropy theorem. -/
def purifiedResource {m : ℕ} (p : PureLossBroadcastParameters m) (N : ℝ≥0) :
    Matrix (ResourceMode m → ℕ) (ResourceMode m → ℕ) ℂ :=
  fun a b => (resourceAmplitude p N a : ℂ) * (resourceAmplitude p N b : ℂ)

/-- PDF pp.3,6: actual partial trace over the complementary modes. On all
resource states used here the diagonal trace series is convergent. -/
def subsystem {J : Type} (S : Finset J) (X : Matrix (J → ℕ) (J → ℕ) ℂ) :
    Matrix (S → ℕ) (S → ℕ) ℂ :=
  fun a b => ∑' e : {i : J // i ∉ S} → ℕ,
    X (fun i => if h : i ∈ S then a ⟨i, h⟩ else e ⟨i, h⟩)
      (fun i => if h : i ∈ S then b ⟨i, h⟩ else e ⟨i, h⟩)

/-- The selected receiver modes in the purified resource, PDF p.6. -/
def receiverModes {m : ℕ} (T : Finset (Fin m)) : Finset (ResourceMode m) :=
  T.image (fun i => some (some i))

/-- Alice together with selected receivers; PDF pp.3,6. -/
def aliceWith {m : ℕ} (T : Finset (Fin m)) : Finset (ResourceMode m) :=
  insert none (receiverModes T)

/-- Environment together with selected receivers; PDF pp.3,6. -/
def environmentWith {m : ℕ} (T : Finset (Fin m)) : Finset (ResourceMode m) :=
  insert (some none) (receiverModes T)

/-- PDF pp.3,6: spectral von Neumann entropy of an actual reduced resource,
converted from the accepted extended entropy in nats to bits. -/
def resourceEntropyBits {m : ℕ} (p : PureLossBroadcastParameters m) (N : ℝ≥0)
    (S : Finset (ResourceMode m)) : ℝ≥0∞ :=
  extendedEntropyNats (subsystem S (purifiedResource p N)) /
    ENNReal.ofReal (Real.log 2)

/-- PDF pp.3,6: negative conditional entropy, computed from actual marginals.
The entropy theorem supplies finiteness before either toReal is interpreted. -/
def reverseCutYield {m : ℕ} (p : PureLossBroadcastParameters m) (N : ℝ≥0)
    (T : Finset (Fin m)) : ℝ :=
  (resourceEntropyBits p N (aliceWith (Finset.univ \ T))).toReal -
    (resourceEntropyBits p N (aliceWith Finset.univ)).toReal

/-- PDF pp.2,6, (4)-(6),(27): extended endpoint interpretation of the cut
bound, inferred from the finite-energy entropy limit. A zero selected signal
has bound zero even when the environmental weight is zero. -/
def extendedCutBound {m : ℕ} (p : PureLossBroadcastParameters m)
    (T : Finset (Fin m)) : ℝ≥0∞ :=
  let selected : ℝ≥0 := ∑ i ∈ T, p.transmissivity i
  let loss := portWeight p none
  if selected = 0 then 0 else if loss = 0 then ⊤ else
    ENNReal.ofReal (Real.logb 2 (((loss : ℝ) + (selected : ℝ)) / (loss : ℝ)))

/-- PDF pp.3,6: reconstruct the full occupation at the T : A complement(T)
cut, including the environment that will be traced out. -/
def cutOccupation {m : ℕ} (T : Finset (Fin m)) (a : T → ℕ)
    (b : ℕ × ({i : Fin m // i ∉ T} → ℕ)) (e : ℕ) : ResourceMode m → ℕ
  | none => b.1
  | some none => e
  | some (some i) => if h : i ∈ T then a ⟨i, h⟩ else b.2 ⟨i, h⟩

/-- PDF pp.4,6: the actual resource after tracing E, grouped across the
selected receiver cut. The right factor includes Alice and all other receivers. -/
def resourceCut {m : ℕ} (p : PureLossBroadcastParameters m) (N : ℝ≥0)
    (T : Finset (Fin m)) :
    Matrix ((T → ℕ) × (ℕ × ({i : Fin m // i ∉ T} → ℕ)))
      ((T → ℕ) × (ℕ × ({i : Fin m // i ∉ T} → ℕ))) ℂ :=
  fun a b => ∑' e : ℕ, purifiedResource p N
    (cutOccupation T a.1 a.2 e) (cutOccupation T b.1 b.2 e)

/-- PDF p.3, (14): infimum of actual extended relative entropy over all
normal separable states, using trace-norm closed separability; measured in bits.
Arbitrary shields are not bounded and the infimum is extended, not real. -/
def relativeEntanglementBits {I J : Type} (X : Matrix (I × J) (I × J) ℂ) : ℝ≥0∞ :=
  (⨅ sigma : {rho : State (I × J) // IsSeparable rho.coefficients},
    extendedRelativeEntropyNats X sigma.val.coefficients) / ENNReal.ofReal (Real.log 2)

/-- PDF p.6, (30): remaining input intensity before zero-based stage j.
The ordering permutes all m+1 ports, including the environment. -/
def residualIntensity {m : ℕ} (eta : Fin (m + 1) → ℝ≥0)
    (order : Equiv.Perm (Fin (m + 1))) (j : ℕ) : ℝ :=
  1 - ∑ k ∈ Finset.univ.filter (fun k : Fin (m + 1) => k.val < j), (eta (order k) : ℝ)

/-- Number of photons already emitted before stage j, PDF p.6, Fig.3. -/
def emittedPhotons {m : ℕ} (order : Equiv.Perm (Fin (m + 1)))
    (out : Fin (m + 1) → ℕ) (j : ℕ) : ℕ :=
  ∑ k ∈ Finset.univ.filter (fun k : Fin (m + 1) => k.val < j), out (order k)

/-- PDF p.6, Fig.3,(30): the full vacuum network amplitude, with m actual
splitters. Each factor is the normalized binomial vacuum splitting amplitude;
the final remaining port is fixed by total photon conservation. -/
def sequentialAmplitude {m : ℕ} (t : Fin m → ℝ)
    (order : Equiv.Perm (Fin (m + 1))) (out : Fin (m + 1) → ℕ) (n : ℕ) : ℝ :=
  if (∑ i, out i) = n then
    ∏ j : Fin m,
      Real.sqrt (Nat.choose (n - emittedPhotons order out j.val)
        (out (order j.castSucc)) : ℝ) *
      Real.sqrt (1 - t j) ^ out (order j.castSucc) *
      Real.sqrt (t j) ^ (n - emittedPhotons order out j.val - out (order j.castSucc))
  else 0

/-- PDF pp.2,6: the full referenced output of a photon-conserving vacuum
isometry. Input number indices are fixed by total output photon numbers, so
no formal infinite matrix product is used. -/
def referencedVacuumOutput {J R : Type} [Fintype J]
    (amplitude : (J → ℕ) → ℕ → ℝ) (X : Matrix (R × ℕ) (R × ℕ) ℂ) :
    Matrix (R × (J → ℕ)) (R × (J → ℕ)) ℂ :=
  fun a b => (amplitude a.2 (∑ i, a.2 i) : ℂ) *
    X (a.1, ∑ i, a.2 i) (b.1, ∑ i, b.2 i) *
    (amplitude b.2 (∑ i, b.2 i) : ℂ)

/-- The vacuum sector has amplitude one, even if some port weights vanish. -/
example {J : Type} [Fintype J] (eta : J → ℝ≥0) :
    vacuumAmplitude eta (fun _ => 0) 0 = 1 := by
  simp [vacuumAmplitude]

/-- The TMSV zero-photon probability is 1/(N+1), including N=0. -/
example (N : ℝ≥0) : tmsvWeight N 0 = 1 / ((N : ℝ) + 1) := by
  simp [tmsvWeight]

/-- The empty cut never becomes infinite at the lossless endpoint. -/
example {m : ℕ} (p : PureLossBroadcastParameters m) : extendedCutBound p ∅ = 0 := by
  simp [extendedCutBound]

/-- The environment coordinate is retained explicitly in the cut reconstruction. -/
example {m : ℕ} (T : Finset (Fin m)) (a : T → ℕ)
    (b : ℕ × ({i : Fin m // i ∉ T} → ℕ)) (e : ℕ) :
    cutOccupation T a b e (some none) = e := by rfl

/-- With no photons, every physical splitter acts trivially on the vacuum. -/
example {m : ℕ} (t : Fin m → ℝ) (order : Equiv.Perm (Fin (m + 1))) :
    sequentialAmplitude t order (fun _ => 0) 0 = 1 := by
  simp [sequentialAmplitude, emittedPhotons]

end QAlgorithms.Papers.Independent.Support50.P48


