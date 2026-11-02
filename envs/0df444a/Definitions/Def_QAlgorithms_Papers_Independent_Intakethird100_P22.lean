-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P22
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P22
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T07:58:25.597858+00:00
-- url     : https://prove2.me/theorems/6c588a87-dd8f-41a5-a725-b4d8eb8482b1
-- title:
--   Definitions for Limitations on device independent key secure against non signaling adversary via the squashed non-locality
-- statement:
--   The objects the formalized statements of *Limitations on device independent key secure against non signaling adversary via the squashed non-locality* (arXiv:1903.12154) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `finiteMax`: PDF pp.21,24: a maximum on a finite nonempty alphabet. Every use has a nonempty finite range, so the real supremum has neither empty nor unbounded input.
--   - `CDArray`: PDF p.23: classical-device arrays, with only Eve's input non-unary.
--   - `IsCD`: PDF pp.23–24: normalized conditional laws and a classical marginal independent of Eve's input. All alphabets in the statements are finite and nonempty.
--   - `CDObservation`: PDF pp.23–29: the causal normal form of a G-observation on a c-d state. After seeing the whole classical tuple c, a dice chooses z; after receiving e, a stochastic map produces an arbitrary finite observation. The input z can be retained in that observation. This is the source's c-d class, not all positive maps.
--   - `CDObservation.apply`: PDF p.23, (30): action of the causal observation, including the dice.
--   - `cdDistance`: PDF p.23, (30): half l1 distance after all source G-observations on c-d arrays. For normalized arrays the score set is nonempty (constant observation) and lies in [0,1]. Weighted pass arrays have the corresponding finite mass bound.
--   - `idealCDKey`: PDF p.30, (82): uniform correlated key times the ACTUAL transcript/Eve marginal.
--   - `intermediateKey`: PDF p.30, (85): copy Alice into Bob, preserving (Alice,transcript,Eve|Z).
--   - `aliceMarginal`: PDF p.31, (87): Alice and Eve's marginal, including all public messages.
--   - `withAbort`: PDF p.30, (81): abort and pass branches; the abort array is common to all states.
--   - `KeyOutput`: PDF pp.30–31: data available at protocol termination. At pass probability zero, the normalized pass law is an arbitrary representative; all errors multiply it by zero. No conditioning by a zero-probability event is performed.
--   - `correctnessError`: PDF p.31, (88): the weighted probability of unequal keys. Any reference input z gives the same number, by the classical marginal no-signaling constraint.
--   - `cdSecrecyError`: PDF p.30, (86): weighted secrecy distance for Alice and Eve with the transcript.
--   - `securityError`: PDF p.31, (89): weighted real/ideal NS security distance.
--   - `deviceCMI`: PDF p.20, (23): entropy identity for CMI; this includes the probability weights missing in the printed (22), and never divides by a zero marginal.
--   - `EveChannel`: PDF p.20, (24): a channel of arbitrary positive finite output cardinality.
--   - `EveChannel.apply`: PDF p.20, (24): actual stochastic output processing, not a free new law.
--   - `intrinsicInformation`: PDF p.20, (24): intrinsic information. For a probability law, constant channels make the score set nonempty and every CMI is between zero and log2 min(|A|,|B|).
--   - `ValidDevice`: PDF p.21, (26),(27): validity and both no-signaling equalities.
--   - `DeviceEnsemble`: PDF pp.21,45, (217): an ensemble reconstructs the same device at EVERY input.
--   - `IsVertex`: PDF p.21: purity means an extreme point of this fixed non-signaling polytope.
--   - `DeviceEnsemble.support`: PDF p.21, Definition 4: support of the positive-weight pure members, ignoring zero padding and label permutations.
--   - `DeviceEnsemble.IsMinimal`: PDF p.21, Definition 4: a pure-members ensemble is minimal when no ensemble on a proper subset of its positive support represents p.
--   - `DeviceEnsemble.massAt`: PDF p.21, (28): weight assigned to an actual vertex, invariant under labels.
--   - `CompleteExtension`: PDF p.21, Definition 5: exactly the minimal ensembles, modulo zero padding and repeated member labels. The conditioned device may depend on BOTH Eve input and output, as the source superscript (e,z) explicitly states. No ACCESS, GENERATION or optimization assertion is assumed.
--   - `CompleteExtension.measured`: PDF p.22, XI.B items 2–3 and p.44 (215): a general measurement retains its dice result together with the CE output. The source explicitly allows postprocessing conditioned on that result. Summing the retained result recovers (7); erasing it before the channel would remove allowed Eve strategies.
--   - `squashSecrecy`: PDF p.6, (6): maximum over honest settings, then infimum over all Eve dice. The infimum convention records the source's unproved attainment claim. Eve retains the dice result as required by XI.B item 3.
--   - `squashedNonlocality`: PDF p.7, Definition 3: squashed nonlocality from CE and classical intrinsic information. Neither a roof formula nor a key bound is used to define it.
--   - `squashedMI`: PDF pp.6–7: squashed MI, computed from the marginal of the measured CE.
--   - `squashedCMI`: PDF pp.6–7 and p.22: squashed classical CMI with general Eve measurements and the retained dice result. Thus mixing pure-member ensembles does not silently erase their preparation record.
--   - `UnaryExtension`: PDF pp.44–45, (216): an arbitrary unary-input extension is fully tripartite non-signaling. In particular, conditioning on Eve's output preserves the honest no-signaling equalities; an extension of only one measured law is insufficient.
--   - `extensionForm`: PDF p.44, (216): infimum over all positive finite Eve output alphabets.
--   - `ensembleForm`: PDF p.45, (218): the convex roof is taken at each fixed input BEFORE maximum.
--   - `ampAtInput`: PDF pp.3,45, (2),(3): AMP optimizes intrinsic information of whole-device ensembles, not just decompositions of the evaluated joint distribution.
--   - `aliceSupport`: PDF p.52: maximum support of Alice's no-signaling marginal. The reference Bob input can be any y, and is not an additional physical choice.
--   - `bobSupport`: PDF p.52: maximum support of Bob's no-signaling marginal.
--   - `singleDeviceEnsemble`: PDF p.45, (217): a one-member decomposition witnesses nonemptiness of the ensemble score sets on every valid device.
--   - `squashedLowerHull`: PDF pp.54–55, (317): lower convex hull of both entire bound functions. Each term is evaluated at an actual device in a finite decomposition of p, with its complete extension. Selecting the smaller bound at each term is exactly allowing either graph in the convex hull. Complete-extension labels are auxiliary representation data; both CE invariance and convexity remain theorem content. The one-member decomposition gives nonemptiness and nonnegative information scores give boundedness below, with no numerical interpolation.
--   - `nonlocalityFraction`: PDF pp.52–53, (296),(297): the printed single-nonlocal-vertex fraction. This real infimum is used below ONLY in the binary HRW sector with an explicit feasible decomposition; no value on an empty decomposition set is asserted.
--   - `nonlocalityCost`: PDF p.52, Definition 16, (294): cost with the source's maximum SUPPORT sizes. Only the feasible binary HRW sector is used; the universal residual convention of Proposition 9 is explicitly deferred.
--   - `GeneralLocalMap`: PDF p.48, (241),(242): the source's two INDEPENDENT shared randomizers, with local input preprocessing and local output kernels depending on the original local input and output. This class is exactly the displayed map, not arbitrary communicating operations. Public local randomizers are not optimized as Eve data.
--   - `GeneralLocalMap.apply`: PDF p.48, (243)–(245): computed device transformation by the named source map.
--   - `hrwBox`: PDF p.56, (319): exact HRW binary device. The second source parameter is called eta, distinguishing it from the CHSH error epsilon.
--   - `chshLoss`: PDF p.56, (320): independent uniform CHSH inputs; true is the bit 1.
--   - `deterministicBox`: PDF p.56, (321): all sixteen deterministic binary local devices.
--   - `prVariant`: PDF p.56, (322): the eight binary PR-type devices, true denoting one.
-- source:
--   Limitations on device independent key secure against non signaling adversary via the squashed non-locality, arXiv:1903.12154v7, https://arxiv.org/abs/1903.12154v7

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P47
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P27
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P37
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P25

/-!
Statements from arXiv:1903.12154v7. All page references are PDF pages.
The imported paper modules are pinned accepted library modules. Their scalar
probability, correlation, locality and entropy definitions are reused exactly;
their operator-valued extension objects are not used. New objects are paper-local.
Infima replace the source's unjustified attained minima, as recorded in STATUS.md.
Eve retains the input-dice result as permitted on PDF p.22, item 3.
The general-measurement marginal (7) is recovered by summing that record.
Compilation is pending the separate batch handoff.
-/

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Advance50.P47
  (Box IsCorrelation IsNoSignaling HasLocalModel correlationMixture prBox)
open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)
open QAlgorithms.Papers.Independent.Information100.P27 (shannon)
open QAlgorithms.Papers.Independent.Gap48.P25 (classicalMI)

/-- PDF pp.21,24: a maximum on a finite nonempty alphabet. Every use has a
nonempty finite range, so the real supremum has neither empty nor unbounded input. -/
def finiteMax {I : Type} [Fintype I] [Nonempty I] (f : I → ℝ) : ℝ :=
  sSup (Set.range f)

/-- PDF p.23: classical-device arrays, with only Eve's input non-unary. -/
abbrev CDArray (C E Z : Type) := Z → C → E → ℝ

/-- PDF pp.23–24: normalized conditional laws and a classical marginal independent
of Eve's input. All alphabets in the statements are finite and nonempty. -/
def IsCD {C E Z : Type} [Fintype C] [Fintype E] (p : CDArray C E Z) : Prop :=
  (∀ z c e, 0 ≤ p z c e) ∧
  (∀ z, ∑ c, ∑ e, p z c e = 1) ∧
  (∀ z zOther c, ∑ e, p z c e = ∑ e, p zOther c e)

/-- PDF pp.23–29: the causal normal form of a G-observation on a c-d state.
After seeing the whole classical tuple c, a dice chooses z; after receiving e,
a stochastic map produces an arbitrary finite observation. The input z can be
retained in that observation. This is the source's c-d class, not all positive maps. -/
structure CDObservation (C E Z : Type) [Fintype Z] where
  size : ℕ
  positive : 0 < size
  input : C → Z → ℝ
  input_law : ∀ c, IsLaw (input c)
  output : C → Z → E → Fin size → ℝ
  output_law : ∀ c z e, IsLaw (output c z e)

/-- PDF p.23, (30): action of the causal observation, including the dice. -/
def CDObservation.apply {C E Z : Type} [Fintype C] [Fintype E] [Fintype Z]
    (g : CDObservation C E Z) (p : CDArray C E Z) (j : Fin g.size) : ℝ :=
  ∑ c, ∑ z, ∑ e, g.input c z * p z c e * g.output c z e j

/-- PDF p.23, (30): half l1 distance after all source G-observations on c-d arrays.
For normalized arrays the score set is nonempty (constant observation) and lies
in [0,1]. Weighted pass arrays have the corresponding finite mass bound. -/
def cdDistance {C E Z : Type} [Fintype C] [Fintype E] [Fintype Z]
    (p q : CDArray C E Z) : ℝ :=
  sSup {v | ∃ g : CDObservation C E Z,
    v = (1 / 2 : ℝ) * ∑ j, |g.apply p j - g.apply q j|}

/-- PDF p.30, (82): uniform correlated key times the ACTUAL transcript/Eve marginal. -/
def idealCDKey {K T E Z : Type} [Fintype K]
    (p : CDArray (K × K × T) E Z) : CDArray (K × K × T) E Z :=
  fun z c e => if c.1 = c.2.1 then
    (∑ a, ∑ b, p z (a,b,c.2.2) e) / (Fintype.card K : ℝ) else 0

/-- PDF p.30, (85): copy Alice into Bob, preserving (Alice,transcript,Eve|Z). -/
def intermediateKey {K T E Z : Type} [Fintype K]
    (p : CDArray (K × K × T) E Z) : CDArray (K × K × T) E Z :=
  fun z c e => if c.1 = c.2.1 then ∑ b, p z (c.1,b,c.2.2) e else 0

/-- PDF p.31, (87): Alice and Eve's marginal, including all public messages. -/
def aliceMarginal {K T E Z : Type} [Fintype K]
    (p : CDArray (K × K × T) E Z) : CDArray (K × T) E Z :=
  fun z c e => ∑ b, p z (c.1,b,c.2) e

/-- PDF p.30, (81): abort and pass branches; the abort array is common to all states. -/
def withAbort {C E Z : Type} (r : ℝ) (abort pass : CDArray C E Z) : CDArray C E Z :=
  fun z c e => r * abort z c e + (1-r) * pass z c e

/-- PDF pp.30–31: data available at protocol termination. At pass probability zero,
the normalized pass law is an arbitrary representative; all errors multiply it
by zero. No conditioning by a zero-probability event is performed. -/
structure KeyOutput (K T E Z : Type) [Fintype K] [Fintype T] [Fintype E] where
  abortProbability : ℝ
  abort_nonneg : 0 ≤ abortProbability
  abort_le_one : abortProbability ≤ 1
  pass : CDArray (K × K × T) E Z
  pass_valid : IsCD pass
  abort : CDArray (K × K × T) E Z
  abort_valid : IsCD abort

/-- PDF p.31, (88): the weighted probability of unequal keys. Any reference input
z gives the same number, by the classical marginal no-signaling constraint. -/
def correctnessError {K T E Z : Type} [Fintype K] [Fintype T] [Fintype E]
    (r : KeyOutput K T E Z) (z : Z) : ℝ :=
  (1-r.abortProbability) * ∑ a, ∑ b, ∑ t, ∑ e,
    if a = b then 0 else r.pass z (a,b,t) e

/-- PDF p.30, (86): weighted secrecy distance for Alice and Eve with the transcript. -/
def cdSecrecyError {K T E Z : Type} [Fintype K] [Fintype T] [Fintype E] [Fintype Z]
    (r : KeyOutput K T E Z) : ℝ :=
  (1-r.abortProbability) * cdDistance (aliceMarginal r.pass) (aliceMarginal (idealCDKey r.pass))

/-- PDF p.31, (89): weighted real/ideal NS security distance. -/
def securityError {K T E Z : Type} [Fintype K] [Fintype T] [Fintype E] [Fintype Z]
    (r : KeyOutput K T E Z) : ℝ :=
  (1-r.abortProbability) * cdDistance r.pass (idealCDKey r.pass)

/-- PDF p.20, (23): entropy identity for CMI; this includes the probability
weights missing in the printed (22), and never divides by a zero marginal. -/
def deviceCMI {A B E : Type} [Fintype A] [Fintype B] [Fintype E]
    (p : A × B × E → ℝ) : ℝ :=
  shannon (fun ae : A × E => ∑ b, p (ae.1,b,ae.2)) +
  shannon (fun be : B × E => ∑ a, p (a,be.1,be.2)) -
  shannon (fun e => ∑ a, ∑ b, p (a,b,e)) - shannon p

/-- PDF p.20, (24): a channel of arbitrary positive finite output cardinality. -/
structure EveChannel (E : Type) where
  size : ℕ
  positive : 0 < size
  kernel : E → Fin size → ℝ
  law : ∀ e, IsLaw (kernel e)

/-- PDF p.20, (24): actual stochastic output processing, not a free new law. -/
def EveChannel.apply {A B E : Type} [Fintype E]
    (k : EveChannel E) (p : A × B × E → ℝ) : A × B × Fin k.size → ℝ :=
  fun c => ∑ e, p (c.1,c.2.1,e) * k.kernel e c.2.2

/-- PDF p.20, (24): intrinsic information. For a probability law, constant channels
make the score set nonempty and every CMI is between zero and log2 min(|A|,|B|). -/
def intrinsicInformation {A B E : Type} [Fintype A] [Fintype B] [Fintype E]
    (p : A × B × E → ℝ) : ℝ :=
  sInf {v | ∃ k : EveChannel E, v = deviceCMI (k.apply p)}

section Devices

variable {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]

/-- PDF p.21, (26),(27): validity and both no-signaling equalities. -/
def ValidDevice (p : Box X Y A B) : Prop := IsCorrelation p ∧ IsNoSignaling p

/-- PDF pp.21,45, (217): an ensemble reconstructs the same device at EVERY input. -/
structure DeviceEnsemble (p : Box X Y A B) (n : ℕ) where
  weight : Fin n → ℝ
  law : IsLaw weight
  member : Fin n → Box X Y A B
  valid : ∀ i, ValidDevice (member i)
  reconstruct : ∀ x y a b, ∑ i, weight i * member i x y a b = p x y a b

/-- PDF p.21: purity means an extreme point of this fixed non-signaling polytope. -/
def IsVertex (p : Box X Y A B) : Prop :=
  ValidDevice p ∧ ∀ q r : Box X Y A B, ValidDevice q → ValidDevice r →
    ∀ t : ℝ, 0 < t → t < 1 → p = correlationMixture q r t → q = p ∧ r = p

/-- PDF p.21, Definition 4: support of the positive-weight pure members, ignoring
zero padding and label permutations. -/
def DeviceEnsemble.support {p : Box X Y A B} {n : ℕ} (d : DeviceEnsemble p n) : Set (Box X Y A B) :=
  {v | ∃ i, 0 < d.weight i ∧ d.member i = v}

/-- PDF p.21, Definition 4: a pure-members ensemble is minimal when no ensemble
on a proper subset of its positive support represents p. -/
def DeviceEnsemble.IsMinimal {p : Box X Y A B} {n : ℕ} (d : DeviceEnsemble p n) : Prop :=
  (∀ i, 0 < d.weight i → IsVertex (d.member i)) ∧
  ∀ m : ℕ, ∀ dOther : DeviceEnsemble p m, ¬ dOther.support ⊂ d.support

/-- PDF p.21, (28): weight assigned to an actual vertex, invariant under labels. -/
def DeviceEnsemble.massAt {p : Box X Y A B} {n : ℕ} (d : DeviceEnsemble p n)
    (v : Box X Y A B) : ℝ := ∑ i, if d.member i = v then d.weight i else 0

/-- PDF p.21, Definition 5: exactly the minimal ensembles, modulo zero
padding and repeated member labels. The conditioned device may depend on BOTH
Eve input and output, as the source superscript (e,z) explicitly states.
No ACCESS, GENERATION or optimization assertion is assumed. -/
structure CompleteExtension (p : Box X Y A B) where
  valid : ValidDevice p
  inputs : ℕ
  inputs_positive : 0 < inputs
  outputs : ℕ
  outputs_positive : 0 < outputs
  ensemble : Fin inputs → DeviceEnsemble p outputs
  minimal : ∀ z, (ensemble z).IsMinimal
  complete : ∀ n : ℕ, ∀ d : DeviceEnsemble p n, d.IsMinimal →
    ∃! z : Fin inputs, ∀ v, (ensemble z).massAt v = d.massAt v

/-- PDF p.22, XI.B items 2–3 and p.44 (215): a general measurement
retains its dice result together with the CE output. The source explicitly allows
postprocessing conditioned on that result. Summing the retained result recovers
(7); erasing it before the channel would remove allowed Eve strategies. -/
def CompleteExtension.measured {p : Box X Y A B} (c : CompleteExtension p)
    (dice : Fin c.inputs → ℝ) (x : X) (y : Y) :
    A × B × (Fin c.inputs × Fin c.outputs) → ℝ :=
  fun abe => dice abe.2.2.1 * (c.ensemble abe.2.2.1).weight abe.2.2.2 *
    (c.ensemble abe.2.2.1).member abe.2.2.2 x y abe.1 abe.2.1

/-- PDF p.6, (6): maximum over honest settings, then infimum over all Eve dice.
The infimum convention records the source's unproved attainment claim.
Eve retains the dice result as required by XI.B item 3. -/
def squashSecrecy {p : Box X Y A B} (c : CompleteExtension p)
    (m : (A × B × (Fin c.inputs × Fin c.outputs) → ℝ) → ℝ) : ℝ :=
  finiteMax (fun xy : X × Y => sInf {v | ∃ dice : Fin c.inputs → ℝ,
    IsLaw dice ∧ v = m (c.measured dice xy.1 xy.2)})

/-- PDF p.7, Definition 3: squashed nonlocality from CE and classical intrinsic
information. Neither a roof formula nor a key bound is used to define it. -/
def squashedNonlocality {p : Box X Y A B} (c : CompleteExtension p) : ℝ :=
  squashSecrecy c intrinsicInformation

/-- PDF pp.6–7: squashed MI, computed from the marginal of the measured CE. -/
def squashedMI {p : Box X Y A B} (c : CompleteExtension p) : ℝ :=
  squashSecrecy c (fun d => classicalMI (fun ab => ∑ e, d (ab.1,ab.2,e)))

/-- PDF pp.6–7 and p.22: squashed classical CMI with general Eve
measurements and the retained dice result. Thus mixing pure-member ensembles
does not silently erase their preparation record. -/
def squashedCMI {p : Box X Y A B} (c : CompleteExtension p) : ℝ :=
  squashSecrecy c deviceCMI

/-- PDF pp.44–45, (216): an arbitrary unary-input extension is fully tripartite
non-signaling. In particular, conditioning on Eve's output preserves the honest
no-signaling equalities; an extension of only one measured law is insufficient. -/
structure UnaryExtension (p : Box X Y A B) (n : ℕ) where
  probability : X → Y → A → B → Fin n → ℝ
  nonneg : ∀ x y a b e, 0 ≤ probability x y a b e
  marginal : ∀ x y a b, ∑ e, probability x y a b e = p x y a b
  eveNS : ∀ x y xOther yOther e,
    ∑ a, ∑ b, probability x y a b e = ∑ a, ∑ b, probability xOther yOther a b e
  aliceNS : ∀ x xOther y b e, ∑ a, probability x y a b e = ∑ a, probability xOther y a b e
  bobNS : ∀ y yOther x a e, ∑ b, probability x y a b e = ∑ b, probability x yOther a b e

/-- PDF p.44, (216): infimum over all positive finite Eve output alphabets. -/
def extensionForm (p : Box X Y A B) : ℝ :=
  finiteMax (fun xy : X × Y => sInf {v | ∃ n : ℕ, 0 < n ∧
    ∃ d : UnaryExtension p n,
      v = deviceCMI (fun abe => d.probability xy.1 xy.2 abe.1 abe.2.1 abe.2.2)})

/-- PDF p.45, (218): the convex roof is taken at each fixed input BEFORE maximum. -/
def ensembleForm (p : Box X Y A B) : ℝ :=
  finiteMax (fun xy : X × Y => sInf {v | ∃ n : ℕ, 0 < n ∧ ∃ d : DeviceEnsemble p n,
    v = ∑ i, d.weight i * classicalMI (fun ab => d.member i xy.1 xy.2 ab.1 ab.2)})

/-- PDF pp.3,45, (2),(3): AMP optimizes intrinsic information of whole-device
ensembles, not just decompositions of the evaluated joint distribution. -/
def ampAtInput (p : Box X Y A B) (x : X) (y : Y) : ℝ :=
  sInf {v | ∃ n : ℕ, 0 < n ∧ ∃ d : DeviceEnsemble p n,
    v = intrinsicInformation (fun abe => d.weight abe.2.2 *
      d.member abe.2.2 x y abe.1 abe.2.1)}

/-- PDF p.52: maximum support of Alice's no-signaling marginal. The reference
Bob input can be any y, and is not an additional physical choice. -/
def aliceSupport (p : Box X Y A B) (y : Y) : ℕ :=
  Finset.univ.sup (fun x : X => (Finset.univ.filter (fun a => 0 < ∑ b, p x y a b)).card)

/-- PDF p.52: maximum support of Bob's no-signaling marginal. -/
def bobSupport (p : Box X Y A B) (x : X) : ℕ :=
  Finset.univ.sup (fun y : Y => (Finset.univ.filter (fun b => 0 < ∑ a, p x y a b)).card)

/-- PDF p.45, (217): a one-member decomposition witnesses nonemptiness of the
ensemble score sets on every valid device. -/
def singleDeviceEnsemble (p : Box X Y A B) (hp : ValidDevice p) : DeviceEnsemble p 1 where
  weight := fun _ => 1
  law := by simp [IsLaw]
  member := fun _ => p
  valid := fun _ => hp
  reconstruct := by intro x y a b; simp

/-- PDF pp.54–55, (317): lower convex hull of both entire bound functions.
Each term is evaluated at an actual device in a finite decomposition of p,
with its complete extension. Selecting the smaller bound at each term is
exactly allowing either graph in the convex hull. Complete-extension labels are
auxiliary representation data; both CE invariance and convexity remain theorem
content. The one-member decomposition gives nonemptiness and nonnegative
information scores give boundedness below, with no numerical interpolation. -/
def squashedLowerHull (p : Box X Y A B) : ℝ :=
  sInf {v | ∃ n : ℕ, 0 < n ∧ ∃ d : DeviceEnsemble p n,
    ∃ cs : (i : Fin n) → CompleteExtension (d.member i),
      v = ∑ i, d.weight i * min (squashedMI (cs i)) (squashedCMI (cs i))}

/-- PDF pp.52–53, (296),(297): the printed single-nonlocal-vertex fraction.
This real infimum is used below ONLY in the binary HRW sector with an explicit
feasible decomposition; no value on an empty decomposition set is asserted. -/
def nonlocalityFraction (p : Box X Y A B) : ℝ :=
  sInf {t | 0 ≤ t ∧ t ≤ 1 ∧ ∃ v l : Box X Y A B,
    IsVertex v ∧ ¬ HasLocalModel v ∧ HasLocalModel l ∧ p = correlationMixture v l t}

/-- PDF p.52, Definition 16, (294): cost with the source's maximum SUPPORT sizes.
Only the feasible binary HRW sector is used; the universal residual convention
of Proposition 9 is explicitly deferred. -/
def nonlocalityCost (p : Box X Y A B) (x : X) (y : Y) : ℝ :=
  nonlocalityFraction p * Real.logb 2 (min (aliceSupport p y) (bobSupport p x) : ℕ)

end Devices

/-- PDF p.48, (241),(242): the source's two INDEPENDENT shared randomizers,
with local input preprocessing and local output kernels depending on the original
local input and output. This class is exactly the displayed map, not arbitrary
communicating operations. Public local randomizers are not optimized as Eve data. -/
structure GeneralLocalMap (X Y A B Xo Yo Ao Bo L M : Type)
    [Fintype X] [Fintype Y] [Fintype Ao] [Fintype Bo] [Fintype L] [Fintype M] where
  mu : L → ℝ
  nu : M → ℝ
  mu_law : IsLaw mu
  nu_law : IsLaw nu
  aliceInput : L → Xo → X → ℝ
  bobInput : L → Yo → Y → ℝ
  aliceInput_law : ∀ l x, IsLaw (aliceInput l x)
  bobInput_law : ∀ l y, IsLaw (bobInput l y)
  aliceOutput : M → A → X → Ao → ℝ
  bobOutput : M → B → Y → Bo → ℝ
  aliceOutput_law : ∀ m a x, IsLaw (aliceOutput m a x)
  bobOutput_law : ∀ m b y, IsLaw (bobOutput m b y)

/-- PDF p.48, (243)–(245): computed device transformation by the named source map. -/
def GeneralLocalMap.apply {X Y A B Xo Yo Ao Bo L M : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype Ao] [Fintype Bo] [Fintype L] [Fintype M]
    (g : GeneralLocalMap X Y A B Xo Yo Ao Bo L M) (p : Box X Y A B) : Box Xo Yo Ao Bo :=
  fun xo yo ao bo => ∑ l, ∑ m, ∑ x, ∑ y, ∑ a, ∑ b,
    g.mu l * g.nu m * g.aliceInput l xo x * g.bobInput l yo y *
    p x y a b * g.aliceOutput m a x ao * g.bobOutput m b y bo

/-- PDF p.56, (319): exact HRW binary device. The second source parameter is
called eta, distinguishing it from the CHSH error epsilon. -/
def hrwBox (delta eta : ℝ) : Box Bool Bool Bool Bool :=
  fun x y a b => if x = false ∧ y = false then
    (if a = b then (1-delta)/2 else delta/2)
  else if Bool.xor a b = (x && y) then 3/8 - eta/2 else 1/8 + eta/2

/-- PDF p.56, (320): independent uniform CHSH inputs; true is the bit 1. -/
def chshLoss (p : Box Bool Bool Bool Bool) : ℝ :=
  (1/4 : ℝ) * ∑ x, ∑ y, ∑ a, ∑ b,
    if Bool.xor a b = (x && y) then 0 else p x y a b

/-- PDF p.56, (321): all sixteen deterministic binary local devices. -/
def deterministicBox (alpha beta gamma sigma : Bool) : Box Bool Bool Bool Bool :=
  fun x y a b => if a = Bool.xor (alpha && x) beta ∧
    b = Bool.xor (gamma && y) sigma then 1 else 0

/-- PDF p.56, (322): the eight binary PR-type devices, true denoting one. -/
def prVariant (r s t : Bool) : Box Bool Bool Bool Bool :=
  fun x y a b => if Bool.xor a b =
    Bool.xor (Bool.xor (Bool.xor (x && y) (r && x)) (s && y)) t then 1/2 else 0

section Sanity

/-! Sanity examples pin local definitions; none is a source theorem proof. -/

example : IsCD (fun (_ _ _ : Unit) => (1 : ℝ)) := by simp [IsCD]

example {C E Z : Type} (a p : CDArray C E Z) : withAbort 1 a p = a := by
  funext z c e
  simp [withAbort]

example {C E Z : Type} (a p : CDArray C E Z) : withAbort 0 a p = p := by
  funext z c e
  simp [withAbort]

example : idealCDKey (fun (_ : Unit) (_ : Unit × Unit × Unit) (_ : Unit) => (1 : ℝ))
    () ((),(),()) () = 1 := by simp [idealCDKey]

example : intermediateKey (fun (_ : Unit) (_ : Unit × Unit × Unit) (_ : Unit) => (1 : ℝ))
    () ((),(),()) () = 1 := by simp [intermediateKey]

example : shannon (fun _ : Unit => (1 : ℝ)) = 0 := by
  simp [shannon]

example : deviceCMI (fun _ : Unit × Unit × Unit => (1 : ℝ)) = 0 := by
  simp [deviceCMI, shannon]

example : hrwBox (1/5) (-(1/20)) false false false false = 2/5 := by
  norm_num [hrwBox]

example : hrwBox (1/5) (-(1/20)) false true false true = 1/10 := by
  norm_num [hrwBox]

example : deterministicBox false false false false false false false false = 1 := by
  norm_num [deterministicBox]

example : prVariant false false false false false false false = (1/2 : ℝ) := by
  norm_num [prVariant]

end Sanity

end QAlgorithms.Papers.Independent.Intakethird100.P22


