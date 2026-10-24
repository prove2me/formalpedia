-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support50_P26
-- name    : QAlgorithms_Papers_Independent_Support50_P26
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-23T21:03:15.787777+00:00
-- url     : https://prove2.me/theorems/44d07a42-cac1-4384-9a42-19cf4b8b6b16
-- title:
--   Definitions for Classical codes for quantum broadcast channels
-- statement:
--   The objects the formalized statements of *Classical codes for quantum broadcast channels* (arXiv:1111.3645) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `BroadcastChannel`: The fixed cq broadcast channel (1), PDF p.2. Nonempty finite alphabets and nonzero finite output dimensions are explicit; dimension one is allowed.
--   - `broadcastWordOutput`: Actual memoryless output (5), PDF pp.2–3, regrouped by receiver.
--   - `CqBroadcastCode`: Definition 1, PDF p.3: deterministic encoder and separate collective block POVMs. The two positive message sizes permit singleton messages at zero rate.
--   - `averageJointError`: Equations (6)–(7), PDF p.3: joint error averaged over independent uniform messages. Both POVMs are fixed before the unknown message pair.
--   - `AverageJointAchievable`: Definition 1, PDF p.3, including boundary rates via arbitrary positive backoff. The threshold precedes every sufficiently large block length.
--   - `superState`: State (12), PDF p.3. A joint law is exactly p_W p_(X|W), including null rows.
--   - `superWB1`: The actual WB1 marginal of (12), PDF pp.3–4.
--   - `superWB2`: The actual WB2 marginal of (12), PDF p.4.
--   - `superPrivate`: I(X;B1|W) of (12), PDF p.3: H(WB1)-H(W)-sum p(w,x)H(rho_x^B1). This form avoids conditional division at null W.
--   - `superTotal`: I(X;B1) of (12), PDF p.3, as entropy of the actual average minus average entropy.
--   - `SuperRegion`: All three inequalities (9)–(11), PDF p.3, at a fixed auxiliary law.
--   - `SuccessiveRegion`: Equations (61)–(63), Remark 2, PDF pp.7–8, for the same fixed law.
--   - `successiveCorner`: The shared successive-decoding corner, Remark 2, PDF p.7.
--   - `superUnion`: Full auxiliary union; `some k` bounds alphabet size, `none` leaves it unrestricted. Positive finite alphabets are represented up to relabeling by Fin(w+1).
--   - `superCap`: Auxiliary cardinality bound in Theorem 1, PDF p.3; positive dimensions prevent truncation.
--   - `separatingChannel`: A finite classical-output witness for Remark 2: input (w,v) gives |v,w><v,w|. The construction only instantiates the source's existential noncoincidence assertion.
--   - `separatingLaw`: W,V independent fair bits, X=(W,V), so the joint (W,X) weight is 1/4 on consistency.
--   - `MartonData`: Marton auxiliary data, (67), PDF p.8: arbitrary correlated law and deterministic map. The existence of a law enforces nonemptiness of both auxiliary alphabets.
--   - `martonState`: Actual state (67), PDF p.8, computed from the law, map, and fixed channel.
--   - `martonU1B1`: Actual U1B1 marginal of (67), PDF p.8.
--   - `martonU2B2`: Actual U2B2 marginal of (67), PDF p.8.
--   - `auxiliaryMI`: I(U1;U2) of the actual joint law, (66)–(67), PDF p.8.
--   - `MartonRegion`: All Marton inequalities (64)–(66), PDF p.8, including the correlation penalty.
--   - `martonUnion`: Union over all finite correlated auxiliaries and deterministic maps; both sizes are capped when cap is specified, Theorem 3, PDF p.8.
--   - `auxiliaryRateSystem`: The seven constraints (124)–(128) plus R_i <= tilde R_i, PDF pp.13–14. The two eliminated rates are real, not integer message counts.
--   - `StrongTypical`: Strongly typical supported input words, Appendix B, PDF p.17. Printed support omission is corrected explicitly; n=0 is excluded.
--   - `conditionalState1`: Receiver-1 conditional state (69), PDF p.8. At a null U1 use an arbitrary normalized channel output; supported input words never contain that U1.
--   - `averageState1`: Actual receiver-1 averaged state (70), PDF p.8; null conditional choices have no weight.
--   - `FiniteSpectralResolution`: A fixed orthonormal eigenbasis of the actual state, (141), (155), PDF pp.17–18. This record supplies eigenvalues and a unitary change of basis, never acceptance bounds.
--   - `spectralWordProjector`: Sum of product eigenvector rank-one projectors over the specified eigen-index words. It acts on the receiver's actual coordinate space, with no untracked permutation.
--   - `averagedProjector`: Strong averaged spectral projector, (145), PDF p.17, for the given actual eigenbasis.
--   - `ConditionalSpectralTypical`: Blockwise conditional spectral typicality, (164)–(170), PDF p.19. Each nonempty U1 block has its own empirical frequencies; absent blocks impose no condition.
--   - `conditionalTypicalProjector`: Strong conditional projector, PDF p.9 after (75) and p.19 (170). At each position the eigenbasis belongs to the corresponding conditional state.
--   - `receiver1Word`: Actual receiver-1 product state (68), (73)–(74), PDF pp.8–9.
-- source:
--   Classical codes for quantum broadcast channels, arXiv:1111.3645v4, https://arxiv.org/abs/1111.3645v4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P27
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P47

/-!
Classical codes for quantum broadcast channels, arXiv:1111.3645v4.
PDF page numbers throughout. All entropies and rates are in bits.
The operational average-joint-error region is independent of the information regions.
Appendix B uses supported strong typicality and compatible tolerances; see the
printed/changed/why audit in MODERATION_NOTES.md. Compilation is pending batch handoff.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Support50.P26

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact primitives from pinned accepted modules, under the independent-paper override.
-- No coding theorem or other paper's channel model is reused.
open QAlgorithms.Papers.Independent.Information100.P22 (Op quantumMI)
open QAlgorithms.Papers.Independent.Information100.P27 (shannon)
open QAlgorithms.Papers.Independent.Claimed50.P08 (cqBlocks)
open QAlgorithms.Papers.Independent.Dependency50.P47 (Law)

variable {X B1 B2 W U V A B : Type}
variable [Fintype X] [Fintype B1] [Fintype B2] [Fintype W] [Fintype U] [Fintype V]
variable [Fintype A] [Fintype B]
variable [DecidableEq X] [DecidableEq B1] [DecidableEq B2] [DecidableEq W]
variable [DecidableEq U] [DecidableEq V] [DecidableEq A] [DecidableEq B]

/-- The fixed cq broadcast channel (1), PDF p.2. Nonempty finite alphabets and
nonzero finite output dimensions are explicit; dimension one is allowed. -/
structure BroadcastChannel (X B1 B2 : Type) [Fintype X] [Fintype B1] [Fintype B2] where
  input_nonempty : Nonempty X
  output1_nonempty : Nonempty B1
  output2_nonempty : Nonempty B2
  rho : X → Op (B1 × B2)
  density : ∀ x, IsDensityMatrix (rho x)

/-- Actual memoryless output (5), PDF pp.2–3, regrouped by receiver. -/
def broadcastWordOutput (C : BroadcastChannel X B1 B2) {n : ℕ} (x : Fin n → X) :
    Op ((Fin n → B1) × (Fin n → B2)) :=
  fun a b => ∏ i, C.rho (x i) (a.1 i, a.2 i) (b.1 i, b.2 i)

/-- Definition 1, PDF p.3: deterministic encoder and separate collective block POVMs.
The two positive message sizes permit singleton messages at zero rate. -/
structure CqBroadcastCode (X B1 B2 : Type) [Fintype B1] [Fintype B2]
    [DecidableEq B1] [DecidableEq B2] (n : ℕ) where
  messages1 : ℕ
  messages2 : ℕ
  messages1_positive : 0 < messages1
  messages2_positive : 0 < messages2
  encode : Fin messages1 → Fin messages2 → Fin n → X
  decode1 : Fin messages1 → Op (Fin n → B1)
  decode2 : Fin messages2 → Op (Fin n → B2)
  decode1_povm : IsPOVM decode1
  decode2_povm : IsPOVM decode2

/-- Equations (6)–(7), PDF p.3: joint error averaged over independent uniform messages.
Both POVMs are fixed before the unknown message pair. -/
def averageJointError (C : BroadcastChannel X B1 B2) {n : ℕ}
    (D : CqBroadcastCode X B1 B2 n) : ℝ :=
  ((D.messages1 : ℝ) * D.messages2)⁻¹ *
    ∑ m1, ∑ m2, (1 - effectProb
      (Matrix.kronecker (D.decode1 m1) (D.decode2 m2))
      (broadcastWordOutput C (D.encode m1 m2)))

/-- Definition 1, PDF p.3, including boundary rates via arbitrary positive backoff.
The threshold precedes every sufficiently large block length. -/
def AverageJointAchievable (C : BroadcastChannel X B1 B2) (r : ℝ × ℝ) : Prop :=
  0 ≤ r.1 ∧ 0 ≤ r.2 ∧
    ∀ epsilon > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ N : ℕ, 0 < N ∧
      ∀ n ≥ N, ∃ D : CqBroadcastCode X B1 B2 n,
        r.1 - delta ≤ Real.logb 2 D.messages1 / n ∧
        r.2 - delta ≤ Real.logb 2 D.messages2 / n ∧
        averageJointError C D ≤ epsilon

/-- State (12), PDF p.3. A joint law is exactly p_W p_(X|W), including null rows. -/
def superState (C : BroadcastChannel X B1 B2) (p : Law (W × X)) :
    Op ((W × X) × (B1 × B2)) :=
  cqBlocks fun wx => (p.prob wx : ℂ) • C.rho wx.2

/-- The actual WB1 marginal of (12), PDF pp.3–4. -/
def superWB1 (C : BroadcastChannel X B1 B2) (p : Law (W × X)) : Op (W × B1) :=
  cqBlocks fun w => ∑ x, (p.prob (w, x) : ℂ) • traceRight (C.rho x)

/-- The actual WB2 marginal of (12), PDF p.4. -/
def superWB2 (C : BroadcastChannel X B1 B2) (p : Law (W × X)) : Op (W × B2) :=
  cqBlocks fun w => ∑ x, (p.prob (w, x) : ℂ) • traceLeft (C.rho x)

/-- I(X;B1|W) of (12), PDF p.3: H(WB1)-H(W)-sum p(w,x)H(rho_x^B1).
This form avoids conditional division at null W. -/
def superPrivate (C : BroadcastChannel X B1 B2) (p : Law (W × X)) : ℝ :=
  vnEntropy (superWB1 C p) - shannon (fun w => ∑ x, p.prob (w, x)) -
    ∑ w, ∑ x, p.prob (w, x) * vnEntropy (traceRight (C.rho x))

/-- I(X;B1) of (12), PDF p.3, as entropy of the actual average minus average entropy. -/
def superTotal (C : BroadcastChannel X B1 B2) (p : Law (W × X)) : ℝ :=
  vnEntropy (∑ w, ∑ x, (p.prob (w, x) : ℂ) • traceRight (C.rho x)) -
    ∑ w, ∑ x, p.prob (w, x) * vnEntropy (traceRight (C.rho x))

/-- All three inequalities (9)–(11), PDF p.3, at a fixed auxiliary law. -/
def SuperRegion (C : BroadcastChannel X B1 B2) (p : Law (W × X)) : Set (ℝ × ℝ) :=
  {r | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧ r.1 ≤ superPrivate C p ∧
    r.2 ≤ quantumMI (superWB2 C p) ∧ r.1 + r.2 ≤ superTotal C p}

/-- Equations (61)–(63), Remark 2, PDF pp.7–8, for the same fixed law. -/
def SuccessiveRegion (C : BroadcastChannel X B1 B2) (p : Law (W × X)) : Set (ℝ × ℝ) :=
  {r | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧ r.1 ≤ superPrivate C p ∧
    r.2 ≤ quantumMI (superWB2 C p) ∧ r.2 ≤ quantumMI (superWB1 C p)}

/-- The shared successive-decoding corner, Remark 2, PDF p.7. -/
def successiveCorner (C : BroadcastChannel X B1 B2) (p : Law (W × X)) : ℝ × ℝ :=
  (superPrivate C p, min (quantumMI (superWB1 C p)) (quantumMI (superWB2 C p)))

/-- Full auxiliary union; `some k` bounds alphabet size, `none` leaves it unrestricted.
Positive finite alphabets are represented up to relabeling by Fin(w+1). -/
def superUnion (C : BroadcastChannel X B1 B2) (cap : Option ℕ) : Set (ℝ × ℝ) :=
  {r | ∃ w : ℕ, (∀ k ∈ cap, w + 1 ≤ k) ∧
    ∃ p : Law (Fin (w + 1) × X), r ∈ SuperRegion C p}

/-- Auxiliary cardinality bound in Theorem 1, PDF p.3; positive dimensions prevent truncation. -/
def superCap (X B1 B2 : Type) [Fintype X] [Fintype B1] [Fintype B2] : ℕ :=
  min (Fintype.card X) (Fintype.card B1 ^ 2 + Fintype.card B2 ^ 2 - 1)

/-- A finite classical-output witness for Remark 2: input (w,v) gives |v,w><v,w|.
The construction only instantiates the source's existential noncoincidence assertion. -/
def separatingChannel : BroadcastChannel (Bool × Bool) Bool Bool where
  input_nonempty := inferInstance
  output1_nonempty := inferInstance
  output2_nonempty := inferInstance
  rho x := Matrix.diagonal fun z => if z = (x.2, x.1) then 1 else 0
  density x := by
    constructor
    · apply Matrix.PosSemidef.diagonal
      intro z
      change (0 : ℂ) ≤ (if z = (x.2, x.1) then 1 else 0)
      split_ifs <;> norm_num
    · simp [Matrix.trace]

/-- W,V independent fair bits, X=(W,V), so the joint (W,X) weight is 1/4 on consistency. -/
def separatingLaw : Law (Bool × (Bool × Bool)) where
  prob wx := if wx.1 = wx.2.1 then 1 / 4 else 0
  nonneg wx := by split_ifs <;> norm_num
  total := by norm_num [Fintype.sum_prod_type, Fintype.sum_bool]

/-- Marton auxiliary data, (67), PDF p.8: arbitrary correlated law and deterministic map.
The existence of a law enforces nonemptiness of both auxiliary alphabets. -/
structure MartonData (U V X : Type) [Fintype U] [Fintype V] where
  law : Law (U × V)
  encode : U → V → X

/-- Actual state (67), PDF p.8, computed from the law, map, and fixed channel. -/
def martonState (C : BroadcastChannel X B1 B2) (D : MartonData U V X) :
    Op ((U × V) × (B1 × B2)) :=
  cqBlocks fun uv => (D.law.prob uv : ℂ) • C.rho (D.encode uv.1 uv.2)

/-- Actual U1B1 marginal of (67), PDF p.8. -/
def martonU1B1 (C : BroadcastChannel X B1 B2) (D : MartonData U V X) : Op (U × B1) :=
  cqBlocks fun u => ∑ v, (D.law.prob (u, v) : ℂ) • traceRight (C.rho (D.encode u v))

/-- Actual U2B2 marginal of (67), PDF p.8. -/
def martonU2B2 (C : BroadcastChannel X B1 B2) (D : MartonData U V X) : Op (V × B2) :=
  cqBlocks fun v => ∑ u, (D.law.prob (u, v) : ℂ) • traceLeft (C.rho (D.encode u v))

/-- I(U1;U2) of the actual joint law, (66)–(67), PDF p.8. -/
def auxiliaryMI (D : MartonData U V X) : ℝ :=
  shannon (fun u => ∑ v, D.law.prob (u, v)) +
    shannon (fun v => ∑ u, D.law.prob (u, v)) - shannon D.law.prob

/-- All Marton inequalities (64)–(66), PDF p.8, including the correlation penalty. -/
def MartonRegion (C : BroadcastChannel X B1 B2) (D : MartonData U V X) : Set (ℝ × ℝ) :=
  {r | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧ r.1 ≤ quantumMI (martonU1B1 C D) ∧
    r.2 ≤ quantumMI (martonU2B2 C D) ∧
    r.1 + r.2 ≤ quantumMI (martonU1B1 C D) + quantumMI (martonU2B2 C D) - auxiliaryMI D}

/-- Union over all finite correlated auxiliaries and deterministic maps; both sizes are capped
when cap is specified, Theorem 3, PDF p.8. -/
def martonUnion (C : BroadcastChannel X B1 B2) (cap : Option ℕ) : Set (ℝ × ℝ) :=
  {r | ∃ u v : ℕ, (∀ k ∈ cap, u + 1 ≤ k ∧ v + 1 ≤ k) ∧
    ∃ D : MartonData (Fin (u + 1)) (Fin (v + 1)) X, r ∈ MartonRegion C D}

/-- The seven constraints (124)–(128) plus R_i <= tilde R_i, PDF pp.13–14.
The two eliminated rates are real, not integer message counts. -/
def auxiliaryRateSystem (a b c : ℝ) (r : ℝ × ℝ) (t1 t2 : ℝ) : Prop :=
  r.1 + r.2 + c ≤ t1 + t2 ∧
  2 * t1 + t2 ≤ a + 2 * r.1 + r.2 + c ∧ t1 ≤ a ∧
  2 * t2 + t1 ≤ b + 2 * r.2 + r.1 + c ∧ t2 ≤ b ∧
  r.1 ≤ t1 ∧ r.2 ≤ t2

/-- Strongly typical supported input words, Appendix B, PDF p.17.
Printed support omission is corrected explicitly; n=0 is excluded. -/
def StrongTypical {n : ℕ} (p : A → ℝ) (eta : ℝ) (x : Fin n → A) : Prop :=
  0 < n ∧ (∀ a, |((Finset.univ.filter fun i => x i = a).card : ℝ) / n - p a| ≤ eta) ∧
    ∀ i, 0 < p (x i)

/-- Receiver-1 conditional state (69), PDF p.8. At a null U1 use an arbitrary normalized
channel output; supported input words never contain that U1. -/
def conditionalState1 (C : BroadcastChannel X B1 B2) (D : MartonData U V X) (u : U) : Op B1 :=
  let mass := ∑ v, D.law.prob (u, v)
  if 0 < mass then (mass⁻¹ : ℂ) •
    ∑ v, (D.law.prob (u, v) : ℂ) • traceRight (C.rho (D.encode u v))
  else traceRight (C.rho (Classical.choice C.input_nonempty))

/-- Actual receiver-1 averaged state (70), PDF p.8; null conditional choices have no weight. -/
def averageState1 (C : BroadcastChannel X B1 B2) (D : MartonData U V X) : Op B1 :=
  ∑ u, ∑ v, (D.law.prob (u, v) : ℂ) • traceRight (C.rho (D.encode u v))

/-- A fixed orthonormal eigenbasis of the actual state, (141), (155), PDF pp.17–18.
This record supplies eigenvalues and a unitary change of basis, never acceptance bounds. -/
structure FiniteSpectralResolution (B : Type) [Fintype B] [DecidableEq B] (rho : Op B) where
  eigenvalue : B → ℝ
  nonnegative : ∀ z, 0 ≤ eigenvalue z
  normalized : ∑ z, eigenvalue z = 1
  basis : Matrix.unitaryGroup B ℂ
  reconstruct : ∀ a b, rho a b = ∑ z,
    (eigenvalue z : ℂ) * (basis : Op B) a z * conj ((basis : Op B) b z)

/-- Sum of product eigenvector rank-one projectors over the specified eigen-index words.
It acts on the receiver's actual coordinate space, with no untracked permutation. -/
def spectralWordProjector {n : ℕ} (basis : Fin n → Op B) (accept : (Fin n → B) → Prop) :
    Op (Fin n → B) :=
  fun a b => ∑ z : Fin n → B, if accept z then
    ∏ i, basis i (a i) (z i) * conj (basis i (b i) (z i)) else 0

/-- Strong averaged spectral projector, (145), PDF p.17, for the given actual eigenbasis. -/
def averagedProjector {rho : Op B} (S : FiniteSpectralResolution B rho) (n : ℕ) (delta : ℝ) :
    Op (Fin n → B) :=
  spectralWordProjector (fun _ => (S.basis : Op B)) (StrongTypical S.eigenvalue delta)

/-- Blockwise conditional spectral typicality, (164)–(170), PDF p.19.
Each nonempty U1 block has its own empirical frequencies; absent blocks impose no condition. -/
def ConditionalSpectralTypical {n : ℕ} (q : U → B → ℝ) (delta : ℝ)
    (u : Fin n → U) (z : Fin n → B) : Prop :=
  (∀ i, 0 < q (u i) (z i)) ∧
    ∀ a, let block := Finset.univ.filter fun i => u i = a
      0 < block.card → ∀ b,
        |((block.filter fun i => z i = b).card : ℝ) / block.card - q a b| ≤ delta

/-- Strong conditional projector, PDF p.9 after (75) and p.19 (170).
At each position the eigenbasis belongs to the corresponding conditional state. -/
def conditionalTypicalProjector (C : BroadcastChannel X B1 B2) (D : MartonData U V X)
    (S : ∀ u, FiniteSpectralResolution B1 (conditionalState1 C D u))
    {n : ℕ} (u : Fin n → U) (delta : ℝ) : Op (Fin n → B1) :=
  spectralWordProjector (fun i => ((S (u i)).basis : Op B1))
    (ConditionalSpectralTypical (fun a => (S a).eigenvalue) delta u)

/-- Actual receiver-1 product state (68), (73)–(74), PDF pp.8–9. -/
def receiver1Word (C : BroadcastChannel X B1 B2) (D : MartonData U V X)
    {n : ℕ} (u : Fin n → U) (v : Fin n → V) : Op (Fin n → B1) :=
  fun a b => ∏ i, traceRight (C.rho (D.encode (u i) (v i))) (a i) (b i)

/-- Empty tensor products are scalar identity; operational statements require positive n. -/
example (C : BroadcastChannel X B1 B2) (x : Fin 0 → X)
    (a b : (Fin 0 → B1) × (Fin 0 → B2)) : broadcastWordOutput C x a b = 1 := by
  simp [broadcastWordOutput]

/-- Classical labels give the actual diagonal block. -/
example (blocks : A → Op B) (a : A) (b c : B) :
    cqBlocks blocks (a, b) (a, c) = blocks a b c := by
  simp [cqBlocks]

/-- Both lower bounds on auxiliary rates are part of the projection system. -/
example (a b c : ℝ) (r : ℝ × ℝ) (t1 t2 : ℝ)
    (h : auxiliaryRateSystem a b c r t1 t2) : r.1 ≤ t1 ∧ r.2 ≤ t2 :=
  ⟨h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-- An absent conditional block contributes no constraint, including the empty tensor word. -/
example (q : U → B → ℝ) (delta : ℝ) (u : Fin 0 → U) (z : Fin 0 → B) :
    ConditionalSpectralTypical q delta u z := by
  simp [ConditionalSpectralTypical]

/-- A one-symbol probability distribution has zero Shannon entropy. -/
example : shannon (fun _ : Unit => (1 : ℝ)) = 0 := by
  simp [shannon]

/-- An off-diagonal classical-label block vanishes. -/
example (blocks : A → Op B) (a a2 : A) (h : a ≠ a2) (b c : B) :
    cqBlocks blocks (a, b) (a2, c) = 0 := by
  simp [cqBlocks, h]

/-- The concrete witness uses the consistency law, including its zero-probability pairs. -/
example : separatingLaw.prob (false, (false, true)) = 1 / 4 ∧
    separatingLaw.prob (false, (true, true)) = 0 := by
  constructor <;> rfl

/-- With one channel use, the receiver-1 product is exactly its channel marginal. -/
example (C : BroadcastChannel X B1 B2) (D : MartonData U V X)
    (u : Fin 1 → U) (v : Fin 1 → V) (a b : Fin 1 → B1) :
    receiver1Word C D u v a b =
      traceRight (C.rho (D.encode (u 0) (v 0))) (a 0) (b 0) := by
  simp [receiver1Word]

/-- A zero-weight conditioning symbol takes the stated normalized fallback. -/
example (C : BroadcastChannel X B1 B2) (D : MartonData U V X) (u : U)
    (h : (∑ v, D.law.prob (u, v)) = 0) :
    conditionalState1 C D u = traceRight (C.rho (Classical.choice C.input_nonempty)) := by
  simp [conditionalState1, h]

end QAlgorithms.Papers.Independent.Support50.P26


