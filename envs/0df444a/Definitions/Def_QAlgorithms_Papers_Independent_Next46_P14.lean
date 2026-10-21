-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Next46_P14
-- name    : QAlgorithms_Papers_Independent_Next46_P14
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T13:08:14.773808+00:00
-- url     : https://prove2.me/theorems/bd63fc44-10ba-417a-96e8-e5ffc83ccca6
-- title:
--   Definitions for The Capacity of Symmetric Private Information Retrieval
-- statement:
--   The objects the formalized statements of *The Capacity of Symmetric Private Information Retrieval* (arXiv:1606.08828) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `SpirParameters`: Section 2, PDF pp.2–3: prime alphabet, positive numbers of messages and servers, and positive integer message multipliers.
--   - `Message`: Section 2, PDF p.2: the k-th message consists of ell_k L field symbols.
--   - `Messages`: Section 2, PDF p.2: all replicated messages, with their joint uniform law below.
--   - `largestMultiplier`: Section 3.2, PDF p.6, (14): largest message multiplier. Finite maximum, no unbounded real supremum. SpirParameters ensures a nonempty index set.
--   - `spirEntropy`: Section 2, PDF pp.2–4: Shannon spirEntropy in p-ary units. The nonnegative extended sum preserves infinite spirEntropy; no infinite spirEntropy is projected to real zero.
--   - `spirConditionalEntropy`: Section 4.1.2, PDF pp.8–9: discrete conditional Shannon spirEntropy, expressed as the nonnegative joint-mass sum. Zero-mass summands are zero (0 log 0 = 0). Used only at prime p and for bounded-length finite-alphabet answer outputs.
--   - `Independent`: Section 2, PDF p.4, (7): independence of the entire two random objects, through factorization of their joint mass function.
--   - `SpirProtocol`: Section 2, PDF pp.3–4, (4)–(8): one-round replicated classical protocol. The answer encoder of server n receives only its query, all messages, and S; it has no requested-index or user-seed argument. Answer lengths depend only on the received query. Download is the attained worst-case TOTAL symbol count over all requests and supported user seeds. Privacy and correctness are separate predicates, so no result below assumes what it is to establish.
--   - `dataLaw`: Section 2, PDF p.3, (1)–(3): product of the joint uniform message law, private user randomness, and independent server randomness.
--   - `spirExperimentLaw`: Section 2, PDF p.3, (3): independent uniform desired index together with the data experiment. The privacy predicates compare its conditional laws for every k.
--   - `observedAnswer`: Section 2, PDF p.3, (5): evaluation of the fixed local answer function.
--   - `serverView`: Section 2, PDF p.4, (6): full view of one server, including W and S.
--   - `userView`: Section 2, PDF p.4, (7): all queries, all answers, and the private user seed.
--   - `undesired`: Section 2, PDF p.4, (7): the JOINT vector of undesired messages.
--   - `UserPrivate`: Section 2, PDF p.4, (6): every server's full law is identical for every index.
--   - `DatabasePrivate`: Section 2, PDF p.4, (7): joint database privacy against the full user view.
--   - `Private`: Section 2, PDF p.4: exact information-theoretic privacy at this blocklength.
--   - `errorProbability`: Section 2, PDF pp.3–4: decoding error probability for each fixed request, with respect to the independent message and seed ensemble.
--   - `ZeroError`: Section 3.3, PDF p.7: exact zero error for every requested message.
--   - `spirRate`: Section 2, PDF p.4, (8): field symbols of requested information per downloaded field symbol. A zero-download incorrect protocol has spirRate zero by convention.
--   - `WithinBudget`: Section 3.2, PDF p.6, (14): AVAILABLE spirEntropy budget, normalized by the largest message; unused randomness is allowed. Extended spirEntropy is retained.
--   - `ReliableSequence`: Section 2, PDF p.4, (9)–(10): operational sequence, allowing growing admissible blocklengths. Privacy is exact at every blocklength; per-index error tends to zero. The functions of each block are selected before the random messages or index.
--   - `SpirAchievable`: Section 2, PDF p.4: simultaneously achievable nonnegative LOWER spirRate guarantees, with one protocol sequence serving all indices and respecting the spirEntropy budget.
--   - `spirCapacityRegion`: Section 2, PDF p.4: closed operational region, with the paper's zero-vector convention even when no reliable private sequence exists.
--   - `spirCapacity`: Section 3.1, PDF p.4: supremum of equal-coordinate operational lower rates. An extended nonnegative supremum avoids the default value of an unbounded real supremum. The theorem establishes its finite value.
--   - `IntegerRandomness`: Section 4.3.2, PDF p.12: the special finite-length convention that H_p(S) is an integer. It is not imposed on the asymptotic model or the general converse.
--   - `spirFiniteCapacity`: Section 3.3, PDF p.7, with the p.12 convention: zero-error spirCapacity at a fixed positive L, supremized over all exact-private schemes with integral shared spirEntropy. The supremum adjoins zero without asserting a below-threshold scheme exists.
--   - `CostAchievable`: Section 3.2, PDF p.6: an asymptotic upper guarantee on normalized total download.
--   - `minimumNormalizedDownload`: Section 3.2, PDF p.6: operational infimum of achievable normalized download upper guarantees. Empty feasibility gives +infinity, never real zero.
--   - `equalParameters`: Section 3.1, PDF p.4: equal-message instance, independently of any spirCapacity claim.
--   - `pirExpression`: Section 3.1, PDF p.5, (13): scalar ordinary-PIR comparison curve cited from [3]. This definition does not assert an operational spirCapacity theorem for PIR.
--   - `BinaryArray`: Section 4.1.1, PDF p.7: binary message array and user-seed array.
--   - `binaryQuery`: Section 4.1.1, PDF p.7, (17): server 0 receives h; server i+1 receives h with coordinate (k,i) flipped. All additions are in F_2.
--   - `binaryAnswer`: Section 4.1.1, PDF pp.7–8, (18): the local encoder uses its received q, not the hidden h or k. Each server's answer is exactly one field symbol.
--   - `spirBinaryLaw`: Section 4.1.1, PDF pp.7–8: independent uniform messages, user seed, and one-bit pad.
--   - `binaryServerView`: Section 4.1.1, PDF p.8: entire per-server view (Q,A,W,S).
--   - `binaryUserView`: Section 4.1.1, PDF p.8, (19)–(24): entire user view, including h and all queries.
--   - `binaryUndesired`: Section 4.1.1, PDF p.8: joint undesired-message array for the binary scheme.
--   - `binaryDownload`: Section 4.1.1, PDF p.8: total count of the N one-symbol answers.
-- source:
--   The Capacity of Symmetric Private Information Retrieval, arXiv:1606.08828v2, https://arxiv.org/abs/1606.08828v2

import Mathlib

/-!
# The Capacity of Symmetric Private Information Retrieval

Sun–Jafar, arXiv:1606.08828v2, PDF pp.2–12.
The operational definitions below are local to this paper. No spirCapacity formula is
used in their definitions. All randomness is discrete. Natural-number labels code
arbitrary countable seed and query supports, without finiteness or computability
restrictions; relabeling the countable positive-mass support loses no discrete law.
The desired index is conditioned to each fixed k throughout; equality of all these
server laws is precisely privacy of an independent uniform desired index.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Next46.P14

/-- Section 2, PDF pp.2–3: prime alphabet, positive numbers of messages and servers,
and positive integer message multipliers. -/
structure SpirParameters where
  p : ℕ
  prime : p.Prime
  K : ℕ
  K_pos : 0 < K
  N : ℕ
  N_pos : 0 < N
  ell : Fin K → ℕ
  ell_pos : ∀ k, 0 < ell k

/-- Section 2, PDF p.2: a prime alphabet has nonzero modulus. -/
instance modulusNeZero (m : SpirParameters) : NeZero m.p := ⟨m.prime.ne_zero⟩

/-- Section 2, PDF p.2: the k-th message consists of ell_k L field symbols. -/
abbrev Message (m : SpirParameters) (L : ℕ) (k : Fin m.K) :=
  Fin (m.ell k * L) → ZMod m.p

/-- Section 2, PDF p.2: all replicated messages, with their joint uniform law below. -/
abbrev Messages (m : SpirParameters) (L : ℕ) := (k : Fin m.K) → Message m L k

/-- Section 3.2, PDF p.6, (14): largest message multiplier. Finite maximum, no
unbounded real supremum. SpirParameters ensures a nonempty index set. -/
def largestMultiplier (m : SpirParameters) : ℕ := Finset.univ.sup m.ell

/-- Section 2, PDF pp.2–4: Shannon spirEntropy in p-ary units. The nonnegative extended
sum preserves infinite spirEntropy; no infinite spirEntropy is projected to real zero. -/
def spirEntropy {A : Type*} (p : ℕ) (P : PMF A) : ℝ≥0∞ :=
  ∑' a, ENNReal.ofReal
    (-(P a).toReal * Real.log ((P a).toReal) / Real.log (p : ℝ))

/-- Section 4.1.2, PDF pp.8–9: discrete conditional Shannon spirEntropy, expressed
as the nonnegative joint-mass sum. Zero-mass summands are zero (0 log 0 = 0).
Used only at prime p and for bounded-length finite-alphabet answer outputs. -/
def spirConditionalEntropy {O A B : Type*} (p : ℕ) (P : PMF O)
    (X : O → A) (Y : O → B) : ℝ≥0∞ :=
  let joint := P.map (fun x => (X x, Y x))
  let marginal := P.map Y
  ∑' ab : A × B, ENNReal.ofReal
    (-(joint ab).toReal *
      Real.log ((joint ab).toReal / (marginal ab.2).toReal) / Real.log (p : ℝ))

/-- Section 2, PDF p.4, (7): independence of the entire two random objects,
through factorization of their joint mass function. -/
def Independent {O A B : Type*} (P : PMF O) (X : O → A) (Y : O → B) : Prop :=
  ∀ a b, (P.map (fun x => (X x, Y x))) (a, b) = (P.map X) a * (P.map Y) b

/-- Section 2, PDF pp.3–4, (4)–(8): one-round replicated classical protocol.
The answer encoder of server n receives only its query, all messages, and S;
it has no requested-index or user-seed argument. Answer lengths depend only on
the received query. Download is the attained worst-case TOTAL symbol count over
all requests and supported user seeds. Privacy and correctness are separate
predicates, so no result below assumes what it is to establish. -/
structure SpirProtocol (m : SpirParameters) (L : ℕ) where
  length_pos : 0 < L
  userSeed : PMF ℕ
  sharedSeed : PMF ℕ
  query : Fin m.K → ℕ → Fin m.N → ℕ
  format : Fin m.N → ℕ → ℕ
  answer : Fin m.N → ℕ → Messages m L → ℕ → List (ZMod m.p)
  answer_length : ∀ n q w s, (answer n q w s).length = format n q
  decode : (k : Fin m.K) → ℕ → (Fin m.N → ℕ) →
    (Fin m.N → List (ZMod m.p)) → Message m L k
  download : ℕ
  download_bound : ∀ k h, userSeed h ≠ 0 →
    (∑ n, format n (query k h n)) ≤ download
  download_attained : ∃ k h, userSeed h ≠ 0 ∧
    (∑ n, format n (query k h n)) = download

/-- Section 2, PDF p.3, (1)–(3): product of the joint uniform message law,
private user randomness, and independent server randomness. -/
def dataLaw {m : SpirParameters} {L : ℕ} (b : SpirProtocol m L) :
    PMF (Messages m L × ℕ × ℕ) :=
  (PMF.uniformOfFintype (Messages m L)).bind fun w =>
    b.userSeed.bind fun h => b.sharedSeed.map fun s => (w, h, s)

/-- Section 2, PDF p.3, (3): independent uniform desired index together with
the data experiment. The privacy predicates compare its conditional laws for every k. -/
def spirExperimentLaw {m : SpirParameters} {L : ℕ} (b : SpirProtocol m L) :
    PMF (Fin m.K × (Messages m L × ℕ × ℕ)) := by
  letI : NeZero m.K := ⟨Nat.ne_of_gt m.K_pos⟩
  exact (PMF.uniformOfFintype (Fin m.K)).bind fun k => (dataLaw b).map fun x => (k, x)

/-- Section 2, PDF p.3, (5): evaluation of the fixed local answer function. -/
def observedAnswer {m : SpirParameters} {L : ℕ} (b : SpirProtocol m L)
    (k : Fin m.K) (n : Fin m.N) (x : Messages m L × ℕ × ℕ) : List (ZMod m.p) :=
  b.answer n (b.query k x.2.1 n) x.1 x.2.2

/-- Section 2, PDF p.4, (6): full view of one server, including W and S. -/
def serverView {m : SpirParameters} {L : ℕ} (b : SpirProtocol m L)
    (k : Fin m.K) (n : Fin m.N) (x : Messages m L × ℕ × ℕ) :=
  (b.query k x.2.1 n, observedAnswer b k n x, x.1, x.2.2)

/-- Section 2, PDF p.4, (7): all queries, all answers, and the private user seed. -/
def userView {m : SpirParameters} {L : ℕ} (b : SpirProtocol m L)
    (k : Fin m.K) (x : Messages m L × ℕ × ℕ) :=
  (b.query k x.2.1, fun n => observedAnswer b k n x, x.2.1)

/-- Section 2, PDF p.4, (7): the JOINT vector of undesired messages. -/
def undesired {m : SpirParameters} {L : ℕ} (k : Fin m.K)
    (x : Messages m L × ℕ × ℕ) :=
  fun j : {j : Fin m.K // j ≠ k} => x.1 j.val

/-- Section 2, PDF p.4, (6): every server's full law is identical for every index. -/
def UserPrivate {m : SpirParameters} {L : ℕ} (b : SpirProtocol m L) : Prop :=
  ∀ k k2 n, (dataLaw b).map (serverView b k n) =
    (dataLaw b).map (serverView b k2 n)

/-- Section 2, PDF p.4, (7): joint database privacy against the full user view. -/
def DatabasePrivate {m : SpirParameters} {L : ℕ} (b : SpirProtocol m L) : Prop :=
  ∀ k, Independent (dataLaw b) (undesired k) (userView b k)

/-- Section 2, PDF p.4: exact information-theoretic privacy at this blocklength. -/
def Private {m : SpirParameters} {L : ℕ} (b : SpirProtocol m L) : Prop :=
  UserPrivate b ∧ DatabasePrivate b

/-- Section 2, PDF pp.3–4: decoding error probability for each fixed request,
with respect to the independent message and seed ensemble. -/
def errorProbability {m : SpirParameters} {L : ℕ} (b : SpirProtocol m L) (k : Fin m.K) : ℝ :=
  ((dataLaw b).map (fun x => decide
    (b.decode k x.2.1 (b.query k x.2.1) (fun n => observedAnswer b k n x) ≠ x.1 k))
    true).toReal

/-- Section 3.3, PDF p.7: exact zero error for every requested message. -/
def ZeroError {m : SpirParameters} {L : ℕ} (b : SpirProtocol m L) : Prop :=
  ∀ k, errorProbability b k = 0

/-- Section 2, PDF p.4, (8): field symbols of requested information per downloaded
field symbol. A zero-download incorrect protocol has spirRate zero by convention. -/
def spirRate {m : SpirParameters} {L : ℕ} (b : SpirProtocol m L) (k : Fin m.K) : ℝ :=
  ((m.ell k * L : ℕ) : ℝ) / (b.download : ℝ)

/-- Section 3.2, PDF p.6, (14): AVAILABLE spirEntropy budget, normalized by the
largest message; unused randomness is allowed. Extended spirEntropy is retained. -/
def WithinBudget {m : SpirParameters} {L : ℕ} (b : SpirProtocol m L) (rho : ℝ) : Prop :=
  spirEntropy m.p b.sharedSeed ≤ ENNReal.ofReal (rho * ((L * largestMultiplier m : ℕ) : ℝ))

/-- Section 2, PDF p.4, (9)–(10): operational sequence, allowing growing admissible
blocklengths. Privacy is exact at every blocklength; per-index error tends to zero.
The functions of each block are selected before the random messages or index. -/
structure ReliableSequence (m : SpirParameters) where
  length : ℕ → ℕ
  block : (t : ℕ) → SpirProtocol m (length t)
  grows : Filter.Tendsto length Filter.atTop Filter.atTop
  privacy : ∀ t, Private (block t)
  reliability : ∀ k, Filter.Tendsto (fun t => errorProbability (block t) k)
    Filter.atTop (nhds 0)

/-- Section 2, PDF p.4: simultaneously achievable nonnegative LOWER spirRate guarantees,
with one protocol sequence serving all indices and respecting the spirEntropy budget. -/
def SpirAchievable (m : SpirParameters) (rho : ℝ) (R : Fin m.K → ℝ) : Prop :=
  (∀ k, 0 ≤ R k) ∧ ∃ a : ReliableSequence m,
    (∀ t, WithinBudget (a.block t) rho) ∧ ∀ t k, R k ≤ spirRate (a.block t) k

/-- Section 2, PDF p.4: closed operational region, with the paper's zero-vector
convention even when no reliable private sequence exists. -/
def spirCapacityRegion (m : SpirParameters) (rho : ℝ) : Set (Fin m.K → ℝ) :=
  closure ({0} ∪ {R | SpirAchievable m rho R})

/-- Section 3.1, PDF p.4: supremum of equal-coordinate operational lower rates.
An extended nonnegative supremum avoids the default value of an unbounded real
supremum. The theorem establishes its finite value. -/
def spirCapacity (m : SpirParameters) (rho : ℝ) : ℝ≥0∞ :=
  ⨆ r : {r : ℝ // 0 ≤ r ∧ (fun _ : Fin m.K => r) ∈ spirCapacityRegion m rho},
    ENNReal.ofReal r.val

/-- Section 4.3.2, PDF p.12: the special finite-length convention that H_p(S)
is an integer. It is not imposed on the asymptotic model or the general converse. -/
def IntegerRandomness {m : SpirParameters} {L : ℕ} (b : SpirProtocol m L) : Prop :=
  ∃ t : ℕ, spirEntropy m.p b.sharedSeed = (t : ℝ≥0∞)

/-- Section 3.3, PDF p.7, with the p.12 convention: zero-error spirCapacity at a fixed
positive L, supremized over all exact-private schemes with integral shared spirEntropy.
The supremum adjoins zero without asserting a below-threshold scheme exists. -/
def spirFiniteCapacity (m : SpirParameters) (L : ℕ) (rho : ℝ) : ℝ≥0∞ :=
  ⨆ b : SpirProtocol m L, if Private b ∧ ZeroError b ∧ WithinBudget b rho ∧
    IntegerRandomness b then ENNReal.ofReal ((L : ℝ) / (b.download : ℝ)) else 0

/-- Section 3.2, PDF p.6: an asymptotic upper guarantee on normalized total download. -/
def CostAchievable (m : SpirParameters) (rho c : ℝ) : Prop :=
  0 ≤ c ∧ ∃ a : ReliableSequence m,
    (∀ t, WithinBudget (a.block t) rho) ∧
      ∀ t, ((a.block t).download : ℝ) / (a.length t : ℝ) ≤ c

/-- Section 3.2, PDF p.6: operational infimum of achievable normalized download
upper guarantees. Empty feasibility gives +infinity, never real zero. -/
def minimumNormalizedDownload (m : SpirParameters) (rho : ℝ) : ℝ≥0∞ :=
  sInf (ENNReal.ofReal '' {c : ℝ | CostAchievable m rho c})

/-- Section 3.1, PDF p.4: equal-message instance, independently of any spirCapacity claim. -/
def equalParameters (p : ℕ) (hp : p.Prime) (K N : ℕ)
    (hK : 0 < K) (hN : 0 < N) : SpirParameters :=
  ⟨p, hp, K, hK, N, hN, fun _ => 1, fun _ => by omega⟩

/-- Section 3.1, PDF p.5, (13): scalar ordinary-PIR comparison curve cited from [3].
This definition does not assert an operational spirCapacity theorem for PIR. -/
def pirExpression (K N : ℕ) : ℝ :=
  (∑ i ∈ Finset.range K, (1 / (N : ℝ)) ^ i)⁻¹

/-- Section 4.1.1, PDF p.7: binary message array and user-seed array. -/
abbrev BinaryArray (K N : ℕ) := Fin K → Fin (N - 1) → ZMod 2

/-- Section 4.1.1, PDF p.7, (17): server 0 receives h; server i+1 receives
h with coordinate (k,i) flipped. All additions are in F_2. -/
def binaryQuery {K N : ℕ} (k : Fin K) (n : Fin N) (h : BinaryArray K N) :
    BinaryArray K N :=
  fun j i => h j i + if j = k ∧ n.val = i.val + 1 then 1 else 0

/-- Section 4.1.1, PDF pp.7–8, (18): the local encoder uses its received q,
not the hidden h or k. Each server's answer is exactly one field symbol. -/
def binaryAnswer {K N : ℕ} (q w : BinaryArray K N) (s : ZMod 2) : ZMod 2 :=
  (∑ j, ∑ i, q j i * w j i) + s

/-- Section 4.1.1, PDF pp.7–8: independent uniform messages, user seed, and one-bit pad. -/
def spirBinaryLaw (K N : ℕ) : PMF (BinaryArray K N × BinaryArray K N × ZMod 2) :=
  PMF.uniformOfFintype (BinaryArray K N × BinaryArray K N × ZMod 2)

/-- Section 4.1.1, PDF p.8: entire per-server view (Q,A,W,S). -/
def binaryServerView {K N : ℕ} (k : Fin K) (n : Fin N)
    (x : BinaryArray K N × BinaryArray K N × ZMod 2) :=
  (binaryQuery k n x.2.1, binaryAnswer (binaryQuery k n x.2.1) x.1 x.2.2,
    x.1, x.2.2)

/-- Section 4.1.1, PDF p.8, (19)–(24): entire user view, including h and all queries. -/
def binaryUserView {K N : ℕ} (k : Fin K)
    (x : BinaryArray K N × BinaryArray K N × ZMod 2) :=
  (fun n : Fin N => binaryQuery k n x.2.1,
    fun n : Fin N => binaryAnswer (binaryQuery k n x.2.1) x.1 x.2.2, x.2.1)

/-- Section 4.1.1, PDF p.8: joint undesired-message array for the binary scheme. -/
def binaryUndesired {K N : ℕ} (k : Fin K)
    (x : BinaryArray K N × BinaryArray K N × ZMod 2) :=
  fun j : {j : Fin K // j ≠ k} => x.1 j.val

/-- Section 4.1.1, PDF p.8: total count of the N one-symbol answers. -/
def binaryDownload (N : ℕ) : ℕ := ∑ _ : Fin N, 1

/-- The empty undesired-message index set at K=1, PDF p.4. -/
example (k : Fin 1) : IsEmpty {j : Fin 1 // j ≠ k} := by
  refine ⟨fun j => j.property (Subsingleton.elim _ _)⟩

/-- The zero-vector convention is retained even if reliable schemes are absent. -/
example (m : SpirParameters) (rho : ℝ) : (0 : Fin m.K → ℝ) ∈ spirCapacityRegion m rho := by
  exact subset_closure (Or.inl rfl)

/-- Constant-source spirEntropy is zero, consistent with no common randomness. -/
example : spirEntropy 2 (PMF.pure () : PMF Unit) = 0 := by
  simp [spirEntropy]

/-- The baseline query does not depend on k, PDF p.7, (17). -/
example {K N : ℕ} (hN : 0 < N) (k : Fin K) (h : BinaryArray K N) :
    binaryQuery k (⟨0, hN⟩ : Fin N) h = h := by
  funext j i
  simp [binaryQuery]

/-- A zero received coefficient array returns just the shared pad, PDF p.7, (18). -/
example {K N : ℕ} (w : BinaryArray K N) (s : ZMod 2) :
    binaryAnswer (fun _ _ => 0) w s = s := by
  simp [binaryAnswer]

end QAlgorithms.Papers.Independent.Next46.P14


