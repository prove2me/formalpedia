-- Prove2me | Definitions.Def_DetDLP_W5_M6DivisorConstraints
-- name    : DetDLP_W5_M6DivisorConstraints
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T00:31:11.700847+00:00
-- url     : https://prove2.me/theorems/9c8111c7-9ec3-4cb5-a246-756eb5ffddf5
-- title:
--   M6 Divisor Constraints
-- statement:
--   A parsimonious multiplier graph with output and prefix pins counts the feasible completions of each prefix. Removing the two trivial products makes a binary prefix search return a proper divisor of every composite input using at most four queries per input bit.

import Definitions.Def_DetDLP_BTN

set_option autoImplicit false

namespace DetDLP
namespace w5_M6DivisorConstraints

/-- A global edge assignment satisfies every Boolean tensor. -/
def Satisfies (G : BipartiteMultigraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
    (x : Fin G.nE → Bool) : Prop :=
  ∀ v, T v (fun j => x ((G.ports v).get j)) = true

/-- A partial assignment of interface bits, with `none` meaning unpinned. -/
def MatchesPins {k : ℕ} (pin : Fin k → Option Bool) (x : Fin k → Bool) : Prop :=
  ∀ i b, pin i = some b → x i = b

/-- Pinning is absorbed into the old endpoint tensors, without adding vertices or edges. -/
def pinTensor (G : BipartiteMultigraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
    {k : ℕ} (ext : Fin k → Fin G.nE) (pin : Fin k → Option Bool)
    (v : Fin G.nV) (α : Fin (G.deg v) → Bool) : Bool :=
  T v α && (List.finRange k).all (fun i =>
    (List.finRange (G.deg v)).all (fun j =>
      if (G.ports v).get j = ext i then
        match pin i with
        | none => true
        | some b => α j == b
      else true))

lemma pinTensor_eq_true (G : BipartiteMultigraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
    {k : ℕ} (ext : Fin k → Fin G.nE) (pin : Fin k → Option Bool)
    (v : Fin G.nV) (α : Fin (G.deg v) → Bool) :
    pinTensor G T ext pin v α = true ↔ T v α = true ∧
      (∀ i b, pin i = some b →
        ∀ j : Fin (G.deg v), (G.ports v).get j = ext i → α j = b) := by
  simp only [pinTensor, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const]
  constructor
  · rintro ⟨hT, h⟩
    refine ⟨hT, ?_⟩
    intro i b hb j hj
    simpa [hj, hb] using h i j
  · rintro ⟨hT, h⟩
    refine ⟨hT, ?_⟩
    intro i j
    by_cases hj : (G.ports v).get j = ext i
    · cases hb : pin i with
      | none => simp [hj]
      | some b => simpa [hj, hb] using h i b hb j hj
    · simp [hj]

lemma edge_mem_first_ports (G : BipartiteMultigraph) (e : Fin G.nE) :
    e ∈ G.ports (G.endpoints e).1 := by
  simp [BipartiteMultigraph.ports]

lemma satisfies_pinTensor_iff (G : BipartiteMultigraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
    {k : ℕ} (ext : Fin k → Fin G.nE) (pin : Fin k → Option Bool)
    (x : Fin G.nE → Bool) :
    Satisfies G (pinTensor G T ext pin) x ↔
      Satisfies G T x ∧ MatchesPins pin (fun i => x (ext i)) := by
  classical
  simp only [Satisfies, pinTensor_eq_true]
  constructor
  · intro h
    refine ⟨fun v => (h v).1, ?_⟩
    intro i b hb
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp (edge_mem_first_ports G (ext i))
    simpa only [hj] using (h (G.endpoints (ext i)).1).2 i b hb j hj
  · rintro ⟨hT, hpin⟩ v
    refine ⟨hT v, ?_⟩
    intro i b hb j hj
    rw [hj]
    exact hpin i b hb

lemma relation_of_satisfies (G : BipartiteMultigraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
    {k : ℕ} (ext : Fin k → Fin G.nE) (R : (Fin k → Bool) → Prop)
    (hpar : IsParsimonious G T ext R) (x : Fin G.nE → Bool)
    (hx : Satisfies G T x) : R (fun i => x (ext i)) := by
  by_contra hn
  exact (hpar.2 _).2 hn ⟨x, (fun _ => rfl), hx⟩

/-- Pins preserve parsimony, including its no-extension clause. -/
theorem parsimonious_pinTensor (G : BipartiteMultigraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
    {k : ℕ} (ext : Fin k → Fin G.nE) (R : (Fin k → Bool) → Prop)
    (hpar : IsParsimonious G T ext R) (pin : Fin k → Option Bool) :
    IsParsimonious G (pinTensor G T ext pin) ext
      (fun y => R y ∧ MatchesPins pin y) := by
  classical
  refine ⟨hpar.1, fun y => ⟨?_, ?_⟩⟩
  · rintro ⟨hR, hp⟩
    obtain ⟨x, hx, huniq⟩ := (hpar.2 y).1 hR
    refine ⟨x, ⟨hx.1, ?_⟩, ?_⟩
    · apply (satisfies_pinTensor_iff G T ext pin x).2
      refine ⟨hx.2, ?_⟩
      intro i b hb
      exact (hx.1 i).trans (hp i b hb)
    · rintro z ⟨hz, hpinz⟩
      exact huniq z ⟨hz, ((satisfies_pinTensor_iff G T ext pin z).1 hpinz).1⟩
  · intro hn hex
    obtain ⟨x, hx, hs⟩ := hex
    obtain ⟨hT, hp⟩ := (satisfies_pinTensor_iff G T ext pin x).1 hs
    apply hn
    have heq : (fun i => x (ext i)) = y := funext hx
    rw [← heq]
    exact ⟨relation_of_satisfies G T ext R hpar x hT, hp⟩

/-- Restriction to the interface is a bijection on satisfying assignments. -/
noncomputable def satisfyingEquiv (G : BipartiteMultigraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
    {k : ℕ} (ext : Fin k → Fin G.nE) (R : (Fin k → Bool) → Prop)
    (hpar : IsParsimonious G T ext R) :
    {x : Fin G.nE → Bool // Satisfies G T x} ≃ {y : Fin k → Bool // R y} := by
  classical
  let f : {x : Fin G.nE → Bool // Satisfies G T x} →
      {y : Fin k → Bool // R y} :=
    fun x => ⟨fun i => x.val (ext i), relation_of_satisfies G T ext R hpar x.val x.property⟩
  apply Equiv.ofBijective f
  constructor
  · intro x z h
    have hxz : (fun i => x.val (ext i)) = (fun i => z.val (ext i)) :=
      congrArg Subtype.val h
    obtain ⟨w, _, hw⟩ := (hpar.2 _).1 (f x).property
    apply Subtype.ext
    exact (hw x.val ⟨fun _ => rfl, x.property⟩).trans
      (hw z.val ⟨fun i => (congrFun hxz i).symm, z.property⟩).symm
  · intro y
    obtain ⟨x, hx, _⟩ := (hpar.2 y.val).1 y.property
    refine ⟨⟨x, hx.2⟩, ?_⟩
    apply Subtype.ext
    exact funext hx.1

/-- Boolean tensors embedded in any commutative ring count satisfying assignments. -/
theorem contract_eq_sat_card (G : BipartiteMultigraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
    {S : Type*} [CommRing S] :
    BTNContract G (fun v α => if T v α then (1 : S) else 0) =
      (Nat.card {x : Fin G.nE → Bool // Satisfies G T x} : S) := by
  classical
  unfold BTNContract
  have hterm (x : Fin G.nE → Bool) :
      (∏ v : Fin G.nV, if T v (fun j => x ((G.ports v).get j)) then (1 : S) else 0) =
        if Satisfies G T x then 1 else 0 := by
    by_cases hx : Satisfies G T x
    · rw [if_pos hx]
      exact Finset.prod_eq_one fun v _ => by rw [if_pos (hx v)]
    · rw [if_neg hx]
      simp only [Satisfies, not_forall] at hx
      obtain ⟨v, hv⟩ := hx
      exact Finset.prod_eq_zero (Finset.mem_univ v) (by rw [if_neg hv])
  simp_rw [hterm]
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using
    (Finset.sum_boole (R := S) (Satisfies G T) (Finset.univ : Finset (Fin G.nE → Bool)))

/-- The count returned by a parsimonious network is exactly the interface-relation count. -/
theorem contract_eq_relation_card (G : BipartiteMultigraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
    {k : ℕ} (ext : Fin k → Fin G.nE) (R : (Fin k → Bool) → Prop)
    (hpar : IsParsimonious G T ext R) {S : Type*} [CommRing S] :
    BTNContract G (fun v α => if T v α then (1 : S) else 0) =
      (Nat.card {y : Fin k → Bool // R y} : S) := by
  rw [contract_eq_sat_card]
  exact congrArg (fun n : ℕ => (n : S)) (Nat.card_congr (satisfyingEquiv G T ext R hpar))

/-- The count for a partial interface assignment, with no graph-size overhead. -/
theorem contract_pin_eq_relation_card (G : BipartiteMultigraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
    {k : ℕ} (ext : Fin k → Fin G.nE) (R : (Fin k → Bool) → Prop)
    (hpar : IsParsimonious G T ext R) (pin : Fin k → Option Bool)
    {S : Type*} [CommRing S] :
    BTNContract G (fun v α => if pinTensor G T ext pin v α then (1 : S) else 0) =
      (Nat.card {y : Fin k → Bool // R y ∧ MatchesPins pin y} : S) :=
  contract_eq_relation_card G (pinTensor G T ext pin) ext _
    (parsimonious_pinTensor G T ext R hpar pin)

/-- Evaluation at zero descends to every positive truncation length. -/
noncomputable def truncConstantHom (P0 ℓ : ℕ) (hℓ : 0 < ℓ) :
    TruncPoly P0 ℓ →+* ZMod (2 ^ P0) :=
  Ideal.Quotient.lift _ (Polynomial.evalRingHom 0) (by
    have hle : Ideal.span {(Polynomial.X : Polynomial (ZMod (2 ^ P0))) ^ ℓ} ≤
        RingHom.ker (Polynomial.evalRingHom 0) := by
      rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
      simp [hℓ.ne']
    intro p hp
    exact hle hp)

/-- A small natural count cannot disappear in the truncated coefficient ring. -/
theorem trunc_natCast_ne_zero_iff (P0 ℓ c : ℕ) (hℓ : 0 < ℓ) (hc : c < 2 ^ P0) :
    (c : TruncPoly P0 ℓ) ≠ 0 ↔ c ≠ 0 := by
  constructor
  · intro h hzero
    subst c
    exact h (by simp)
  · intro hc0 heq
    have hmod : (c : ZMod (2 ^ P0)) = 0 := by
      simpa only [map_natCast, map_zero] using congrArg (truncConstantHom P0 ℓ hℓ) heq
    have hval := congrArg ZMod.val hmod
    rw [ZMod.val_natCast_of_lt hc, ZMod.val_zero] at hval
    exact hc0 hval

lemma relation_card_lt_pow (G : BipartiteMultigraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
    {k : ℕ} (ext : Fin k → Fin G.nE) (R : (Fin k → Bool) → Prop)
    (hpar : IsParsimonious G T ext R) (P0 : ℕ) (hP0 : G.nE < P0) :
    Nat.card {y : Fin k → Bool // R y} < 2 ^ P0 := by
  classical
  rw [← Nat.card_congr (satisfyingEquiv G T ext R hpar)]
  have hle : Nat.card {x : Fin G.nE → Bool // Satisfies G T x} ≤ 2 ^ G.nE := by
    rw [Nat.card_eq_fintype_card]
    simpa using Fintype.card_subtype_le (Satisfies G T)
  exact hle.trans_lt ((Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).2 hP0)

/-- With sufficient coefficient precision, the pinned contraction tests completion exactly. -/
theorem contract_pin_ne_zero_iff (G : BipartiteMultigraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
    {k : ℕ} (ext : Fin k → Fin G.nE) (R : (Fin k → Bool) → Prop)
    (hpar : IsParsimonious G T ext R) (pin : Fin k → Option Bool)
    (P0 ℓ : ℕ) (hP0 : G.nE < P0) (hℓ : 0 < ℓ) :
    BTNContract G (fun v α => if pinTensor G T ext pin v α
      then (1 : TruncPoly P0 ℓ) else 0) ≠ 0 ↔
      ∃ y, R y ∧ MatchesPins pin y := by
  rw [contract_pin_eq_relation_card G T ext R hpar pin]
  rw [trunc_natCast_ne_zero_iff P0 ℓ _ hℓ
    (relation_card_lt_pow G (pinTensor G T ext pin) ext _
      (parsimonious_pinTensor G T ext R hpar pin) P0 hP0)]
  rw [Nat.card_ne_zero]
  simp only [and_iff_left (inferInstance : Finite {y : Fin k → Bool // R y ∧ MatchesPins pin y})]
  exact nonempty_subtype

/-- A completion oracle tests whether a pinned relation has a witness. -/
def CompletionOracle {k : ℕ} (R : (Fin k → Bool) → Prop)
    (oracle : (Fin k → Option Bool) → Bool) : Prop :=
  ∀ pin, oracle pin = true ↔ ∃ y, R y ∧ MatchesPins pin y

/-- A stronger partial assignment preserves all previously pinned bits. -/
def Refines {k : ℕ} (old new : Fin k → Option Bool) : Prop :=
  ∀ i b, old i = some b → new i = some b

lemma refines_refl {k : ℕ} (pin : Fin k → Option Bool) : Refines pin pin :=
  fun _ _ h => h

lemma refines_trans {k : ℕ} {a b c : Fin k → Option Bool}
    (hab : Refines a b) (hbc : Refines b c) : Refines a c :=
  fun i v h => hbc i v (hab i v h)

lemma matchesPins_of_refines {k : ℕ} {old new : Fin k → Option Bool}
    (h : Refines old new) {y : Fin k → Bool} (hy : MatchesPins new y) :
    MatchesPins old y := fun i b hi => hy i b (h i b hi)

lemma matchesPins_update {k : ℕ} (pin : Fin k → Option Bool) (i : Fin k)
    (b : Bool) (y : Fin k → Bool) (hy : MatchesPins pin y) (hyi : y i = b) :
    MatchesPins (Function.update pin i (some b)) y := by
  intro j c hj
  by_cases hji : j = i
  · subst j
    simpa using hyi.trans (by simpa using hj : b = c)
  · apply hy j c
    simpa [Function.update, hji] using hj

lemma refines_update_none {k : ℕ} (pin : Fin k → Option Bool) (i : Fin k)
    (b : Bool) (hi : pin i = none) : Refines pin (Function.update pin i (some b)) := by
  intro j c hj
  by_cases hji : j = i
  · subst j
    rw [hi] at hj
    cases hj
  · simpa [Function.update, hji] using hj

/-- One oracle call chooses zero when that branch has a completion; old pins are retained. -/
def choosePin {k : ℕ} (oracle : (Fin k → Option Bool) → Bool)
    (pin : Fin k → Option Bool) (i : Fin k) : Fin k → Option Bool :=
  if pin i = none then
    if oracle (Function.update pin i (some false)) then
      Function.update pin i (some false)
    else Function.update pin i (some true)
  else pin

lemma choosePin_refines {k : ℕ} (oracle : (Fin k → Option Bool) → Bool)
    (pin : Fin k → Option Bool) (i : Fin k) : Refines pin (choosePin oracle pin i) := by
  unfold choosePin
  split
  · split <;> exact refines_update_none pin i _ ‹_›
  · exact refines_refl pin

lemma choosePin_assigned {k : ℕ} (oracle : (Fin k → Option Bool) → Bool)
    (pin : Fin k → Option Bool) (i : Fin k) :
    ∃ b, choosePin oracle pin i i = some b := by
  unfold choosePin
  split
  · split
    · exact ⟨false, by simp⟩
    · exact ⟨true, by simp⟩
  · cases h : pin i with
    | none => contradiction
    | some b => exact ⟨b, rfl⟩

lemma choosePin_has_completion {k : ℕ} (R : (Fin k → Bool) → Prop)
    (oracle : (Fin k → Option Bool) → Bool) (ho : CompletionOracle R oracle)
    (pin : Fin k → Option Bool) (i : Fin k)
    (h : ∃ y, R y ∧ MatchesPins pin y) :
    ∃ y, R y ∧ MatchesPins (choosePin oracle pin i) y := by
  unfold choosePin
  split
  · split
    · exact (ho _).1 ‹_›
    · obtain ⟨y, hR, hy⟩ := h
      have hyi : y i = true := by
        cases hb : y i
        · have hzero : oracle (Function.update pin i (some false)) = true :=
            (ho _).2 ⟨y, hR, matchesPins_update pin i false y hy hb⟩
          contradiction
        · rfl
      exact ⟨y, hR, matchesPins_update pin i true y hy hyi⟩
  · exact h

/-- Iterate the one-query choice in any requested bit order. -/
def completePins {k : ℕ} (oracle : (Fin k → Option Bool) → Bool) :
    List (Fin k) → (Fin k → Option Bool) → (Fin k → Option Bool)
  | [], pin => pin
  | i :: rest, pin => completePins oracle rest (choosePin oracle pin i)

lemma completePins_refines {k : ℕ} (oracle : (Fin k → Option Bool) → Bool)
    (order : List (Fin k)) (pin : Fin k → Option Bool) :
    Refines pin (completePins oracle order pin) := by
  induction order generalizing pin with
  | nil => exact refines_refl pin
  | cons i rest ih =>
    exact refines_trans (choosePin_refines oracle pin i) (ih _)

lemma completePins_assigned {k : ℕ} (oracle : (Fin k → Option Bool) → Bool)
    (order : List (Fin k)) (pin : Fin k → Option Bool) (i : Fin k)
    (hi : i ∈ order) : ∃ b, completePins oracle order pin i = some b := by
  induction order generalizing pin with
  | nil => cases hi
  | cons j rest ih =>
    rcases List.mem_cons.mp hi with rfl | hi
    · obtain ⟨b, hb⟩ := choosePin_assigned oracle pin i
      exact ⟨b, completePins_refines oracle rest (choosePin oracle pin i) i b hb⟩
    · exact ih _ hi

lemma completePins_has_completion {k : ℕ} (R : (Fin k → Bool) → Prop)
    (oracle : (Fin k → Option Bool) → Bool) (ho : CompletionOracle R oracle)
    (order : List (Fin k)) (pin : Fin k → Option Bool)
    (h : ∃ y, R y ∧ MatchesPins pin y) :
    ∃ y, R y ∧ MatchesPins (completePins oracle order pin) y := by
  induction order generalizing pin with
  | nil => exact h
  | cons i rest ih => exact ih _ (choosePin_has_completion R oracle ho pin i h)

/-- Decoding the fully pinned word after exactly the listed sequence of choices. -/
def searchWord {k : ℕ} (oracle : (Fin k → Option Bool) → Bool)
    (order : List (Fin k)) (pin : Fin k → Option Bool) : Fin k → Bool :=
  fun i => (completePins oracle order pin i).getD false

/-- Deterministic prefix search recovers a witness, using any order containing every bit. -/
theorem searchWord_spec {k : ℕ} (R : (Fin k → Bool) → Prop)
    (oracle : (Fin k → Option Bool) → Bool) (ho : CompletionOracle R oracle)
    (order : List (Fin k)) (horder : ∀ i, i ∈ order)
    (pin : Fin k → Option Bool) (h : ∃ y, R y ∧ MatchesPins pin y) :
    R (searchWord oracle order pin) ∧ MatchesPins pin (searchWord oracle order pin) := by
  obtain ⟨y, hR, hy⟩ := completePins_has_completion R oracle ho order pin h
  have heq : searchWord oracle order pin = y := by
    funext i
    obtain ⟨b, hb⟩ := completePins_assigned oracle order pin i (horder i)
    have hyi := hy i b hb
    simp [searchWord, hb, hyi]
  rw [heq]
  exact ⟨hR, matchesPins_of_refines (completePins_refines oracle order pin) hy⟩

/-- A semantic counter for oracle calls in `completePins`. -/
def completionQueryCount {k : ℕ} (oracle : (Fin k → Option Bool) → Bool) :
    List (Fin k) → (Fin k → Option Bool) → ℕ
  | [], _ => 0
  | i :: rest, pin => (if pin i = none then 1 else 0) +
      completionQueryCount oracle rest (choosePin oracle pin i)

lemma completionQueryCount_le_length {k : ℕ}
    (oracle : (Fin k → Option Bool) → Bool) (order : List (Fin k))
    (pin : Fin k → Option Bool) : completionQueryCount oracle order pin ≤ order.length := by
  induction order generalizing pin with
  | nil => simp [completionQueryCount]
  | cons i rest ih =>
    simp only [completionQueryCount, List.length_cons]
    have h := ih (choosePin oracle pin i)
    split <;> omega

/-- The most-significant-first search uses at most `k` count queries. -/
theorem binary_search_query_bound {k : ℕ}
    (oracle : (Fin k → Option Bool) → Bool) (pin : Fin k → Option Bool) :
    completionQueryCount oracle (List.finRange k).reverse pin ≤ k := by
  simpa using completionQueryCount_le_length oracle (List.finRange k).reverse pin

/-- A witness-producing search with all the interface bits ordered high to low. -/
theorem binary_search_spec {k : ℕ} (R : (Fin k → Bool) → Prop)
    (oracle : (Fin k → Option Bool) → Bool) (ho : CompletionOracle R oracle)
    (pin : Fin k → Option Bool) (h : ∃ y, R y ∧ MatchesPins pin y) :
    R (searchWord oracle (List.finRange k).reverse pin) ∧
      MatchesPins pin (searchWord oracle (List.finRange k).reverse pin) :=
  searchWord_spec R oracle ho _ (by simp) pin h

/-- Removing two distinguished assignments changes a finite count by two indicators. -/
lemma erase_two_card {α : Type*} [DecidableEq α] (s : Finset α) (a b : α) (hab : a ≠ b) :
    ((s.erase a).erase b).card + (if a ∈ s then 1 else 0) +
      (if b ∈ s then 1 else 0) = s.card := by
  have herase (t : Finset α) (x : α) :
      (t.erase x).card + (if x ∈ t then 1 else 0) = t.card := by
    by_cases hx : x ∈ t
    · rw [if_pos hx]
      exact Finset.card_erase_add_one hx
    · simp [hx]
  have ha := herase s a
  have hb := herase (s.erase a) b
  simp only [Finset.mem_erase, hab.symm, ne_eq, not_false_eq_true, true_and] at hb
  omega

/-- The exact cardinality of the completions of a partial assignment. -/
noncomputable def completionCount {k : ℕ} (R : (Fin k → Bool) → Prop)
    (pin : Fin k → Option Bool) : ℕ := by
  classical
  exact (Finset.univ.filter fun y => R y ∧ MatchesPins pin y).card

/-- Executable finite-loop test of a partial assignment against a word. -/
def matchesPinsBool {k : ℕ} (pin : Fin k → Option Bool) (x : Fin k → Bool) : Bool :=
  (List.finRange k).all fun i => match pin i with
    | none => true
    | some b => x i == b

lemma matchesPinsBool_eq_true {k : ℕ} (pin : Fin k → Option Bool) (x : Fin k → Bool) :
    matchesPinsBool pin x = true ↔ MatchesPins pin x := by
  simp only [matchesPinsBool, List.all_eq_true, List.mem_finRange, forall_const]
  constructor
  · intro h i b hb
    simpa only [hb, beq_iff_eq] using h i
  · intro h i
    cases hb : pin i with
    | none => rfl
    | some b => simpa only [beq_iff_eq] using h i b hb

def matchesPinsDecidable {k : ℕ} (pin : Fin k → Option Bool) (x : Fin k → Bool) :
    Decidable (MatchesPins pin x) :=
  decidable_of_iff (matchesPinsBool pin x = true) (matchesPinsBool_eq_true pin x)

/-- The trivial factor-pair contribution is computed from the pinned bits without a count query. -/
def trivialCount {k : ℕ} (a b : Fin k → Bool)
    (pin : Fin k → Option Bool) : ℕ :=
  (if matchesPinsBool pin a then 1 else 0) + (if matchesPinsBool pin b then 1 else 0)

lemma trivialCount_eq {k : ℕ} (a b : Fin k → Bool) (pin : Fin k → Option Bool)
    [Decidable (MatchesPins pin a)] [Decidable (MatchesPins pin b)] :
    trivialCount a b pin = (if MatchesPins pin a then 1 else 0) +
      (if MatchesPins pin b then 1 else 0) := by
  simp only [trivialCount, matchesPinsBool_eq_true]

lemma completionCount_pos_iff {k : ℕ} (R : (Fin k → Bool) → Prop)
    (pin : Fin k → Option Bool) :
    0 < completionCount R pin ↔ ∃ y, R y ∧ MatchesPins pin y := by
  classical
  simp only [completionCount, Finset.card_pos, Finset.nonempty_def,
    Finset.mem_filter, Finset.mem_univ, true_and]

/-- Proper-factor completion counts require only subtracting the two trivial solutions. -/
theorem completionCount_remove_two {k : ℕ} (R : (Fin k → Bool) → Prop)
    (a b : Fin k → Bool) (ha : R a) (hb : R b) (hab : a ≠ b)
    (pin : Fin k → Option Bool) :
    completionCount (fun y => R y ∧ y ≠ a ∧ y ≠ b) pin + trivialCount a b pin =
      completionCount R pin := by
  classical
  have hset :
      (Finset.univ.filter fun y => (R y ∧ y ≠ a ∧ y ≠ b) ∧ MatchesPins pin y) =
      ((Finset.univ.filter fun y => R y ∧ MatchesPins pin y).erase a).erase b := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    tauto
  have h := erase_two_card (Finset.univ.filter fun y => R y ∧ MatchesPins pin y) a b hab
  rw [← hset] at h
  simpa only [completionCount, trivialCount_eq, Finset.mem_filter,
    Finset.mem_univ, true_and, ha, hb, add_assoc] using h

/-- A count oracle for all product witnesses yields a proper-factor oracle by removing two terms. -/
def correctedOracle {k : ℕ} (count : (Fin k → Option Bool) → ℕ)
    (a b : Fin k → Bool) (pin : Fin k → Option Bool) : Bool :=
  decide (trivialCount a b pin < count pin)

theorem correctedOracle_spec {k : ℕ} (R : (Fin k → Bool) → Prop)
    (count : (Fin k → Option Bool) → ℕ)
    (hcount : ∀ pin, count pin = completionCount R pin)
    (a b : Fin k → Bool) (ha : R a) (hb : R b) (hab : a ≠ b) :
    CompletionOracle (fun y => R y ∧ y ≠ a ∧ y ≠ b) (correctedOracle count a b) := by
  intro pin
  simp only [correctedOracle, decide_eq_true_eq, hcount]
  rw [← completionCount_remove_two R a b ha hb hab pin]
  rw [← completionCount_pos_iff]
  omega

/-- Search on the original multiplication graph can exclude both trivial factors arithmetically. -/
theorem corrected_binary_search_spec {k : ℕ} (R : (Fin k → Bool) → Prop)
    (count : (Fin k → Option Bool) → ℕ)
    (hcount : ∀ pin, count pin = completionCount R pin)
    (a b : Fin k → Bool) (ha : R a) (hb : R b) (hab : a ≠ b)
    (pin : Fin k → Option Bool)
    (hex : ∃ y, (R y ∧ y ≠ a ∧ y ≠ b) ∧ MatchesPins pin y) :
    let y := searchWord (correctedOracle count a b) (List.finRange k).reverse pin
    (R y ∧ y ≠ a ∧ y ≠ b) ∧ MatchesPins pin y :=
  binary_search_spec _ _ (correctedOracle_spec R count hcount a b ha hb hab) pin hex

/-- Explicit little-endian binary encoding, used to pin constants in the product word. -/
def natWord : (d : ℕ) → ℕ → (Fin d → Bool)
  | 0, _ => Fin.elim0
  | d + 1, a => Fin.cons (a % 2 == 1) (natWord d (a / 2))

lemma bitsToNat_cons {d : ℕ} (b : Bool) (w : Fin d → Bool) :
    bitsToNat (Fin.cons b w) = (if b then 1 else 0) + 2 * bitsToNat w := by
  simp only [bitsToNat, Fin.sum_univ_succ, Fin.cons_zero, Fin.val_zero, pow_zero,
    mul_one, Fin.cons_succ, Fin.val_succ, pow_succ]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma bitsToNat_lt {d : ℕ} (w : Fin d → Bool) : bitsToNat w < 2 ^ d := by
  induction d with
  | zero => simp [bitsToNat]
  | succ d ih =>
    rw [← Fin.cons_self_tail w, bitsToNat_cons, pow_succ]
    have h := ih (Fin.tail w)
    cases w 0 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

lemma bitsToNat_natWord (d a : ℕ) (ha : a < 2 ^ d) : bitsToNat (natWord d a) = a := by
  induction d generalizing a with
  | zero => have : a = 0 := by simpa using ha
            simp [natWord, bitsToNat, this]
  | succ d ih =>
    rw [natWord, bitsToNat_cons]
    have hdiv : a / 2 < 2 ^ d := by
      apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).2
      simpa [pow_succ, Nat.mul_comm] using ha
    rw [ih _ hdiv]
    have hm : a % 2 < 2 := Nat.mod_lt a (by decide)
    have heq := Nat.mod_add_div a 2
    by_cases h : a % 2 = 1 <;> simp [h] <;> omega

lemma natWord_bitsToNat (d : ℕ) (w : Fin d → Bool) : natWord d (bitsToNat w) = w := by
  induction d with
  | zero => exact Subsingleton.elim _ _
  | succ d ih =>
    conv_lhs => rw [← Fin.cons_self_tail w, bitsToNat_cons, natWord]
    have hlow : (((if w 0 then 1 else 0) + 2 * bitsToNat (Fin.tail w)) % 2 == 1) =
        w 0 := by cases w 0 <;> simp
    have hhigh : ((if w 0 then 1 else 0) + 2 * bitsToNat (Fin.tail w)) / 2 =
        bitsToNat (Fin.tail w) := by cases w 0 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
    rw [hlow, hhigh, ih]
    exact Fin.cons_self_tail w

lemma bitsToNat_injective (d : ℕ) : Function.Injective (@bitsToNat d) := by
  intro a b h
  rw [← natWord_bitsToNat d a, ← natWord_bitsToNat d b, h]

/-- Three blocks of lengths `d,d,2d`, matching the target gadget's exact interface. -/
def inputA {d : ℕ} (x : Fin (4 * d) → Bool) : Fin d → Bool :=
  fun i => x ⟨i.val, by omega⟩
def inputB {d : ℕ} (x : Fin (4 * d) → Bool) : Fin d → Bool :=
  fun i => x ⟨d + i.val, by omega⟩
def productWord {d : ℕ} (x : Fin (4 * d) → Bool) : Fin (2 * d) → Bool :=
  fun i => x ⟨2 * d + i.val, by omega⟩

/-- The relation counted when only the product block is pinned. -/
def ProductIs {d : ℕ} (N : ℕ) (x : Fin (4 * d) → Bool) : Prop :=
  bitsToNat (inputA x) * bitsToNat (inputB x) = N ∧
    bitsToNat (productWord x) = N

/-- The same local tensor network represents product pinning without any comparator. -/
def outputPins (d N : ℕ) : Fin (4 * d) → Option Bool :=
  fun i => if h : 2 * d ≤ i.val then
    some (natWord (2 * d) N ⟨i.val - 2 * d, by omega⟩) else none

lemma matches_outputPins_iff {d N : ℕ} (hN : N < 2 ^ (2 * d))
    (x : Fin (4 * d) → Bool) :
    MatchesPins (outputPins d N) x ↔ bitsToNat (productWord x) = N := by
  constructor
  · intro h
    have heq : productWord x = natWord (2 * d) N := by
      funext i
      have hpin : outputPins d N ⟨2 * d + i.val, by omega⟩ =
          some (natWord (2 * d) N i) := by simp [outputPins]
      exact h _ _ hpin
    rw [heq, bitsToNat_natWord _ _ hN]
  · intro h i b hb
    have heq : productWord x = natWord (2 * d) N := by
      apply bitsToNat_injective
      rw [h, bitsToNat_natWord _ _ hN]
    unfold outputPins at hb
    split at hb
    · rename_i hi
      have hword := congrFun heq ⟨i.val - 2 * d, by omega⟩
      have hind : (⟨2 * d + (i.val - 2 * d), by omega⟩ : Fin (4 * d)) = i :=
        Fin.ext (by dsimp; omega)
      simpa only [productWord, hind, Option.some.inj hb] using hword
    · cases hb

/-- Pack the three blocks in the interface order used by the multiplication gadget. -/
def packWords {d : ℕ} (a b : Fin d → Bool) (c : Fin (2 * d) → Bool) :
    Fin (4 * d) → Bool :=
  fun i => if hi : i.val < d then a ⟨i.val, hi⟩ else
    if hi' : i.val < 2 * d then b ⟨i.val - d, by omega⟩ else
      c ⟨i.val - 2 * d, by omega⟩

@[simp] lemma inputA_pack {d : ℕ} (a b : Fin d → Bool) (c : Fin (2 * d) → Bool) :
    inputA (packWords a b c) = a := by
  funext i
  simp [inputA, packWords, i.isLt]

@[simp] lemma inputB_pack {d : ℕ} (a b : Fin d → Bool) (c : Fin (2 * d) → Bool) :
    inputB (packWords a b c) = b := by
  funext i
  have h1 : ¬d + i.val < d := by omega
  have h2 : d + i.val < 2 * d := by omega
  simp [inputB, packWords, h1, h2]

@[simp] lemma productWord_pack {d : ℕ} (a b : Fin d → Bool) (c : Fin (2 * d) → Bool) :
    productWord (packWords a b c) = c := by
  funext i
  have h1 : ¬2 * d + i.val < d := by omega
  have h2 : ¬2 * d + i.val < 2 * d := by omega
  simp [productWord, packWords, h1, h2]

lemma packWords_eta {d : ℕ} (x : Fin (4 * d) → Bool) :
    packWords (inputA x) (inputB x) (productWord x) = x := by
  funext i
  unfold packWords
  split
  · rfl
  · split
    · unfold inputB
      congr 1
      apply Fin.ext
      dsimp
      omega
    · unfold productWord
      congr 1
      apply Fin.ext
      dsimp
      omega

lemma interface_ext_values {d : ℕ} (x y : Fin (4 * d) → Bool)
    (ha : bitsToNat (inputA x) = bitsToNat (inputA y))
    (hb : bitsToNat (inputB x) = bitsToNat (inputB y))
    (hc : bitsToNat (productWord x) = bitsToNat (productWord y)) : x = y := by
  rw [← packWords_eta x, ← packWords_eta y,
    bitsToNat_injective d ha, bitsToNat_injective d hb,
    bitsToNat_injective (2 * d) hc]

/-- The all-factor-pair relation before output pinning. -/
def MulRelation {d : ℕ} (x : Fin (4 * d) → Bool) : Prop :=
  bitsToNat (inputA x) * bitsToNat (inputB x) = bitsToNat (productWord x)

lemma mulRelation_outputPins {d N : ℕ} (hN : N < 2 ^ (2 * d))
    (x : Fin (4 * d) → Bool) :
    (MulRelation x ∧ MatchesPins (outputPins d N) x) ↔ ProductIs N x := by
  rw [matches_outputPins_iff hN]
  unfold MulRelation ProductIs
  constructor <;> rintro ⟨hm, hc⟩ <;> exact ⟨by simpa only [hc] using hm, hc⟩

theorem output_pinned_parsimonious {d N : ℕ} (hN : N < 2 ^ (2 * d))
    (G : BipartiteMultigraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
    (ext : Fin (4 * d) → Fin G.nE) (hpar : IsParsimonious G T ext MulRelation) :
    IsParsimonious G (pinTensor G T ext (outputPins d N)) ext (ProductIs N) := by
  have h := parsimonious_pinTensor G T ext MulRelation hpar (outputPins d N)
  have hrel : (fun x => MulRelation x ∧ MatchesPins (outputPins d N) x) = ProductIs N := by
    funext x
    exact propext (mulRelation_outputPins hN x)
  rwa [hrel] at h

/-- An interface word for a prescribed factor pair and product. -/
def factorWord (d a b N : ℕ) : Fin (4 * d) → Bool :=
  packWords (natWord d a) (natWord d b) (natWord (2 * d) N)

lemma factorWord_values (d a b N : ℕ) (ha : a < 2 ^ d) (hb : b < 2 ^ d)
    (hN : N < 2 ^ (2 * d)) :
    bitsToNat (inputA (factorWord d a b N)) = a ∧
    bitsToNat (inputB (factorWord d a b N)) = b ∧
    bitsToNat (productWord (factorWord d a b N)) = N := by
  simp [factorWord, bitsToNat_natWord, ha, hb, hN]

lemma trivial_words_spec {d N : ℕ} (hN2 : 2 ≤ N) (hN : N < 2 ^ d) :
    ProductIs N (factorWord d 1 N N) ∧ ProductIs N (factorWord d N 1 N) ∧
      factorWord d 1 N N ≠ factorWord d N 1 N := by
  have h1 : 1 < 2 ^ d := by omega
  have hNN : N < 2 ^ (2 * d) := hN.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hl := factorWord_values d 1 N N h1 hN hNN
  have hr := factorWord_values d N 1 N hN h1 hNN
  refine ⟨⟨by rw [hl.1, hl.2.1, one_mul], hl.2.2⟩,
    ⟨by rw [hr.1, hr.2.1, mul_one], hr.2.2⟩, ?_⟩
  intro heq
  have ha := congrArg (fun x => bitsToNat (inputA x)) heq
  rw [hl.1, hr.1] at ha
  omega

/-- Removing the two trivial factor words is exactly the proper-divisor constraint. -/
theorem nontrivial_product_iff {d N : ℕ} (hN2 : 2 ≤ N) (hN : N < 2 ^ d)
    (x : Fin (4 * d) → Bool) :
    (ProductIs N x ∧ x ≠ factorWord d 1 N N ∧ x ≠ factorWord d N 1 N) ↔
      ProductIs N x ∧ 2 ≤ bitsToNat (inputA x) ∧ bitsToNat (inputA x) < N := by
  have h1 : 1 < 2 ^ d := by omega
  have hNN : N < 2 ^ (2 * d) := hN.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hl := factorWord_values d 1 N N h1 hN hNN
  have hr := factorWord_values d N 1 N hN h1 hNN
  constructor
  · rintro ⟨hx, hxl, hxr⟩
    have ha0 : 0 < bitsToNat (inputA x) := by
      have hm := hx.1
      by_contra h
      have hz : bitsToNat (inputA x) = 0 := by omega
      rw [hz, zero_mul] at hm
      omega
    have hb0 : 0 < bitsToNat (inputB x) := by
      have hm := hx.1
      by_contra h
      have hz : bitsToNat (inputB x) = 0 := by omega
      rw [hz, mul_zero] at hm
      omega
    have ha_le : bitsToNat (inputA x) ≤ N := by
      have hb1 : 1 ≤ bitsToNat (inputB x) := hb0
      have h := Nat.mul_le_mul_left (bitsToNat (inputA x)) hb1
      simpa only [mul_one, hx.1] using h
    have ha1 : bitsToNat (inputA x) ≠ 1 := by
      intro ha
      have hb : bitsToNat (inputB x) = N := by simpa [ha] using hx.1
      exact hxl (interface_ext_values x _ (ha.trans hl.1.symm)
        (hb.trans hl.2.1.symm) (hx.2.trans hl.2.2.symm))
    have haN : bitsToNat (inputA x) ≠ N := by
      intro ha
      have hb : bitsToNat (inputB x) = 1 := by
        have hm := hx.1
        rw [ha] at hm
        nlinarith
      exact hxr (interface_ext_values x _ (ha.trans hr.1.symm)
        (hb.trans hr.2.1.symm) (hx.2.trans hr.2.2.symm))
    exact ⟨hx, by omega, by omega⟩
  · rintro ⟨hx, ha2, haN⟩
    refine ⟨hx, ?_, ?_⟩
    · intro heq
      have ha := congrArg (fun x => bitsToNat (inputA x)) heq
      rw [hl.1] at ha
      omega
    · intro heq
      have ha := congrArg (fun x => bitsToNat (inputA x)) heq
      rw [hr.1] at ha
      omega

/-- A nontrivial product witness yields the divisor required by the machine target. -/
theorem proper_divisor_of_nontrivial_product {d N : ℕ} (hN2 : 2 ≤ N)
    (hN : N < 2 ^ d) (x : Fin (4 * d) → Bool)
    (hx : ProductIs N x ∧ x ≠ factorWord d 1 N N ∧ x ≠ factorWord d N 1 N) :
    2 ≤ bitsToNat (inputA x) ∧ bitsToNat (inputA x) < N ∧
      bitsToNat (inputA x) ∣ N := by
  obtain ⟨hprod, h2, hlt⟩ := (nontrivial_product_iff hN2 hN x).1 hx
  exact ⟨h2, hlt, ⟨bitsToNat (inputB x), hprod.1.symm⟩⟩

/-- Read the exact count from the constant coefficient of a pinned contraction. -/
noncomputable def pinnedContractCount (G : BipartiteMultigraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
    {k : ℕ} (ext : Fin k → Fin G.nE) (P0 : ℕ)
    (pin : Fin k → Option Bool) : ℕ :=
  (truncConstantHom P0 1 (by decide)
    (BTNContract G (fun v α =>
      if pinTensor G T ext pin v α then (1 : TruncPoly P0 1) else 0))).val

/-- This is the exact natural count, not just its residue, when precision exceeds the edge count. -/
theorem pinnedContractCount_eq (G : BipartiteMultigraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
    {k : ℕ} (ext : Fin k → Fin G.nE) (R : (Fin k → Bool) → Prop)
    (hpar : IsParsimonious G T ext R) (P0 : ℕ) (hP0 : G.nE < P0)
    (pin : Fin k → Option Bool) :
    pinnedContractCount G T ext P0 pin = completionCount R pin := by
  classical
  unfold pinnedContractCount
  rw [contract_pin_eq_relation_card G T ext R hpar pin, map_natCast]
  rw [ZMod.val_natCast_of_lt (relation_card_lt_pow G (pinTensor G T ext pin) ext _
    (parsimonious_pinTensor G T ext R hpar pin) P0 hP0)]
  simp only [completionCount, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- A composite input has a witness other than the two trivial factor pairs. -/
theorem exists_nontrivial_product {d N : ℕ} (hN2 : 2 ≤ N) (hN : N < 2 ^ d)
    (hnot : ¬N.Prime) :
    ∃ x : Fin (4 * d) → Bool,
      ProductIs N x ∧ x ≠ factorWord d 1 N N ∧ x ≠ factorWord d N 1 N := by
  have hp : N.minFac.Prime := Nat.minFac_prime (by omega)
  have hp_le : N.minFac ≤ N := Nat.minFac_le (by omega)
  have hp_lt : N.minFac < N :=
    lt_of_le_of_ne hp_le (fun h => hnot (h ▸ hp))
  have hq_le : N / N.minFac ≤ N := Nat.div_le_self _ _
  have hNN : N < 2 ^ (2 * d) := hN.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  let x := factorWord d N.minFac (N / N.minFac) N
  have hx := factorWord_values d N.minFac (N / N.minFac) N (hp_le.trans_lt hN)
    (hq_le.trans_lt hN) hNN
  refine ⟨x, (nontrivial_product_iff hN2 hN x).2 ?_⟩
  refine ⟨⟨?_, hx.2.2⟩, ?_, ?_⟩
  · rw [hx.1, hx.2.1]
    exact Nat.mul_div_cancel' (Nat.minFac_dvd N)
  · rw [hx.1]
    exact hp.two_le
  · rw [hx.1]
    exact hp_lt

/-- Executable divisor-extraction program relative to a natural-valued count oracle. -/
def divisorFromCount (d N : ℕ) (count : (Fin (4 * d) → Option Bool) → ℕ) : ℕ :=
  let oracle := correctedOracle count (factorWord d 1 N N) (factorWord d N 1 N)
  bitsToNat (inputA (searchWord oracle (List.finRange (4 * d)).reverse (fun _ => none)))

/-- The executable wrapper needs only an exact count oracle for output-pinned products. -/
theorem divisorFromCount_spec {d N : ℕ} (hN2 : 2 ≤ N) (hN : N < 2 ^ d)
    (count : (Fin (4 * d) → Option Bool) → ℕ)
    (hcount : ∀ pin, count pin = completionCount (ProductIs N) pin) (hnot : ¬N.Prime) :
    2 ≤ divisorFromCount d N count ∧ divisorFromCount d N count < N ∧
      divisorFromCount d N count ∣ N := by
  obtain ⟨ha, hb, hab⟩ := trivial_words_spec hN2 hN
  obtain ⟨x, hx⟩ := exists_nontrivial_product hN2 hN hnot
  have hsearch := corrected_binary_search_spec (ProductIs N) count hcount
    (factorWord d 1 N N) (factorWord d N 1 N) ha hb hab (fun _ => none)
    ⟨x, hx, by simp [MatchesPins]⟩
  exact proper_divisor_of_nontrivial_product hN2 hN _ hsearch.1

/-- The natural-number divisor extracted by corrected count queries to the original graph. -/
noncomputable def divisorSearch {d : ℕ} (G : BipartiteMultigraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
    (ext : Fin (4 * d) → Fin G.nE) (P0 N : ℕ) : ℕ :=
  let base := pinTensor G T ext (outputPins d N)
  let oracle := correctedOracle (pinnedContractCount G base ext P0)
    (factorWord d 1 N N) (factorWord d N 1 N)
  bitsToNat (inputA (searchWord oracle (List.finRange (4 * d)).reverse (fun _ => none)))

/-- Complete arithmetic/semantic correctness of the BTN-based proper-divisor search. -/
theorem divisorSearch_spec {d N : ℕ} (hN2 : 2 ≤ N) (hN : N < 2 ^ d)
    (G : BipartiteMultigraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
    (ext : Fin (4 * d) → Fin G.nE) (hpar : IsParsimonious G T ext MulRelation)
    (P0 : ℕ) (hP0 : G.nE < P0) (hnot : ¬N.Prime) :
    2 ≤ divisorSearch G T ext P0 N ∧ divisorSearch G T ext P0 N < N ∧
      divisorSearch G T ext P0 N ∣ N := by
  have hNN : N < 2 ^ (2 * d) := hN.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  let base := pinTensor G T ext (outputPins d N)
  have hbase : IsParsimonious G base ext (ProductIs N) :=
    output_pinned_parsimonious hNN G T ext hpar
  have hcount : ∀ pin, pinnedContractCount G base ext P0 pin = completionCount (ProductIs N) pin :=
    pinnedContractCount_eq G base ext (ProductIs N) hbase P0 hP0
  obtain ⟨ha, hb, hab⟩ := trivial_words_spec hN2 hN
  obtain ⟨x, hx⟩ := exists_nontrivial_product hN2 hN hnot
  have hsearch := corrected_binary_search_spec (ProductIs N) _ hcount
    (factorWord d 1 N N) (factorWord d N 1 N) ha hb hab (fun _ => none)
    ⟨x, hx, by simp [MatchesPins]⟩
  exact proper_divisor_of_nontrivial_product hN2 hN _ hsearch.1

/-- Every oracle call uses the same graph, and there are at most `4*d` calls. -/
theorem divisorSearch_query_bound {d : ℕ} (G : BipartiteMultigraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
    (ext : Fin (4 * d) → Fin G.nE) (P0 N : ℕ) :
    let base := pinTensor G T ext (outputPins d N)
    let oracle := correctedOracle (pinnedContractCount G base ext P0)
      (factorWord d 1 N N) (factorWord d N 1 N)
    completionQueryCount oracle (List.finRange (4 * d)).reverse (fun _ => none) ≤ 4 * d :=
  binary_search_query_bound _ _

lemma truncPolyOfCoeffs_one_eq_natCast (P0 c : ℕ) :
    truncPolyOfCoeffs P0 1 (fun _ => c) = (c : TruncPoly P0 1) := by
  unfold truncPolyOfCoeffs
  rw [Fin.sum_univ_one]
  simp only [Fin.val_zero, Polynomial.monomial_zero_left, map_natCast]

/-- A length-one polynomial output is precisely a framed singleton natural number. -/
theorem encodesTruncPoly_one_iff (P0 : ℕ) (w : List Bool) (x : TruncPoly P0 1) :
    EncodesTruncPoly P0 1 w x ↔
      ∃ c : ℕ, c < 2 ^ P0 ∧ w = encodeNatListBin [c] ∧ x = (c : TruncPoly P0 1) := by
  constructor
  · rintro ⟨c, hc, hw, hx⟩
    have heq : c = (fun _ => c 0) := funext fun i => congrArg c (Subsingleton.elim _ _)
    refine ⟨c 0, hc 0, ?_, ?_⟩
    · simpa only [List.ofFn_succ, List.ofFn_zero] using hw
    · rw [hx]
      exact (congrArg (truncPolyOfCoeffs P0 1) heq).trans
        (truncPolyOfCoeffs_one_eq_natCast P0 (c 0))
  · rintro ⟨c, hc, hw, hx⟩
    refine ⟨fun _ => c, fun _ => hc, ?_, ?_⟩
    · simpa only [List.ofFn_const, List.replicate_one] using hw
    · rw [hx, truncPolyOfCoeffs_one_eq_natCast]

/-- The contraction machine's actual encoded word contains the exact completion count. -/
theorem encoded_pinned_count (G : BipartiteMultigraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
    {k : ℕ} (ext : Fin k → Fin G.nE) (R : (Fin k → Bool) → Prop)
    (hpar : IsParsimonious G T ext R) (P0 : ℕ) (hP0 : G.nE < P0)
    (pin : Fin k → Option Bool) (w : List Bool)
    (hw : EncodesTruncPoly P0 1 w
      (BTNContract G (fun v α => if pinTensor G T ext pin v α
        then (1 : TruncPoly P0 1) else 0))) :
    w = encodeNatListBin [completionCount R pin] := by
  obtain ⟨c, hc, hwc, hpoly⟩ := (encodesTruncPoly_one_iff P0 w _).1 hw
  have hread : pinnedContractCount G T ext P0 pin = c := by
    unfold pinnedContractCount
    rw [hpoly, map_natCast, ZMod.val_natCast_of_lt hc]
  rw [pinnedContractCount_eq G T ext R hpar P0 hP0 pin] at hread
  exact hwc.trans (congrArg (fun n => encodeNatListBin [n]) hread.symm)

end w5_M6DivisorConstraints
end DetDLP


