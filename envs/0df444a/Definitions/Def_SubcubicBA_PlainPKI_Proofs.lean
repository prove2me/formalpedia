-- Prove2me | Definitions.Def_SubcubicBA_PlainPKI_Proofs
-- name    : SubcubicBA_PlainPKI_Proofs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T15:43:06.679254+00:00
-- url     : https://prove2.me/theorems/fd5bf071-78c1-4141-9385-721899e8c597
-- title:
--   Votes, accusations and proofs (Definition 10), ComputeProof, the specifications of proof creation and validated dispersal, and the group-merging invariant
-- statement:
--   Combinatorial and specification-level objects of §§6, 7 and 11.
--
--   1. **Proofs (Definition 10).** A vote $(p,v)$ says party $p$ voted $v\in\{0,1,\bot\}$ ($\bot$ is $2$), and an accusation $(a,c)$ says party $a$ accused $c$. Sets $V$ of votes and $A$ of accusations form a proof for $b\in\{0,1\}$ when every vote is for $b$ or $\bot$; voters are distinct; the voters and the parties of the accusations (accuser and accused) are pairwise disjoint; there is at least one vote; $|V|+|A|=t+1$; and all parties are among $0,\dots,n-1$.
--   2. **Accuracy (p. 12).** Voting accuracy: an honest party votes $v\in\{0,1\}$ only if its input is $v$, and votes $\bot$ only if not all honest inputs are equal. Accusation accuracy: an honest party accuses only byzantine parties.
--   3. **ComputeProof (p. 19).** $Q$ is the set of parties with a vote for $b$ or $\bot$; $E$ is the set of accusations disjoint from $Q$; a matching is a set of accusations with pairwise disjoint party sets.
--   4. **Proofs as messages.** A proof message is a list of items $(\mathrm{Vote}(p,v),\sigma)$ and $(\mathrm{Accuse}(a,c),\sigma)$, each signed by $p$ resp. $a$ in session $s$, whose data form a proof. An honest party can check this with shapes and signature tests (`Obs.ProofFor`), and `IsProofTerm s n t b x` applies the check to a term.
--   5. **Definition 8 (`SolvesPC`).** With binary inputs, every honest party outputs $m$ or $\bot$ by the round bound; a non-$\bot$ honest output is a proof for $0$ or $1$; at least $n/10$ honest parties do not output $\bot$.
--   6. **Definition 5 (`ProofSound`).** If all honest inputs are $1-v$, no proof for $v$ in the protocol's session is derivable with the adversary's capabilities from the auxiliary knowledge and the messages sent.
--   7. **Definition 9 (`SolvesVD`).** For a validity function: if every honest input is $\bot$ or valid and at least $n/10$ honest inputs are valid, every honest party outputs a list of messages by the round bound, all output messages are valid, and some valid message is in every honest output. `valWBA` is WeakBA's validity function: a proof for $0$ or $1$ with the signatures of the sibling proof-creation instance.
--   8. **Group merging (§11.1).** The invariant of a group $G$ with tuple $(h,H)$: $H\subseteq G$, $h$ is valid, honest members of $H$ know the value of $h$, and at least $(|G|-|H|)/2$ parties of $G\setminus H$ are byzantine. `MergeResult` lists the outputs of MergeGroups over all choices of $K'$ and $H_1'$.
--
--   **Formalization Note** "Votes for $b$ or $\bot$" in ComputeProof are counted per party, since a proof needs distinct voters. Accumulators and knowledge are abstract in the merging invariant.
-- source:
--   Marc Dufay, Roger Wattenhofer, Optimal Subcubic Byzantine Agreement with Plain PKI, STOC 2027 submission #101 (October 2026), §6 Definitions 8, 9 (p. 11); §5 Definition 5 (p. 10); §7.1 Definition 10 (pp. 12–13); §7.5 ComputeProof (p. 19); §11.1 (pp. 27–28)

import Mathlib
import Definitions.Def_SubcubicBA_PlainPKI_Model

set_option autoImplicit false

namespace SubcubicBA.PlainPKI

/-! # Votes, accusations and proofs (§7.1, pp. 12–13), ComputeProof (§7.5, p. 19),
the proof-creation and validated-dispersal specifications (§6, Definitions 5, 8, 9, pp. 10–11),
and the group-merging invariant (§11.1, pp. 27–28).

Parties are `0, …, n-1`; a vote value is `0`, `1` or `2` (`2` = `⊥`). A vote is a pair
`(p, v)`: party `p` votes `v`. An accusation is a pair `(a, c)`: party `a` accuses party `c`. -/

/-- Definition 10 on sets: `V` (votes) and `A` (accusations) form a proof for `b`: every vote is
for `b` or `⊥`; voters are distinct; voters and the parties of the accusations (accuser and
accused) are pairwise disjoint; there is at least one vote and `|V| + |A| = t + 1`; all parties
are among `0, …, n-1`. -/
def IsProofSet (n t b : ℕ) (V A : Finset (ℕ × ℕ)) : Prop :=
  (∀ x ∈ V, x.2 = b ∨ x.2 = 2) ∧
  (∀ x ∈ V, ∀ x' ∈ V, x.1 = x'.1 → x = x') ∧
  (∀ x ∈ V, ∀ y ∈ A, x.1 ≠ y.1 ∧ x.1 ≠ y.2) ∧
  (∀ y ∈ A, ∀ y' ∈ A, y ≠ y' → Disjoint ({y.1, y.2} : Finset ℕ) {y'.1, y'.2}) ∧
  1 ≤ V.card ∧ V.card + A.card = t + 1 ∧
  (∀ x ∈ V, x.1 < n) ∧ (∀ y ∈ A, y.1 < n ∧ y.2 < n)

/-- Definition 10 on lists of items (no item repeated). -/
def IsProofData (n t b : ℕ) (votes accs : List (ℕ × ℕ)) : Prop :=
  votes.Nodup ∧ accs.Nodup ∧ IsProofSet n t b votes.toFinset accs.toFinset

/-- Voting accuracy (p. 12) for byzantine set `Bz`, honest inputs `input` and the relation
`voted p v` (party `p` signed a vote for `v`): an honest party votes `v ∈ {0,1}` only if its
input is `v`, and votes `⊥` only if not all honest parties have the same input. -/
def VotingAccurate (n : ℕ) (Bz : Finset ℕ) (input : ℕ → ℕ) (voted : ℕ → ℕ → Prop) : Prop :=
  ∀ p < n, p ∉ Bz → ∀ v, voted p v →
    (v ≤ 1 → v = input p) ∧ (v = 2 → ∃ i < n, ∃ j < n, i ∉ Bz ∧ j ∉ Bz ∧ input i ≠ input j)

/-- Accusation accuracy (p. 12): if an honest party accuses `c`, then `c` is byzantine. -/
def AccusationAccurate (n : ℕ) (Bz : Finset ℕ) (accused : ℕ → ℕ → Prop) : Prop :=
  ∀ p < n, p ∉ Bz → ∀ c, accused p c → c ∈ Bz

/-! ## ComputeProof (p. 19) -/

/-- `Q`: the parties having a vote for `b` or `⊥`. -/
def proofQ (b : ℕ) (V : Finset (ℕ × ℕ)) : Finset ℕ :=
  (V.filter fun x => x.2 = b ∨ x.2 = 2).image Prod.fst

/-- `E`: the accusations disjoint from `Q` (neither accuser nor accused in `Q`). -/
def proofE (b : ℕ) (V A : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  A.filter fun y => y.1 ∉ proofQ b V ∧ y.2 ∉ proofQ b V

/-- A matching of accusations: pairwise disjoint party sets. -/
def IsAccMatching (M : Finset (ℕ × ℕ)) : Prop :=
  ∀ y ∈ M, ∀ y' ∈ M, y ≠ y' → Disjoint ({y.1, y.2} : Finset ℕ) {y'.1, y'.2}

/-- `M` is a maximum matching of `E`. -/
def IsMaxAccMatching (E M : Finset (ℕ × ℕ)) : Prop :=
  M ⊆ E ∧ IsAccMatching M ∧ ∀ M' ⊆ E, IsAccMatching M' → M'.card ≤ M.card

/-! ## Proofs as terms -/

/-- The signed content of a vote `Vote(p, v)`. -/
def voteData (p v : ℕ) : Term := .pair (.nat 0) (.pair (.nat p) (.nat v))

/-- The signed content of an accusation `Accuse(a, c)`. -/
def accData (a c : ℕ) : Term := .pair (.nat 1) (.pair (.nat a) (.nat c))

/-- `drop k` of a list expression. -/
def Expr.drop (e : Expr) : ℕ → Expr
  | 0 => e
  | k + 1 => Expr.drop (.snd e) k

/-- The `k`-th element of a list expression. -/
def Expr.nth (e : Expr) (k : ℕ) : Expr := .fst (e.drop k)

/-- The value of `e` is a list (in the `Term.ofList` encoding) of length `L`. -/
def Obs.IsList (o : Obs) (e : Expr) (L : ℕ) : Prop :=
  o.shape (e.drop L) = some (.nat 0) ∧ ∀ k < L, ∃ a b, o.shape (e.drop k) = some (.pair a b)

/-- The value of `e` is the item `(Vote(p, v), σ)` with `σ` party `p`'s signature on `Vote(p,v)`
in session `sess`. -/
def Obs.VoteItem (o : Obs) (sess : ℕ) (e : Expr) (p v : ℕ) : Prop :=
  o.shape e = some (.pair (voteData p v).blind .tok) ∧
    o.test (.isSig p sess (.fst e) (.snd e)) = true

/-- The value of `e` is the item `(Accuse(a, c), σ)` with `σ` party `a`'s signature on it in
session `sess`. -/
def Obs.AccItem (o : Obs) (sess : ℕ) (e : Expr) (a c : ℕ) : Prop :=
  o.shape e = some (.pair (accData a c).blind .tok) ∧
    o.test (.isSig a sess (.fst e) (.snd e)) = true

/-- Proof items. -/
inductive Item where
  | vote : ℕ → ℕ → Item
  | acc : ℕ → ℕ → Item

def Item.voteOf : Item → Option (ℕ × ℕ)
  | .vote p v => some (p, v)
  | .acc _ _ => none

def Item.accOf : Item → Option (ℕ × ℕ)
  | .vote _ _ => none
  | .acc a c => some (a, c)

def Obs.ItemAt (o : Obs) (sess : ℕ) (e : Expr) : Item → Prop
  | .vote p v => o.VoteItem sess e p v
  | .acc a c => o.AccItem sess e a c

/-- Through observation `o`, the value of `e` is a proof for `b` (Definition 10) in session
`sess`: a list of signed votes and accusations whose data satisfy Definition 10. This is
checkable by an honest party (shapes and signature tests only). -/
def Obs.ProofFor (o : Obs) (sess n t : ℕ) (e : Expr) (b : ℕ) : Prop :=
  ∃ items : List Item, o.IsList e items.length ∧
    (∀ k (hk : k < items.length), o.ItemAt sess (e.nth k) (items.get ⟨k, hk⟩)) ∧
    IsProofData n t b (items.filterMap Item.voteOf) (items.filterMap Item.accOf)

/-- The observation of a single term (as the input of an otherwise empty environment). -/
def termObs (x : Term) : Obs := (⟨0, 0, x, fun _ _ => none⟩ : Env).obs 0

/-- The term `x` is a proof for `b` (Definition 10) with signatures of session `sess`. -/
def IsProofTerm (sess n t b : ℕ) (x : Term) : Prop := (termObs x).ProofFor sess n t .input b

/-! ## Specifications of the two subprotocols of WeakBA (§6) -/

variable {n : ℕ}

/-- Every term sent in rounds `≤ r` by an honest party, or by a corrupted party to an honest one. -/
def visibleMsgs (s : Setup n) (tr : Trace n) (r : ℕ) : Set Term :=
  {m | ∃ r' ≤ r, ∃ i j : Fin n, (i ∉ s.F ∨ j ∉ s.F) ∧ tr r' i j = some m}

open Classical in
/-- Definition 8, proof creation (binary inputs; output `opt m`, `⊥ = opt none`):
termination by `T`; certifiability (a non-`⊥` output is a proof for `0` or `1` in the protocol's
session); partial decision (at least `n/10` honest parties do not output `⊥`). -/
def SolvesPC (P : Protocol) (T : ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∀ (n sess t κ : ℕ) (b : Fin n → Bool) (F : Finset (Fin n)) (aux : Set Term) (tr : Trace n),
    2 * t < n → F.card ≤ t →
    FreshAux (baSetup sess t κ b F) aux → IsRun P (baSetup sess t κ b F) aux tr →
      (∀ j : Fin n, j ∉ F → ∃ r ≤ T n t κ, ∃ m : Option Term,
          OutputsAt P (baSetup sess t κ b F) tr j r (Term.opt m)) ∧
      (∀ j : Fin n, j ∉ F → ∀ m : Term, Outputs P (baSetup sess t κ b F) tr j (Term.opt (some m)) →
          ∃ c ≤ 1, IsProofTerm sess n t c m) ∧
      (n : ℝ) ≤ 10 * ((Finset.univ.filter fun j : Fin n =>
          j ∉ F ∧ ∃ m : Term, Outputs P (baSetup sess t κ b F) tr j (Term.opt (some m))).card : ℝ)

/-- Definition 5 for the proofs of protocol `P` ("relevant to the inputs", Definition 8): if all
honest inputs are `1 - v`, no proof for `v` in `P`'s session is derivable with the adversary's
capabilities from the auxiliary knowledge and all terms sent so far (other than among corrupted
parties). -/
def ProofSound (P : Protocol) : Prop :=
  ∀ (n sess t κ : ℕ) (b : Fin n → Bool) (F : Finset (Fin n)) (aux : Set Term) (tr : Trace n),
    2 * t < n → F.card ≤ t →
    FreshAux (baSetup sess t κ b F) aux → IsRun P (baSetup sess t κ b F) aux tr →
      ∀ v ≤ 1, (∀ j : Fin n, j ∉ F → Term.bit (b j) = .nat (1 - v)) →
        ∀ (r : ℕ) (x : Term), IsProofTerm sess n t v x →
          ¬ Derivable (advCap (baSetup sess t κ b F))
              (aux ∪ visibleMsgs (baSetup sess t κ b F) tr r) x

open Classical in
/-- Definition 9, validated dispersal with external validity `val sess n t` (inputs `opt m`,
`⊥ = opt none`; output a list of messages): if every honest input is `⊥` or valid and at least
`n/10` honest inputs are not `⊥`, then termination by `T` (output a list), validity (every output
message is valid) and coverage (one valid message is in every honest output). -/
def SolvesVD (P : Protocol) (val : ℕ → ℕ → ℕ → Term → Prop) (T : ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∀ (n sess t κ : ℕ) (inp : Fin n → Term) (F : Finset (Fin n)) (aux : Set Term) (tr : Trace n),
    2 * t < n → F.card ≤ t →
    (∀ j : Fin n, j ∉ F → inp j = Term.opt none ∨ ∃ m, inp j = Term.opt (some m) ∧ val sess n t m) →
    (n : ℝ) ≤ 10 * ((Finset.univ.filter fun j : Fin n => j ∉ F ∧ inp j ≠ Term.opt none).card : ℝ) →
    FreshAux (⟨sess, t, κ, inp, F⟩ : Setup n) aux → IsRun P ⟨sess, t, κ, inp, F⟩ aux tr →
      (∀ j : Fin n, j ∉ F → ∃ r ≤ T n t κ, ∃ L : List Term,
          OutputsAt P ⟨sess, t, κ, inp, F⟩ tr j r (Term.ofList L)) ∧
      (∀ j : Fin n, j ∉ F → ∀ L : List Term, Outputs P ⟨sess, t, κ, inp, F⟩ tr j (Term.ofList L) →
          ∀ m ∈ L, val sess n t m) ∧
      (∃ m, val sess n t m ∧ ∀ j : Fin n, j ∉ F → ∀ L : List Term,
          Outputs P ⟨sess, t, κ, inp, F⟩ tr j (Term.ofList L) → m ∈ L)

/-- The validity function of WeakBA's validated dispersal (p. 11): in the dispersal instance
`childSession s 1` of a WeakBA instance `s`, a message is valid iff it is a proof for `0` or `1`
with the signatures of the proof-creation instance `childSession s 0`. -/
def valWBA (sess n t : ℕ) (m : Term) : Prop :=
  ∃ s, sess = childSession s 1 ∧ ∃ c ≤ 1, IsProofTerm (childSession s 0) n t c m

/-! ## Group merging (§11.1) -/

/-- The invariant of a group `G` with tuple `(h, H)` (p. 27): `H ⊆ G`, `h` is (the accumulator
of) a valid input, every honest party of `H` knows the value associated with `h`, and at least
`(|G| - |H|)/2` parties of `G \ H` are byzantine. -/
def MergeInv {α : Type} (Bz : Finset ℕ) (valid : α → Prop) (knows : ℕ → α → Prop)
    (G : Finset ℕ) (h : α) (H : Finset ℕ) : Prop :=
  H ⊆ G ∧ valid h ∧ (∀ p ∈ H, p ∉ Bz → knows p h) ∧
    (G \ H).card ≤ 2 * ((G \ H) ∩ Bz).card

/-- The possible results of MergeGroups (p. 28) on `(h₁, H₁)`, `(h₂, H₂)` when `K ⊆ H₂` is the
set of parties of `H₂` that broadcast `0`, over all choices of `K'` and `H₁'`. -/
def MergeResult {α : Type} (h₁ h₂ : α) (H₁ H₂ K : Finset ℕ) (out : α × Finset ℕ) : Prop :=
  (H₁ = ∅ ∧ out = (h₂, H₂)) ∨
  (H₁ ≠ ∅ ∧ H₁.card ≤ K.card ∧ ∃ K' ⊆ K, K'.card = H₁.card ∧ out = (h₂, H₂ \ K')) ∨
  (H₁ ≠ ∅ ∧ K.card < H₁.card ∧ ∃ H₁' ⊆ H₁, H₁'.card = K.card ∧ out = (h₁, (H₁ \ H₁') ∪ (H₂ \ K)))

end SubcubicBA.PlainPKI


