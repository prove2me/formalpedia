-- Prove2me | Definitions.Def_TetraOT_Supplement_multiRun
-- name    : TetraOT_Supplement_multiRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:39:45.44781+00:00
-- url     : https://prove2.me/theorems/5e698bf9-73e2-49d5-8474-4c0078ac7899
-- title:
--   The $(n_A, n_B)$-Multi Tetrahedral Protocol on $S_{4m}$ (Fig. 31)
-- statement:
--   Fix $m$ and hand sizes $n_A + n_B \le 4m$. The deck is $\{0,\dots,4m-1\}$ and is shuffled by a permutation $\rho \in S_{4m}$. Following Definition 2.2, Alice receives the cards at positions $0,\dots,n_A-1$, Bob those at positions $n_A,\dots,n_A+n_B-1$, and the rest are discarded. Card $x$ has **rank** $x \bmod m$ and **suit** $x / m \in \{0,1,2,3\}$, so each rank consists of four cards, one of each suit.
--
--   For a rank $r$, let $N_A(\rho,r)$ and $N_B(\rho,r)$ be the numbers of rank-$r$ cards held by Alice and Bob, $S_A(\rho,k)=\{r : N_A(\rho,r)=k\}$ and $S_B(\rho,k)=\{r : N_B(\rho,r)=k\}$. The good set is
--   $$G(\rho) = \big(S_A(\rho,2)\cap S_B(\rho,1)\big)\cup\big(S_A(\rho,1)\cap S_B(\rho,2)\big),\qquad g(\rho)=|G(\rho)|.$$
--   Alice announces $S_A(\rho,2), S_A(\rho,1)$ and Bob announces $S_B(\rho,1), S_B(\rho,2)$. On each $r\in G(\rho)$ they run the Tetrahedral Protocol on the suits of the rank-$r$ cards: the party holding two rank-$r$ cards is the sender, applies Alice's table $A$ (Fig. 2) to the suits of its two cards in position order, outputs $(m_0,m_1)$ and announces $M_r$; the other party applies Bob's table $B$ (Fig. 3) to $M_r$ and the suit of its card and outputs $(s,m_s)$.
--
--   The definition provides the per-rank run, the **role map** (Alice sender, Bob sender, or $r\notin G(\rho)$), $g(\rho)$, the public transcript (the four announced sets and the messages $M_r$), each party's view (its whole ordered hand and the whole transcript), each party's output (the role map and its result at every rank), and the uniform law on $S_{4m}$.
--
--   **Formalization Note** The identification of the four cards of a rank with $\{0,1,2,3\}$ is by suit $x/m$ (the paper assigns suits arbitrarily). Ranks where Bob holds two cards and Alice one (the "$(1,2;1)$" ranks) are part of $G(\rho)$, as on p.12.
-- source:
--   Beaver, Correlated Group Interactions: Founding Cryptography on S4 and Sn, STOC 2027 submission (preprint, sha256 3dc88c598213707cd4cd52311a9b058999deef19d5aa9eed05208ba8092d65b7), §10, Fig. 31, pp.11–12; §10.4, p.13; Definition 2.2, p.2 (p. = PDF page; the PDF has no printed page numbers)

import Mathlib
import Definitions.Def_TetraOT_Msg
import Definitions.Def_TetraOT_aliceTable
import Definitions.Def_TetraOT_bobTable

set_option autoImplicit false

namespace TetraOT.Supplement

open TetraOT

/-- The rank of card `x` of the deck `{0, …, 4m − 1}`: `x mod m` ("let the rank of element i be defined as
i mod m", §10, p.11). -/
def rank {m : ℕ} (x : Fin (4 * m)) : Fin m :=
  ⟨x.val % m, Nat.mod_lt _ (by have := x.isLt; omega)⟩

/-- The suit of card `x`: `x / m ∈ {0, 1, 2, 3}` (suits ♣ = 0, ♦ = 1, ♥ = 2, ♠ = 3, §10, p.11). The card
of rank `r` and suit `σ` is `σ·m + r`, so the suit is the fixed identification of the four cards of
rank `r` with `{0, 1, 2, 3}` ("mapped in the natural isomorphic way from {0, 1, 2, 3} to the four cards
of rank r", proof of Theorem 10.1, pp.12–13). -/
def suit {m : ℕ} (x : Fin (4 * m)) : Fin 4 :=
  ⟨x.val / m, Nat.div_lt_of_lt_mul (by have := x.isLt; omega)⟩

/-- Alice's ordered hand: the cards `ρ(0), …, ρ(nA − 1)` at the first `nA` positions. -/
def aliceHand (m nA nB : ℕ) (h : nA + nB ≤ 4 * m) (ρ : Equiv.Perm (Fin (4 * m))) :
    Fin nA → Fin (4 * m) :=
  fun i => ρ ⟨i.val, by have := i.isLt; omega⟩

/-- Bob's ordered hand: the cards `ρ(nA), …, ρ(nA + nB − 1)` at the next `nB` positions. The cards at
the remaining positions go to Rob (the discard). -/
def bobHand (m nA nB : ℕ) (h : nA + nB ≤ 4 * m) (ρ : Equiv.Perm (Fin (4 * m))) :
    Fin nB → Fin (4 * m) :=
  fun j => ρ ⟨nA + j.val, by have := j.isLt; omega⟩

/-- `H_A(ρ, r)`: Alice's cards of rank `r`, listed in the order of her positions. Its length is
`N_A(ρ, r)` (§10, p.12). -/
def aliceRankCards (m nA nB : ℕ) (h : nA + nB ≤ 4 * m) (ρ : Equiv.Perm (Fin (4 * m)))
    (r : Fin m) : List (Fin (4 * m)) :=
  (List.ofFn (aliceHand m nA nB h ρ)).filter (fun x => decide (rank x = r))

/-- `H_B(ρ, r)`: Bob's cards of rank `r`, listed in the order of his positions. -/
def bobRankCards (m nA nB : ℕ) (h : nA + nB ≤ 4 * m) (ρ : Equiv.Perm (Fin (4 * m)))
    (r : Fin m) : List (Fin (4 * m)) :=
  (List.ofFn (bobHand m nA nB h ρ)).filter (fun x => decide (rank x = r))

/-- `N_A(ρ, r)`, the number of rank-`r` cards Alice holds. -/
def countA (m nA nB : ℕ) (h : nA + nB ≤ 4 * m) (ρ : Equiv.Perm (Fin (4 * m))) (r : Fin m) : ℕ :=
  (aliceRankCards m nA nB h ρ r).length

/-- `N_B(ρ, r)`, the number of rank-`r` cards Bob holds. -/
def countB (m nA nB : ℕ) (h : nA + nB ≤ 4 * m) (ρ : Equiv.Perm (Fin (4 * m))) (r : Fin m) : ℕ :=
  (bobRankCards m nA nB h ρ r).length

/-- `S_A(ρ, k) = {r : N_A(ρ, r) = k}`. -/
def setA (m nA nB : ℕ) (h : nA + nB ≤ 4 * m) (ρ : Equiv.Perm (Fin (4 * m))) (k : ℕ) :
    Finset (Fin m) :=
  Finset.univ.filter (fun r => countA m nA nB h ρ r = k)

/-- `S_B(ρ, k) = {r : N_B(ρ, r) = k}`. -/
def setB (m nA nB : ℕ) (h : nA + nB ≤ 4 * m) (ρ : Equiv.Perm (Fin (4 * m))) (k : ℕ) :
    Finset (Fin m) :=
  Finset.univ.filter (fun r => countB m nA nB h ρ r = k)

/-- The single-instance Tetrahedral Protocol on one rank, given the sender's two rank-`r` cards and the
receiver's rank-`r` card as lists in position order. If one party holds exactly two cards of the rank
and the other exactly one, the two-card party is the sender: with `σ₀, σ₁` the suits of its two cards in
position order and `σ₂` the suit of the other party's card, it computes `(M, m₀m₁) = A(σ₀, σ₁)` (Fig. 2),
sends `M`, and the receiver computes `B(M, σ₂)` (Fig. 3). The result is
`some (role, M, (m₀, m₁), (s, m_s))` with `role = true` if Alice is the sender (a `(2, 1; 1)` rank) and
`role = false` if Bob is (a `(1, 2; 1)` rank); otherwise `none`. -/
def rankInstance {m : ℕ} (A B : List (Fin (4 * m))) :
    Option (Bool × Msg × (Bool × Bool) × (Bool × Bool)) :=
  match A, B with
  | [x, y], [z] =>
      some (true, (aliceTable (suit x) (suit y)).1, (aliceTable (suit x) (suit y)).2,
        bobTable (aliceTable (suit x) (suit y)).1 (suit z))
  | [z], [x, y] =>
      some (false, (aliceTable (suit x) (suit y)).1, (aliceTable (suit x) (suit y)).2,
        bobTable (aliceTable (suit x) (suit y)).1 (suit z))
  | _, _ => none

/-- **The (nA, nB)-Multi Tetrahedral Protocol** (Beaver, *Correlated Group Interactions: Founding Cryptography on S4 and Sn*, STOC 2027 submission (held preprint, sha256 3dc88c59…92d65b7), §10, Fig. 31, pp.11–12, and §10.4, p.13;
p. = PDF page, the PDF has no printed page numbers). The deck is `{0, …, n − 1}` with `n = 4m`, shuffled
by `ρ ∈ S_n`. Alice holds the cards at positions `0, …, nA − 1` and Bob those at positions
`nA, …, nA + nB − 1`; the rest go to Rob (the discard). Card `x` has rank `x mod m` and suit `x / m`.
Alice announces `S_A(ρ, 2), S_A(ρ, 1)` and Bob announces `S_B(ρ, 1), S_B(ρ, 2)`, from which the good set
`G(ρ) = (S_A(ρ, 2) ∩ S_B(ρ, 1)) ∪ (S_A(ρ, 1) ∩ S_B(ρ, 2))` is common knowledge; they then run the single
Tetrahedral Protocol on every `r ∈ G(ρ)` (Fig. 31), with the two-card party as Alice of Fig. 1 on the
suits of its rank-`r` cards in position order, and the one-card party as Bob on the suit of its card.

`multiRun m nA nB h ρ r` is the run at rank `r` (`rankInstance`): `some (role, M_r, (m₀, m₁), (s, m_s))`
for `r ∈ G(ρ)` and `none` otherwise.

**Formalization Note.** `ρ : Equiv.Perm (Fin (4 * m))`, `ρ i` the card at position `i`. The hypothesis
`h : nA + nB ≤ 4 * m` says the two hands fit in the deck. The (1, 2; 1) ranks (`S_A(ρ, 1) ∩ S_B(ρ, 2)`),
where Bob is the sender, are part of `G(ρ)` as on p.12. The identification of the four cards of a rank
with `{0, 1, 2, 3}` is by suit `x / m`. -/
def multiRun (m nA nB : ℕ) (h : nA + nB ≤ 4 * m) (ρ : Equiv.Perm (Fin (4 * m))) (r : Fin m) :
    Option (Bool × Msg × (Bool × Bool) × (Bool × Bool)) :=
  rankInstance (aliceRankCards m nA nB h ρ r) (bobRankCards m nA nB h ρ r)

/-- The role map, part of both outputs: `some true` if `r ∈ S_A(ρ, 2) ∩ S_B(ρ, 1)` (Alice sends),
`some false` if `r ∈ S_A(ρ, 1) ∩ S_B(ρ, 2)` (Bob sends), `none` if `r ∉ G(ρ)`. -/
def roleMap (m nA nB : ℕ) (h : nA + nB ≤ 4 * m) (ρ : Equiv.Perm (Fin (4 * m))) :
    Fin m → Option Bool :=
  fun r => (multiRun m nA nB h ρ r).map (fun p => p.1)

/-- `g(ρ) = |G(ρ)|`, the number of ranks on which a ½ROT is produced (§10, p.12). -/
def goodCount (m nA nB : ℕ) (h : nA + nB ≤ 4 * m) (ρ : Equiv.Perm (Fin (4 * m))) : ℕ :=
  (Finset.univ.filter (fun r => (roleMap m nA nB h ρ r).isSome)).card

/-- The public transcript of Fig. 31: Alice's announcement `(S_A(ρ, 2), S_A(ρ, 1))`, Bob's announcement
`(S_B(ρ, 1), S_B(ρ, 2))`, and the message `M_r` sent by the sender of each rank `r ∈ G(ρ)` (`none` for
`r ∉ G(ρ)`). -/
def multiTranscript (m nA nB : ℕ) (h : nA + nB ≤ 4 * m) (ρ : Equiv.Perm (Fin (4 * m))) :
    (Finset (Fin m) × Finset (Fin m)) × (Finset (Fin m) × Finset (Fin m)) × (Fin m → Option Msg) :=
  ((setA m nA nB h ρ 2, setA m nA nB h ρ 1), (setB m nA nB h ρ 1, setB m nA nB h ρ 2),
    fun r => (multiRun m nA nB h ρ r).map (fun p => p.2.1))

/-- Alice's view: her whole ordered hand and the whole public transcript. -/
def multiViewA (m nA nB : ℕ) (h : nA + nB ≤ 4 * m) (ρ : Equiv.Perm (Fin (4 * m))) :
    (Fin nA → Fin (4 * m)) ×
      ((Finset (Fin m) × Finset (Fin m)) × (Finset (Fin m) × Finset (Fin m)) × (Fin m → Option Msg)) :=
  (aliceHand m nA nB h ρ, multiTranscript m nA nB h ρ)

/-- Bob's view: his whole ordered hand and the whole public transcript. -/
def multiViewB (m nA nB : ℕ) (h : nA + nB ≤ 4 * m) (ρ : Equiv.Perm (Fin (4 * m))) :
    (Fin nB → Fin (4 * m)) ×
      ((Finset (Fin m) × Finset (Fin m)) × (Finset (Fin m) × Finset (Fin m)) × (Fin m → Option Msg)) :=
  (bobHand m nA nB h ρ, multiTranscript m nA nB h ρ)

/-- Alice's output ("Out: g(ρ), {P_A(ρ, r) | r ∈ G(ρ)}", Fig. 31): the role map (which determines
`G(ρ)` and `g(ρ)`) and her result at each rank: `(m₀, m₁)` where she is the sender, `(s, m_s)` where she
is the receiver, `none` off `G(ρ)`. -/
def multiAliceOut (m nA nB : ℕ) (h : nA + nB ≤ 4 * m) (ρ : Equiv.Perm (Fin (4 * m))) :
    (Fin m → Option Bool) × (Fin m → Option (Bool × Bool)) :=
  (roleMap m nA nB h ρ,
    fun r => (multiRun m nA nB h ρ r).map (fun p => if p.1 then p.2.2.1 else p.2.2.2))

/-- Bob's output ("Out: g(ρ), {P_B(ρ, r) | r ∈ G(ρ)}", Fig. 31): the role map and his result at each
rank: `(s, m_s)` where he is the receiver, `(m₀, m₁)` where he is the sender, `none` off `G(ρ)`. -/
def multiBobOut (m nA nB : ℕ) (h : nA + nB ≤ 4 * m) (ρ : Equiv.Perm (Fin (4 * m))) :
    (Fin m → Option Bool) × (Fin m → Option (Bool × Bool)) :=
  (roleMap m nA nB h ρ,
    fun r => (multiRun m nA nB h ρ r).map (fun p => if p.1 then p.2.2.2 else p.2.2.1))

/-- The deal: `ρ` uniform on `S_n`, `n = 4m` ("let ρ ←$ S_n be distributed uniformly", Theorems 10.1
and 10.2, pp.12–13). -/
noncomputable def multiDeal (m : ℕ) : PMF (Equiv.Perm (Fin (4 * m))) :=
  PMF.uniformOfFintype (Equiv.Perm (Fin (4 * m)))

end TetraOT.Supplement


