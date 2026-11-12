-- Prove2me | Definitions.Def_PoQHierarchy_Main_KLocalNS
-- name    : PoQHierarchy_Main_KLocalNS
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T06:49:21.10106+00:00
-- url     : https://prove2.me/theorems/3a3349a7-804b-4867-b5f4-2fc35d70dd3f
-- title:
--   $k$-local non-signaling strategies (Definition 5.3) and the value $\omega_{ns\text{-}k}$
-- statement:
--   A **$k$-local non-signaling strategy** (Definition 5.3) for an $n$-player game consists of
--
--   1. shared classical randomness $\ell\sim\pi$;
--   2. finitely many independent boxes. Box $\beta$ is shared by a set $S_\beta\subseteq[n]$ of exactly $k$ players, has finite input and output alphabets at each of its parties, and is a conditional distribution $\Pr_\beta[a_S\mid x_S]$ satisfying the **non-signaling constraints**
--   $$\sum_{a_{S\setminus T}}\Pr_\beta[a_S\mid x_S]=\sum_{a_{S\setminus T}}\Pr_\beta[a_S\mid x'_S]\qquad\text{for all }T\subseteq S_\beta\text{ and }x_T=x'_T;$$
--   3. for every player a classical local strategy: a finite decision tree that depends on the player's question $x_i$ and on $\ell$, and that adaptively gives inputs to the player's ports of its boxes, depending on the outputs obtained so far, and finally answers.
--
--   Conditioned on the randomness, distinct boxes are independent, and there is no communication. Formally, for an assignment of an output to every port of every box, each player's tree determines the input it gives each of its ports and its answer; the probability of the assignment is the product over boxes of $\Pr_\beta[\text{outputs}\mid\text{inputs}]$. The correlation sums this over assignments and over $\ell$, and $\omega_{ns\text{-}k}(G)$ is the supremum of the winning probabilities.
--
--   For $k=0$ no box can be used and the model is classical; for $k=n$ it is the non-signaling model.
--
--   **Formalization Note** The randomness ranges over finite sets and the boxes are finitely many; both change no value, because every finite run uses finitely many boxes and winning probabilities are linear in mixtures. Input alphabets are nonempty (`Fin (m+1)`), which excludes only boxes that can never be queried. A port asked twice keeps its first input and output; a port never asked receives a fixed default input, which by non-signaling does not affect the other outputs.
-- source:
--   Kaniuar Bacho, Dominik Leichtle, Atul Singh Arora, Alexandru Cojocaru, STOC 2027 submission #1666 (October 2026), §5.2, Definition 5.3 (p.29), ω_ns-k (p.30); canonical PDF sha256 3009a0afeb95e5789f4e029db39d01935081f03d75e7fa263cb4b408aed40fb1

import Mathlib
import Definitions.Def_PoQHierarchy_Main_NonlocalGame

open QAlgorithms.Complexity
set_option autoImplicit false

namespace PoQHierarchy.Main

/-!
Bacho, Leichtle, Arora, Cojocaru, STOC 2027 submission #1666, §5.2, Definition 5.3 (pp.29–30):
`k`-local non-signaling strategies and the value `ω_{ns-k}(G)`.

The players share classical randomness and finitely many independent boxes; box `β` is shared by
a set `S_β` of exactly `k` players, has finite input and output alphabets at each of its parties
and satisfies the non-signaling constraints for every `T ⊆ S_β`. Each player queries the boxes it
takes part in adaptively, through a finite decision tree that depends on its question and on the
shared randomness, and then answers.

Semantics: for an assignment `out` of an output to every port of every box, each player's tree,
fed the outputs at its own ports, determines the input it gives each of its ports (the first one,
if a port is asked twice; a fixed default input for a port it never asks) and its answer. The
probability of `out` is `∏_β p_β(out_β | inputs_β)`; distinct boxes are independent given the
randomness.
-/

/-- A finite adaptive decision tree of player `i`: either answer, or give input `x` to its port of
a box `β` with `i ∈ S β` and continue according to the box's output. Input alphabets are
`Fin (ni β i + 1)` (nonempty), output alphabets `Fin (no β i)`. -/
inductive LocalTree (n : ℕ) (B : Type) (S : B → Finset (Fin n)) (ni no : B → Fin n → ℕ)
    (i : Fin n) (A : Type) : Type
  | answer (a : A)
  | ask (β : B) (h : i ∈ S β) (x : Fin (ni β i + 1))
      (next : Fin (no β i) → LocalTree n B S ni no i A)

/-- Running a tree against the outputs `out β h` at the player's ports: the first input given to
each port (or `none`), and the answer. -/
def LocalTree.run {n : ℕ} {B : Type} [DecidableEq B] {S : B → Finset (Fin n)}
    {ni no : B → Fin n → ℕ} {i : Fin n} {A : Type} (out : (β : B) → i ∈ S β → Fin (no β i)) :
    LocalTree n B S ni no i A → ((β : B) → Option (Fin (ni β i + 1))) × A
  | .answer a => (fun _ => none, a)
  | .ask β h x next =>
    let r := (next (out β h)).run out
    (Function.update r.1 β (some x), r.2)

/-- A **`k`-local non-signaling strategy** (Definition 5.3) for `n` players with question sets
`Fin (q i)` and answer sets `Fin (o i)`: shared randomness `l ~ π` on a finite set; a finite set `B`
of independent boxes, box `β` shared by the `k` players of `S β`, with the conditional distribution
`p_β(a_S | x_S)` satisfying the non-signaling constraints
`∑_{a_{S∖T}} p_β(a_S | x_S) = ∑_{a_{S∖T}} p_β(a_S | x'_S)` for all `T ⊆ S_β` and `x_T = x'_T`; and
for each player a decision tree depending on the randomness and its question. -/
structure KNSStrategy (n : ℕ) (q o : Fin n → ℕ) (k : ℕ) where
  Λ : Type
  [finΛ : Fintype Λ]
  π : Λ → ℝ
  π_nonneg : ∀ l, 0 ≤ π l
  π_sum : ∑ l, π l = 1
  B : Type
  [finB : Fintype B]
  [decB : DecidableEq B]
  S : B → Finset (Fin n)
  S_card : ∀ β, (S β).card = k
  ni : B → Fin n → ℕ
  no : B → Fin n → ℕ
  p : (β : B) → ((j : {j // j ∈ S β}) → Fin (ni β j + 1)) →
    ((j : {j // j ∈ S β}) → Fin (no β j)) → ℝ
  p_nonneg : ∀ β x a, 0 ≤ p β x a
  p_sum : ∀ β x, ∑ a, p β x a = 1
  p_ns : ∀ β (T : Finset (Fin n)), T ⊆ S β →
    ∀ x x' : (j : {j // j ∈ S β}) → Fin (ni β j + 1), (∀ j : {j // j ∈ S β}, j.1 ∈ T → x j = x' j) →
    ∀ a0 : (j : {j // j ∈ S β}) → Fin (no β j),
      ∑ a ∈ Finset.univ.filter (fun a : (j : {j // j ∈ S β}) → Fin (no β j) =>
          ∀ j : {j // j ∈ S β}, j.1 ∈ T → a j = a0 j), p β x a =
      ∑ a ∈ Finset.univ.filter (fun a : (j : {j // j ∈ S β}) → Fin (no β j) =>
          ∀ j : {j // j ∈ S β}, j.1 ∈ T → a j = a0 j), p β x' a
  T : (i : Fin n) → Λ → Fin (q i) → LocalTree n B S ni no i (Fin (o i))

attribute [instance] KNSStrategy.finΛ KNSStrategy.finB KNSStrategy.decB

/-- The correlation of a `k`-local non-signaling strategy:
`p(a|x) = ∑_l π(l) ∑_{out} ∏_β p_β(out_β | inputs_β(l, x, out)) · [answers(l, x, out) = a]`. -/
noncomputable def KNSStrategy.corr {n : ℕ} {q o : Fin n → ℕ} {k : ℕ} (St : KNSStrategy n q o k)
    (a : (i : Fin n) → Fin (o i)) (x : (i : Fin n) → Fin (q i)) : ℝ :=
  ∑ l, St.π l * ∑ out : ((β : St.B) → (j : {j // j ∈ St.S β}) → Fin (St.no β j)),
    (∏ β, St.p β (fun j => (((St.T j.1 l (x j.1)).run (fun β' h => out β' ⟨j.1, h⟩)).1 β).getD 0)
      (out β)) *
    (if ∀ i, ((St.T i l (x i)).run (fun β' h => out β' ⟨i, h⟩)).2 = a i then 1 else 0)

/-- The value `ω_{ns-k}(G)` (p.30): the supremum of the winning probabilities of `k`-local
non-signaling strategies. -/
noncomputable def omegaNS {n : ℕ} (G : NonlocalGame n) (k : ℕ) : ℝ :=
  sSup {v | ∃ St : KNSStrategy n G.q G.o k, G.winOf St.corr = v}

end PoQHierarchy.Main


