-- Prove2me | Definitions.Def_FiniteMemPOMDP_PlayStep
-- name    : FiniteMemPOMDP_PlayStep
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:29:11.555172+00:00
-- url     : https://prove2.me/theorems/a08e67c6-4688-4390-8cb1-b96ac3f26af1
-- title:
--   One coordinate $(A_{n+1},S_{n+1},K_{n+2})$ of a play
-- statement:
--   A **play** of the POMDP is the infinite sequence $(k_1,a_1,s_1,k_2,a_2,s_2,\dots)$ of states, actions and signals; the set of plays is $\Omega=(\mathcal K\times\mathcal A\times\mathcal S)^{\mathbb N}$.
--
--   The mission stores a play as a sequence $\omega=(\omega_0,\omega_1,\dots)$ of triples in $\mathcal A\times\mathcal S\times\mathcal K$: the coordinate $\omega_{n+1}=(A_{n+1},S_{n+1},K_{n+2})$ holds the action at stage $n+1$, the signal it produces, and the next state, and $\omega_0$ holds the initial state $K_1$ (with a fixed dummy action and signal that nothing reads). This is a re-indexing of $(\mathcal K\times\mathcal A\times\mathcal S)^{\mathbb N}$ that keeps together the pair $(K_{m+1},S_m)$, which is drawn jointly.
--
--   **Formalization Note** `PlayStep A S K` is a type synonym of `A × S × K` carrying the discrete σ-algebra, with accessors `act`, `sig`, `state`.
-- source:
--   Chatterjee, Saona & Ziliotto, Finite-memory strategies in POMDPs with Long-run Average Objectives, arXiv:1904.13360v2, §2.1, p.2

import Mathlib

namespace FiniteMemPOMDP

/-- **One coordinate of a play.**
Chatterjee, Saona & Ziliotto, arXiv:1904.13360v2, §2.1, p.2: "The infinite sequence
(k1, a1, s1, k2, a2, s2, . . .) is called a play, and the set of all plays is denoted by Ω",
with "Ω = (K × A × S)^ℕ".

A play is encoded as a sequence `ω : ℕ → PlayStep A S K`. Coordinate `n + 1` is the triple
`(A_{n+1}, S_{n+1}, K_{n+2})`: the action at stage `n + 1`, the signal it produces and the next
state. Coordinate `0` is `(a₀, s₀, K_1)`, where only the initial state `K_1` is meaningful (the
first two entries are a fixed dummy action and signal that no definition reads).

**Formalization Note** This regrouping of `(K × A × S)^ℕ` is a bijective re-indexing of the
paper's play space (the pair `(K_{m+1}, S_m)` is drawn jointly from `q(K_m, A_m)`, so it is
convenient to store it in one coordinate). `PlayStep` carries the discrete σ-algebra; the play
space carries the product σ-algebra. -/
def PlayStep (A S K : Type) : Type := A × S × K

instance (A S K : Type) : MeasurableSpace (PlayStep A S K) := ⊤

instance (A S K : Type) : MeasurableSingletonClass (PlayStep A S K) :=
  ⟨fun _ => trivial⟩

instance (A S K : Type) : DiscreteMeasurableSpace (PlayStep A S K) :=
  ⟨fun _ => trivial⟩

instance (A S K : Type) [Fintype A] [Fintype S] [Fintype K] [DecidableEq A] [DecidableEq S]
    [DecidableEq K] : Fintype (PlayStep A S K) :=
  inferInstanceAs (Fintype (A × S × K))

instance (A S K : Type) [Finite A] [Finite S] [Finite K] : Finite (PlayStep A S K) :=
  inferInstanceAs (Finite (A × S × K))

/-- The triple `(a, s, k)` as a play coordinate. -/
def PlayStep.mk {A S K : Type} (a : A) (s : S) (k : K) : PlayStep A S K := (a, s, k)

/-- The action entry of a play coordinate. -/
def PlayStep.act {A S K : Type} (x : PlayStep A S K) : A := (show A × S × K from x).1

/-- The signal entry of a play coordinate. -/
def PlayStep.sig {A S K : Type} (x : PlayStep A S K) : S := (show A × S × K from x).2.1

/-- The state entry of a play coordinate. -/
def PlayStep.state {A S K : Type} (x : PlayStep A S K) : K := (show A × S × K from x).2.2

end FiniteMemPOMDP


