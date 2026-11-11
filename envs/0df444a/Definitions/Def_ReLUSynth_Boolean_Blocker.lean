-- Prove2me | Definitions.Def_ReLUSynth_Boolean_Blocker
-- name    : ReLUSynth_Boolean_Blocker
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:11:53.588334+00:00
-- url     : https://prove2.me/theorems/388cecbb-9d46-466d-a206-4d7543609947
-- title:
--   Exact-sum blockers (Definition 4.3), the blocker language and the restrictions of Lemma 4.5
-- statement:
--   For integers $n\ge1$, $p\ge0$ and positive integers $\beta_1,\dots,\beta_n,T$, an **exact-sum blocker of size at most $p$** is a set $H\subseteq\{1,\dots,n\}$ with $|H|\le p$ such that
--   $$\sum_{j=1}^n\beta_jz_j=T\ \Longrightarrow\ \sum_{j\in H}z_j\ge1\qquad\text{for every }z\in\{0,1\}^n.$$
--   The condition is vacuous when no subset sums to $T$. The **blocker language** is the set of binary codes of well-formed instances $(\beta_1,\dots,\beta_n,T,p)$ that have such a blocker.
--
--   An instance satisfies the **restrictions of Lemma 4.5** when there is a prime $q\ge5$ with $p=q-1$, every $\beta_j$ satisfies $0<\beta_j<T$, is not a power of two and $\beta_j\equiv3\pmod q$, $T\equiv0\pmod q$, and $n>p$.
--
--   **Formalization Note.** The supplied prime is $q=p+1$, so it is not stored separately; "odd" is implied by $q\ge5$ prime.
-- source:
--   Myrisiotis, The Complexity of ReLU Network Synthesis from a Parameter Multiset, arXiv:2611.04074v1, p. 16, Definition 4.3; p. 17, Lemma 4.5

import Mathlib
import Definitions.Def_ReLUSynth_Boolean_Synthesis

namespace ReLUSynth.Boolean

/-! Myrisiotis, *The Complexity of ReLU Network Synthesis from a Parameter Multiset*,
arXiv:2611.04074v1, §4.1, Definition 4.3 (p. 16) and the restrictions of Lemma 4.5 (p. 17). -/

/-- **Exact-sum blocker of size at most `p`** (Definition 4.3, p. 16): for source numbers
`β_1, …, β_n` and target `T`, a set `H ⊆ {1, …, n}` with `|H| ≤ p` such that every
`z ∈ {0,1}^n` with `∑_j β_j z_j = T` has `∑_{j ∈ H} z_j ≥ 1`, i.e. selects some index of `H`.
The condition is vacuous when no subset sums to `T`. -/
def IsBlocker {n : ℕ} (β : Fin n → ℕ) (T p : ℕ) (H : Finset (Fin n)) : Prop :=
  H.card ≤ p ∧
    ∀ z : Fin n → Bool, (∑ j, β j * (if z j then 1 else 0)) = T → ∃ j ∈ H, z j = true

/-- An instance `(β_1, …, β_n, T, p)` of the exact-sum blocker problem, the numbers listed
explicitly. -/
structure BlockerInstance where
  /-- the source numbers `β_1, …, β_n` -/
  β : List ℕ
  /-- the target `T` -/
  T : ℕ
  /-- the size bound `p` -/
  p : ℕ

namespace BlockerInstance

/-- Well-formedness (Definition 4.3): `n ≥ 1` and positive integers `β_1, …, β_n, T` (`p ≥ 0` is
any natural number). -/
def WellFormed (I : BlockerInstance) : Prop :=
  I.β ≠ [] ∧ (∀ b ∈ I.β, 0 < b) ∧ 0 < I.T

/-- The instance has an exact-sum blocker of size at most `p`. -/
def HasBlocker (I : BlockerInstance) : Prop :=
  ∃ H : Finset (Fin I.β.length), IsBlocker (fun j => I.β.get j) I.T I.p H

/-- Binary code of an instance: the list of source numbers, `T`, `p`. -/
def encode (I : BlockerInstance) : List Bool := encList encNat I.β ++ encNat I.T ++ encNat I.p

/-- **The restrictions of Lemma 4.5** (p. 17): there is an odd prime `q ≥ 5` with `p = q − 1`;
every `β_j` satisfies `0 < β_j < T`, is not a power of two, and `β_j ≡ 3 (mod q)`; `T ≡ 0
(mod q)`; and `n > p`. (The supplied prime is `q = p + 1`, so it is determined by `p`; "odd" is
implied by `q ≥ 5` prime.) -/
def Restricted (I : BlockerInstance) : Prop :=
  ∃ q : ℕ, q.Prime ∧ 5 ≤ q ∧ I.p = q - 1 ∧
    (∀ b ∈ I.β, 0 < b ∧ b < I.T ∧ (¬ ∃ k : ℕ, b = 2 ^ k) ∧ b % q = 3) ∧
    I.T % q = 0 ∧ I.p < I.β.length

end BlockerInstance

/-- **The exact-sum blocker language**: the codes of the well-formed instances that have an
exact-sum blocker of size at most `p`. -/
def BlockerLang : Set (List Bool) :=
  {s | ∃ I : BlockerInstance, I.WellFormed ∧ I.HasBlocker ∧ s = I.encode}

end ReLUSynth.Boolean


