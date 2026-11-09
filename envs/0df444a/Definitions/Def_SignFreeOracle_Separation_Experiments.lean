-- Prove2me | Definitions.Def_SignFreeOracle_Separation_Experiments
-- name    : SignFreeOracle_Separation_Experiments
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:15:42.597121+00:00
-- url     : https://prove2.me/theorems/ff5c1628-b17c-4945-be30-d7078dd6cb9a
-- title:
--   Adaptive queries, partial labellings and the coupled presampling experiment
-- statement:
--   An adaptive randomized query algorithm uses a finite decision tree with a finite string of private fair coins. Query budgets hold for every input, random string and possible answer function. Graph algorithms may query any label. A partial labelling is an injective partial map; its extensions are sampled uniformly from all extending permutations. Forward and inverse permutation queries are both available in the permutation experiment.
--
--   Given an arbitrary witness map $\pi\mapsto w_\pi$ and a family $D_w$ of distributions over partial labellings, the coupled experiment draws
--   $$\pi\text{ uniformly};\qquad \sigma\sim D_{w_\pi};\qquad \pi'\text{ uniformly extending }\sigma.$$
--   The same witness $w_\pi$ is used in both runs. Finite sums compute the probabilities, including all algorithm randomness. The family $D_w$ is chosen before the test algorithm and all query budgets. Query addresses, returned labels and fixed seeds remain separate. The fresh-query bad event and rooted-component property are defined as events, rather than restrictions on arbitrary algorithms. Only the separate tree-exploration lemma restricts queries to previously exposed neighbouring labels.
-- source:
--   Hamoudi, Le Borgne, Teganahally Sridhara, Quantum Advantage with Sign-Free Proofs: An Oracle Separation between StoqMA and MA, STOC 2027 submission #601 (October 2026), Sections 4–5, pp. 13–16 (PDF pp. 13–16)

import Mathlib
import Definitions.Def_DynOracleConn_ProbeTree
import Definitions.Def_SignFreeOracle_Separation_Encoding

set_option autoImplicit false

namespace SignFreeOracle.Separation

open QAlgorithms.Complexity

/-- Finite adaptive oracle algorithms with private fair coins, without local-query restrictions.
The decision tree can depend on the supplied witness or seed labels. -/
structure RandomQuery (Q Ans Input : Type) where
  coins : ℕ
  tree : Input → Bits coins → DynOracleConn.ProbeTree Q Ans Bool

noncomputable def RandomQuery.accept {Q Ans Input : Type} (A : RandomQuery Q Ans Input)
    (O : Q → Ans) (input : Input) : ℝ := by
  classical
  exact ((Finset.univ.filter fun r => (A.tree input r).run O = true).card : ℝ) / 2 ^ A.coins

def RandomQuery.budget {Q Ans Input : Type} (A : RandomQuery Q Ans Input) (q : ℕ) : Prop :=
  ∀ input r O, (A.tree input r).cost O ≤ q

/-- An injective partial labelling, with no arbitrary choice of an extension. -/
def PartialLabel (N : ℕ) :=
  {f : Fin N → Option (Fin N) // ∀ i j y, f i = some y → f j = some y → i = j}

noncomputable instance (N : ℕ) : Fintype (PartialLabel N) := by
  unfold PartialLabel
  exact Fintype.ofFinite _

noncomputable def PartialLabel.size {N : ℕ} (σ : PartialLabel N) : ℕ := by
  classical
  exact (Finset.univ.filter fun v => (σ.val v).isSome).card

def Extends {N : ℕ} (σ : PartialLabel N) (π : Equiv.Perm (Fin N)) : Prop :=
  ∀ v y, σ.val v = some y → π v = y

/-- Uniform extensions of an injective partial bijection. This finite set is nonempty,
including when the domain is empty or already the entire carrier. -/
noncomputable def extensionMean {N : ℕ} (σ : PartialLabel N)
    (f : Equiv.Perm (Fin N) → ℝ) : ℝ := by
  classical
  exact (∑ π ∈ Finset.univ.filter (Extends σ), f π) /
    ((Finset.univ.filter (Extends σ)).card : ℝ)

noncomputable def permMean {N : ℕ} (f : Equiv.Perm (Fin N) → ℝ) : ℝ :=
  (∑ π, f π) / (Fintype.card (Equiv.Perm (Fin N)) : ℝ)

def permutationAnswer {N : ℕ} (π : Equiv.Perm (Fin N)) (q : Bool × Fin N) : Fin N :=
  if q.1 then π q.2 else π.symm q.2

/-- Step 1 draws π and wπ, step 2 draws σ from D(wπ), step 3 independently draws π'
uniformly extending σ. Both executions receive the same witness wπ. -/
noncomputable def resampledMean {N p : ℕ} (w : Equiv.Perm (Fin N) → Bits p)
    (D : Bits p → PMF (PartialLabel N))
    (f : Equiv.Perm (Fin N) → Bits p → ℝ) : ℝ :=
  permMean fun π => ∑ σ, ((D (w π)) σ).toReal * extensionMean σ (fun π' => f π' (w π))

/-- The simultaneous algorithm-independent guarantee of Lemma 5.1. -/
def PresamplingGood {m p : ℕ} (w : Equiv.Perm (Fin (2 ^ m)) → Bits p)
    (γ : ℝ) (t : ℕ) (D : Bits p → PMF (PartialLabel (2 ^ m))) : Prop :=
  (∀ input σ, (D input) σ ≠ 0 → σ.size ≤ t) ∧
  ∀ (q : ℕ) (A : RandomQuery (Bool × Fin (2 ^ m)) (Fin (2 ^ m)) (Bits p)),
    A.budget q →
    |permMean (fun π => A.accept (permutationAnswer π) (w π)) -
      resampledMean w D (fun π input => A.accept (permutationAnswer π) input)| ≤
        2 * ((p : ℝ) + Real.logb 2 (1 / γ)) * q / t + γ

/-- The same sorted adjacency-list convention on any finite graph, for standalone trees. -/
noncomputable def anyGraphQuery {N : ℕ} (G : SimpleGraph (Fin N))
    (π : Equiv.Perm (Fin N)) (q : Fin N × ℕ) : Fin N := by
  classical
  exact ((Finset.univ.filter fun y => G.Adj (π.symm q.1) (π.symm y)).sort (· ≤ ·)).getD q.2 q.1

/-- Bad event: a query guesses a nonisolated vertex not exposed by the seed or earlier replies.
Addresses and replies are recorded separately; arbitrary addresses are permitted. -/
def FreshNonisolated {N : ℕ} (G : SimpleGraph (Fin N)) (π : Equiv.Perm (Fin N))
    (seed : Set (Fin N)) (history : List ((Fin N × ℕ) × Fin N)) : Prop :=
  ∃ k e, history[k]? = some e ∧ e.1.1 ∉ seed ∧
    (∀ old ∈ history.take k, e.1.1 ≠ old.2) ∧
    ∃ v, G.Adj (π.symm e.1.1) v

/-- Every queried address belongs to a component meeting the seed, or is a YES-isolate.
The graph used for reachability is induced by the seed and the addresses in the prefix. -/
def RootedAddresses {N : ℕ} (G : SimpleGraph (Fin N)) (π : Equiv.Perm (Fin N))
    (seed : Set (Fin N)) (history : List ((Fin N × ℕ) × Fin N)) : Prop :=
  ∀ k, let S : Set (Fin N) := seed ∪ {x | ∃ e ∈ history.take k, e.1.1 = x}
       ∀ v ∈ S, (¬ ∃ u, G.Adj (π.symm v) u) ∨
         ∃ u, ∃ hu : u ∈ S, ∃ hv : v ∈ S, u ∈ seed ∧
           ((G.map π.toEmbedding).induce S).Reachable ⟨u, hu⟩ ⟨v, hv⟩

/-- Local rooted exploration is required only in Lemma 4.3, never in Theorem 4.4. -/
def RootLocal {N : ℕ} (G : SimpleGraph (Fin N)) (A : RandomQuery (Fin N × ℕ) (Fin N) (Fin N))
    (root : Fin N) : Prop :=
  ∀ π r k e, ((A.tree (π root) r).transcript (anyGraphQuery G π))[k]? = some e →
    e.1.1 = π root ∨ ∃ old ∈ ((A.tree (π root) r).transcript (anyGraphQuery G π)).take k,
      e.1.1 = old.2

noncomputable def fixedSeed {N : ℕ} (σ : PartialLabel N) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter fun x => ∃ v, σ.val v = some x

noncomputable def traceProbability {Q Ans Input : Type} (A : RandomQuery Q Ans Input)
    (O : Q → Ans) (input : Input) (E : List (Q × Ans) → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter fun r => E ((A.tree input r).transcript O)).card : ℝ) / 2 ^ A.coins

end SignFreeOracle.Separation


