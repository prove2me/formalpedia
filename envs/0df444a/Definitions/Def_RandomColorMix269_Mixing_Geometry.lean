-- Prove2me | Definitions.Def_RandomColorMix269_Mixing_Geometry
-- name    : RandomColorMix269_Mixing_Geometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:01:35.140185+00:00
-- url     : https://prove2.me/theorems/e0fe9c06-9e24-4072-9dbf-f4f3976969bb
-- title:
--   §§5.2–5.5 — high-degree buffer $S=N_G[V^{HD}]$, low region $U$, components, buffered marginal and percolation events
-- statement:
--   Fix reals $\eta,d$ and put $D=\lfloor(1+\eta/3)d\rfloor$. For a finite graph $G$ let $V^{HD}=\{v:\deg_G(v)>D\}$ be the high-degree vertices, $N_G[A]=A\cup N_G(A)$ the closed neighbourhood, $S=N_G[V^{HD}]$ the **buffer** and $U=V\setminus S$ the **low region** (p.30). The **buffered marginal** is $\nu=(\mu_{G,q})_U$, the pushforward of the uniform proper-colouring law to $U$; it weights each colouring of $U$ by its number of extensions to $S$.
--
--   The components of $G[W]$ are the nonempty vertex sets $R\subseteq W$ with $G[R]$ connected and closed under adjacency inside $W$. A component is a tree or unicyclic exactly when it has at most as many edges as vertices. The **buffer event** with constant $K$ says that every component of $G[S]$ is a tree or unicyclic and has at most $K\ln n$ vertices, $n=|V|$. The **extension property** for $U$ says that every proper colouring of $G[U]$ extends to a proper colouring of $G$. A proper list-colouring for lists $L(v)$ is a proper colouring with $x(v)\in L(v)$ for all $v$.
--
--   For Lemma 5.10, every vertex is marked independently with probability $p$, independently of $G\sim G(n,d/n)$; the joint probability of an event $E(G,Z)$ is
--   $$
--   \sum_G\ \mathbb P(G)\sum_{Z\subseteq[n]}p^{|Z|}(1-p)^{n-|Z|}\,\mathbf 1[E(G,Z)].
--   $$
--   `PercolationConstants η d p K` records both conclusions of Lemma 5.10: $p\in(0,1)$; for every $J>0$, $K_J>0$ and for all large $n$
--   $$
--   \mathbb P_{G,Z}\Big(\max_{R\text{ component of }G[N_G[V^{HD}\cup Z]]}|R|>K_J\ln n\Big)\le n^{-J};
--   $$
--   and there is $A>0$ with $\mathbb P_G(\text{buffer event with }K_1)\ge1-A/n$ for all large $n$.
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #269 (October 2026), PDF sha256 467638f1abc0f57df1bc0dcd9abfd308eb90ddbaf4947dac3eefa5f293ac6f05, p.30 (D, V^HD, S, U), pp.30–33 (Lemma 5.10, §5.3)

import Definitions.Def_RandomColorMix269_Mixing_Laws

open scoped Classical BigOperators
open Finset
set_option autoImplicit false
noncomputable section

namespace RandomColorMix269.Mixing

/-! §2 p.6, §3.2 p.8, §§5.2–5.5 pp.30–37. Components are nonempty
maximal connected vertex sets of the induced graph. Edge count ≤ vertex
count characterizes tree or unicyclic components. -/
variable {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}

def cutoff (η d : ℝ) : ℕ := ⌊(1 + η / 3) * d⌋₊

def highDegree (G : SimpleGraph V) (D : ℕ) : Finset V :=
  univ.filter fun v => D < G.degree v

def closedNeighborhood (G : SimpleGraph V) (A : Finset V) : Finset V :=
  A ∪ univ.filter (fun v => ∃ u ∈ A, G.Adj u v)

def buffer (G : SimpleGraph V) (D : ℕ) : Finset V :=
  closedNeighborhood G (highDegree G D)

def lowRegion (G : SimpleGraph V) (D : ℕ) : Finset V := (buffer G D)ᶜ

def components (G : SimpleGraph V) (W : Finset V) : Finset (Finset V) :=
  univ.filter fun R => R ⊆ W ∧ R.Nonempty ∧ (G.induce (R : Set V)).Connected ∧
    ∀ v ∈ R, ∀ w ∈ W, G.Adj v w → w ∈ R

def SmallComponents (G : SimpleGraph V) (W : Finset V) (L : ℝ) : Prop :=
  ∀ R ∈ components G W, (R.card : ℝ) ≤ L

def Pseudoforest (G : SimpleGraph V) (W : Finset V) : Prop :=
  ∀ R ∈ components G W, (G.induce (R : Set V)).edgeFinset.card ≤ R.card

def BufferEvent (G : SimpleGraph V) (D : ℕ) (K : ℝ) : Prop :=
  Pseudoforest G (buffer G D) ∧
    SmallComponents G (buffer G D) (K * Real.log (Fintype.card V))

def ProperOn (G : SimpleGraph V) (U : Finset V) (z : U → Fin q) : Prop :=
  ∀ v w : U, G.Adj v w → z v ≠ z w

def ExtensionProperty (G : SimpleGraph V) (q : ℕ) (U : Finset V) : Prop :=
  ∀ z : U → Fin q, ProperOn G U z →
    ∃ x : V → Fin q, MarkovMixing.IsProperColoring G x ∧ ∀ u : U, x u = z u

def bufferedLaw (G : SimpleGraph V) (q D : ℕ) : (lowRegion G D → Fin q) → ℝ :=
  marginal (MarkovMixing.properColoringDist G q) (lowRegion G D)

def ProperListColoring (H : SimpleGraph V) (L : V → Finset (Fin q)) (x : V → Fin q) : Prop :=
  MarkovMixing.IsProperColoring H x ∧ ∀ v, x v ∈ L v

/-- Bernoulli marks, independent over all vertices. -/
def markWeight (p : ℝ) (Z : Finset V) : ℝ :=
  ∏ v : V, if v ∈ Z then p else 1 - p

def markedProb (n : ℕ) (d p : ℝ)
    (E : SimpleGraph (Fin n) → Finset (Fin n) → Prop) : ℝ :=
  ∑ G : SimpleGraph (Fin n),
    LPCommunity.SBMRecovery.edgeWeight G (fun _ _ => d / n) *
      ∑ Z : Finset (Fin n), markWeight p Z * (if E G Z then 1 else 0)

/-- The first clause of Lemma 5.10 at exponent J. -/
def PercolationBound (η d p J K : ℝ) : Prop :=
  ∀ᶠ n : ℕ in Filter.atTop,
    markedProb n d p (fun G Z =>
      ¬ SmallComponents G (closedNeighborhood G (highDegree G (cutoff η d) ∪ Z))
        (K * Real.log n)) ≤ (n : ℝ) ^ (-J)

/-- Both conclusions of Lemma 5.10, with one K_J function chosen before n. -/
def PercolationConstants (η d p : ℝ) (K : ℝ → ℝ) : Prop :=
  0 < p ∧ p < 1 ∧ (∀ J : ℝ, 0 < J → 0 < K J ∧ PercolationBound η d p J (K J)) ∧
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ n : ℕ in Filter.atTop,
      1 - A / n ≤ graphProb n d (fun G => BufferEvent G (cutoff η d) (K 1))

end RandomColorMix269.Mixing


