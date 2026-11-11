-- Prove2me | Definitions.Def_RandomColorMix269_Mixing_Laws
-- name    : RandomColorMix269_Mixing_Laws
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:00:54.314062+00:00
-- url     : https://prove2.me/theorems/acb82f52-c5bf-4b6a-925e-45e421e2a969
-- title:
--   §§1–2 — pinnings, marginals, connected conditional supports, marginal boundedness and the random-graph event
-- statement:
--   Let $V$ be a finite set and $q\in\mathbb N$. A law on configurations is a mass function $\mu:[q]^V\to\mathbb R$. For a boundary $\Lambda\subseteq V$ and a configuration $x$, the pinning $\tau=x_\Lambda$ is **feasible** when the mass $\sum_{y:\,y_\Lambda=x_\Lambda}\mu(y)$ is strictly positive; then $\mu^\tau$ is the conditional law, kept on all of $[q]^V$ and supported on configurations agreeing with $x$ on $\Lambda$ (the published `SpinGirth5.pin`). For $U\subseteq V$ the **marginal** $\mu_U$ is the pushforward of $\mu$ under restriction to $U$; it is not a uniform law on any induced subgraph.
--
--   The one-site and two-site probabilities are $\mu(v\leftarrow c)$ and $\mu(v\leftarrow c,\,w\leftarrow e)$, and $d_H(x,y)$ is the Hamming distance. The support of $\mu$ is **connected** if any two configurations of positive mass are joined by a path of positive-mass configurations in which consecutive ones differ at exactly one coordinate. The law has **connected conditional supports** if $\mu^\tau$ has connected support for every feasible pinning $\tau$ (including the empty one). It is **$b$-marginally bounded** if for every feasible pinning $\tau$ on $\Lambda$, every $v\notin\Lambda$ and every colour $c$, either $\mu^\tau(v\leftarrow c)=0$ or $\mu^\tau(v\leftarrow c)\ge b$ (p.28).
--
--   A graph $G$ is $q$-colourable if it has a proper colouring $V\to[q]$. For a real $d>1$, $\mathbb P_{G\sim G(n,d/n)}$ is the Erdős–Rényi law in which each unordered pair of $[n]$ is an edge independently with probability $d/n$ (the published `LPCommunity.SBMRecovery.erProb`), and a sequence of graph events holds **with high probability** if its probability tends to $1$ as $n\to\infty$.
--
--   **Formalization Note** The uniform law $\mu_{G,q}$ on proper colourings is the published `MarkovMixing.properColoringDist`, equal to zero everywhere when $G$ has no proper colouring, which is why colourability is stated separately wherever $\mu_{G,q}$ is used.
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #269 (October 2026), PDF sha256 467638f1abc0f57df1bc0dcd9abfd308eb90ddbaf4947dac3eefa5f293ac6f05, §2 pp.6, §5.1 p.28 (marginal boundedness, connected conditional supports)

import Mathlib
import Definitions.Def_mm_transport
import Definitions.Def_SpinGirth5_heatBath
import Definitions.Def_LPCommunity_SBMRecovery_Setting

open scoped Classical BigOperators
open Finset Filter Topology
set_option autoImplicit false
noncomputable section

namespace RandomColorMix269.Mixing

/-! Li–Yang, STOC 2027 submission #269, §§1–2, pp.3–6.
Finite masses use the published IsDist, pin and properColoringDist interfaces.
All conditional-law statements require positive pinning mass. -/

variable {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}

def agrees (Λ : Finset V) (x y : V → Fin q) : Prop := ∀ v ∈ Λ, x v = y v

def pinMass (μ : (V → Fin q) → ℝ) (Λ : Finset V) (x : V → Fin q) : ℝ :=
  ∑ y, if agrees Λ y x then μ y else 0

def Feasible (μ : (V → Fin q) → ℝ) (Λ : Finset V) (x : V → Fin q) : Prop :=
  0 < pinMass μ Λ x

def marginal (μ : (V → Fin q) → ℝ) (U : Finset V) : (U → Fin q) → ℝ :=
  fun z => ∑ x, if (fun u : U => x u) = z then μ x else 0

def oneSite (μ : (V → Fin q) → ℝ) (v : V) (c : Fin q) : ℝ :=
  ∑ x, if x v = c then μ x else 0

def twoSite (μ : (V → Fin q) → ℝ) (v w : V) (c e : Fin q) : ℝ :=
  ∑ x, if x v = c ∧ x w = e then μ x else 0

def hamming (x y : V → Fin q) : ℕ := (univ.filter fun v => x v ≠ y v).card

def SupportConnected (μ : (V → Fin q) → ℝ) : Prop :=
  ∀ x y, 0 < μ x → 0 < μ y →
    Relation.ReflTransGen
      (fun a b : V → Fin q => 0 < μ a ∧ 0 < μ b ∧ hamming a b = 1) x y

def ConnectedConditionalSupports (μ : (V → Fin q) → ℝ) : Prop :=
  ∀ (Λ : Finset V) (x : V → Fin q), Feasible μ Λ x →
    SupportConnected (SpinGirth5.pin μ Λ x)

def MarginalBounded (μ : (V → Fin q) → ℝ) (b : ℝ) : Prop :=
  ∀ (Λ : Finset V) (x : V → Fin q), Feasible μ Λ x →
    ∀ v ∉ Λ, ∀ c : Fin q,
      oneSite (SpinGirth5.pin μ Λ x) v c = 0 ∨
        b ≤ oneSite (SpinGirth5.pin μ Λ x) v c

def Colorable (G : SimpleGraph V) (q : ℕ) : Prop :=
  Nonempty {x : V → Fin q // MarkovMixing.IsProperColoring G x}

def graphProb (n : ℕ) (d : ℝ) (E : SimpleGraph (Fin n) → Prop) : ℝ :=
  LPCommunity.SBMRecovery.erProb n (d / n) E

def WithHighProbability (d : ℝ) (E : (n : ℕ) → SimpleGraph (Fin n) → Prop) : Prop :=
  Tendsto (fun n => graphProb n d (E n)) atTop (𝓝 1)

end RandomColorMix269.Mixing


