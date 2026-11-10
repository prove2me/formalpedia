-- Prove2me | Definitions.Def_DistancePreserver934_Exact_Removal
-- name    : DistancePreserver934_Exact_Removal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T08:37:49.730458+00:00
-- url     : https://prove2.me/theorems/64a164c6-697b-4433-988c-b1533e2bf116
-- title:
--   §6.2–6.3 — fixed parameters and the demand-removal procedure
-- statement:
--   Let $G$ be a graph on $V$, $n=|V|$, $P$ a demand set with $p=|P|$, and $H$ a minimal distance preserver of $(G,P)$.
--
--   **Fixed parameters (Equations (33)–(34)).** $d=|E_H|/n$ (so $2d$ is the average degree), $l=nd/(5p)$, $r_0=n^{1/2}d^{-3/2}$ and $r=\max\{6,r_0\}$. These are computed from the initial $H$ and $P$ and never change.
--
--   **Setting of the inductive step.** For a constant $C$, the setting means: $P$ is a demand set, $H$ is a minimal distance preserver of $(G,P)$, $n^{7/10}<p\le n$, and $H$ violates Equation (26): $nd=|E_H|>C\,n^{8/9}p^{4/9}$.
--
--   **States and updates.** A state is a pair $(K,R)$ of a current graph and a current demand set. An update to a demand set $R'$ replaces $K$ by an arbitrary subgraph $K'\le K$ that is a minimal distance preserver of $(G,R')$.
--
--   1. **Step 1.** If $|R|>p/2$ and some $q\in R$ has $\lambda_K(q)\le l$ (private length recomputed in $(K,R)$), remove $q$ and update.
--   2. **Step 2.** If $|R|>p/2$ and $\lambda_K(q)>l$ for every $q\in R$, choose nonempty $Q\subseteq R$ and nonempty $S$ such that $S$ covers $Q$ in $K$ and
--   $$|Q|\ge c_0d^2\sqrt r,\qquad |S|\le c_1|Q|/d,\qquad \operatorname{diam}_K(S)\le c_2r\tag{36}$$
--   ($c_0,c_1,c_2$ the constants of Lemma 10), remove $Q$ and update.
--
--   A **run** of length $\tau$ is a sequence of states starting at $(H,P)$ in which each step is a Step 1 or a Step 2 as labelled; it need not be finished. The loss of a step is $|E(K_i)|-|E(K_{i+1})|$, and the Step 1 (resp. Step 2) loss of a run is the sum of the losses of its Step 1 (resp. Step 2) steps.
--
--   The definitions encode only the rules of the procedure; none of the loss bounds of Lemmas 23–25, the retention bound (41) or any sparsity bound is part of them.
-- source:
--   Yanyu Chen, Yu Chen, Zihan Tan, Mingyang Yang, Improved Bounds on Distance Preservers, STOC 2027 submission #934 (October 2026), SHA-256 79b3d23a6e7b7fc6148c7a627181474a0129fb2f4c1d04ccd94c1da7987ed76b, §6.2 Equations (33)–(34) and §6.3 Demand Removal Procedure, Equations (35)–(36), printed p. 22–23 (PDF p. 23–24)

import Mathlib
import Definitions.Def_DistancePreserver934_Exact_Essential

namespace DistancePreserver934.Exact

open Classical

variable {V : Type} [Fintype V]

/-- `n = |V_H|` (§6, Equation (33)); the vertex set is the whole finite type. -/
noncomputable def sec6n (V : Type) [Fintype V] : ℝ := (Fintype.card V : ℝ)

/-- `d = |E_H| / n` (Equation (33)); the average degree of `H` is `2d`. -/
noncomputable def sec6d (H : SimpleGraph V) : ℝ := (numEdges H : ℝ) / sec6n V

/-- `l = nd / (5p)` (Equation (34)), with `p = |P|`. -/
noncomputable def sec6l (H : SimpleGraph V) (P : Finset (Sym2 V)) : ℝ :=
  sec6n V * sec6d H / (5 * (P.card : ℝ))

/-- `r = max{6, r₀}` with `r₀ = n^{1/2} d^{-3/2}` (Equation (34)). -/
noncomputable def sec6r (H : SimpleGraph V) : ℝ :=
  max 6 (sec6n V ^ ((1 : ℝ) / 2) * sec6d H ^ (-(3 : ℝ) / 2))

/-- The setting of the inductive step of §6 (PDF pp.22–23) for a given constant `C`:
`P` is a demand set with `n^{7/10} < p ≤ n`, `H` is a minimal distance preserver of `(G, P)`,
and `H` violates Equation (26): `nd = |E_H| > C n^{8/9} p^{4/9}` (Equation (33)). -/
def Sec6Setting (C : ℝ) (G H : SimpleGraph V) (P : Finset (Sym2 V)) : Prop :=
  IsDemandSet G P ∧ IsMinimalPreserver G H P ∧
    sec6n V ^ ((7 : ℝ) / 10) < (P.card : ℝ) ∧ (P.card : ℝ) ≤ sec6n V ∧
    C * sec6n V ^ ((8 : ℝ) / 9) * (P.card : ℝ) ^ ((4 : ℝ) / 9) < sec6n V * sec6d H

/-- A state `(K, R)` of the demand-removal procedure: the current graph `K = H(R)` and the
current demand set `R`. -/
abbrev RState (V : Type) := SimpleGraph V × Finset (Sym2 V)

/-- The update of §6.3: after the demand set shrinks to `R'`, the new graph `K'` is an arbitrary
subgraph of the current graph `K` that is a minimal distance preserver of `(G, R')`. -/
def IsUpdate (G : SimpleGraph V) (K K' : SimpleGraph V) (R' : Finset (Sym2 V)) : Prop :=
  K' ≤ K ∧ IsMinimalPreserver G K' R'

/-- One execution of Step 1 (§6.3): `|R| > p/2`, some `q ∈ R` has current private length
`λ_K(q) ≤ l`; it is removed and the graph is updated. -/
def Step1 (G H : SimpleGraph V) (P : Finset (Sym2 V)) (s s' : RState V) : Prop :=
  (P.card : ℝ) / 2 < (s.2.card : ℝ) ∧
    ∃ q ∈ s.2, (privLen s.1 s.2 q : ℝ) ≤ sec6l H P ∧ s'.2 = s.2.erase q ∧
      IsUpdate G s.1 s'.1 s'.2

/-- One execution of Step 2 (§6.3) with the Lemma 10 constants `c₀, c₁, c₂`:
`|R| > p/2`, every `q ∈ R` has `λ_K(q) > l`, and nonempty `Q ⊆ R`, `S` with `S` covering `Q`
in `K`, `|Q| ≥ c₀ d² √r`, `|S| ≤ c₁ |Q| / d`, `diam_K(S) ≤ c₂ r` (Equation (36)); `Q` is removed
and the graph is updated. -/
def Step2 (c₀ c₁ c₂ : ℝ) (G H : SimpleGraph V) (P : Finset (Sym2 V)) (s s' : RState V) : Prop :=
  (P.card : ℝ) / 2 < (s.2.card : ℝ) ∧ (∀ q ∈ s.2, sec6l H P < (privLen s.1 s.2 q : ℝ)) ∧
    ∃ Q : Finset (Sym2 V), ∃ S : Finset V, Q ⊆ s.2 ∧ Q.Nonempty ∧ S.Nonempty ∧
      Covers s.1 S Q ∧
      c₀ * sec6d H ^ 2 * Real.sqrt (sec6r H) ≤ (Q.card : ℝ) ∧
      (S.card : ℝ) ≤ c₁ * (Q.card : ℝ) / sec6d H ∧
      DiamLE s.1 S (c₂ * sec6r H) ∧
      s'.2 = s.2 \ Q ∧ IsUpdate G s.1 s'.1 s'.2

/-- The two kinds of steps. -/
inductive StepKind
  | one
  | two
  deriving DecidableEq

/-- A (finite, possibly unfinished) execution of the demand-removal procedure with `τ` steps:
states `st 0, …, st τ` starting from `(H, P)`, the `i`-th step being a Step 1 or a Step 2 according
to `kind i`. -/
def IsRun (c₀ c₁ c₂ : ℝ) (G H : SimpleGraph V) (P : Finset (Sym2 V)) (τ : ℕ)
    (st : ℕ → RState V) (kind : ℕ → StepKind) : Prop :=
  st 0 = (H, P) ∧ ∀ i < τ,
    (kind i = StepKind.one ∧ Step1 G H P (st i) (st (i + 1))) ∨
    (kind i = StepKind.two ∧ Step2 c₀ c₁ c₂ G H P (st i) (st (i + 1)))

/-- The number of edges deleted in step `i`, `|E(K_i)| − |E(K_{i+1})|`, as a real number. -/
noncomputable def stepLoss (st : ℕ → RState V) (i : ℕ) : ℝ :=
  (numEdges (st i).1 : ℝ) - (numEdges (st (i + 1)).1 : ℝ)

/-- The total number of edges deleted in the steps of kind `k` among the first `τ` steps. -/
noncomputable def kindLoss (τ : ℕ) (st : ℕ → RState V) (kind : ℕ → StepKind) (k : StepKind) : ℝ :=
  ∑ i ∈ (Finset.range τ).filter (fun i => kind i = k), stepLoss st i

end DistancePreserver934.Exact


