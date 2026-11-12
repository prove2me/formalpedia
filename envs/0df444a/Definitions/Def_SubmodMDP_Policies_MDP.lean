-- Prove2me | Definitions.Def_SubmodMDP_Policies_MDP
-- name    : SubmodMDP_Policies_MDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:10:21.938198+00:00
-- url     : https://prove2.me/theorems/7b941cb1-b927-4035-a728-dc6cce74bf59
-- title:
--   Submodular MDPs, history-dependent policies, $V(\pi)$, $\mathrm{OPT}$, and policies computed by programs
-- statement:
--   **Submodular MDP (§1.1).** An instance consists of a finite nonempty state set $S=\{0,\dots,n_S-1\}$, a finite nonempty action set $A=\{0,\dots,n_A-1\}$, a horizon $H\ge1$, initial probabilities $\mathbb P[s_1=s']$ and transition probabilities
--   $$\mathbb P[s_{t+1}=s'\mid s_t=s,\ a_t=a],\qquad t\in\{1,\dots,H-1\},$$
--   all non-negative rationals summing to one; the transition probabilities may depend on $t$. The size parameter is $n=|S|+|A|+H$ and $\langle p\rangle$ is the total bit length of the numerators and denominators (in lowest terms) of all initial and transition probabilities. The instance is encoded as the integer list $[n_S,n_A,H]$ followed by these rationals in lexicographic order.
--
--   **Policies and value.** A randomized history-dependent policy $\pi$ assigns to every trajectory $s_1,a_1,\dots,s_{t-1},a_{t-1},s_t$ a probability distribution on $A$. The process draws $s_1$ from the initial law, $a_t$ from $\pi$ given the trajectory so far, and $s_{t+1}$ from the transition law of $(t,s_t,a_t)$. For a reward function $f:2^{S\sqcup A}\to\mathbb Q_{\ge0}$ (states and actions are distinct ground elements) the value of $\pi$ is
--   $$V(\pi)=\mathbb E\big[f(\{s_1,a_1,\dots,s_H,a_H\})\big],$$
--   and $\mathrm{OPT}=\sup_\pi V(\pi)$ over **all** randomized history-dependent policies.
--
--   **Policies computed by programs.** A preprocessing program $\mathrm{Pre}$ reads the encoded instance (and queries $f$) and outputs a description $\sigma$. A deterministic decision program $\mathrm{Dec}$ reads the instance, $\sigma$ and a trajectory and outputs the action distribution of the policy $\pi_\sigma$. The predicate *IsPolicyAlgorithm* with cost bound $B$, ratio $\rho$ and probability $q$ says:
--
--   1. every run of $\mathrm{Pre}$ halts within cost $B$;
--   2. for every $\sigma$ output with positive probability and every trajectory of length $t\le H$, $\mathrm{Dec}$ halts within cost $B$ and outputs a probability vector on $A$;
--   3. (memory) given $\sigma$, the output of $\mathrm{Dec}$ depends only on $t$ and on the entries of the trajectory $s_1,a_1,\dots,s_t$ at a set $K(H,t)$ of positions fixed in advance (independent of $\sigma$ and of the coins);
--   4. with probability at least $q$ over the coins of $\mathrm{Pre}$, $V(\pi_\sigma)\ge \mathrm{OPT}/\rho$.
--
--   These are the objects in which Theorem 2 is stated.
--
--   **Formalization Note** The reward oracle numbers state $s$ as $s$ and action $a$ as $n_S+a$. $\mathrm{Dec}$'s word length is computed from the encoded instance alone, so arithmetic on large numbers stored in $\sigma$ is charged by their length.
-- source:
--   Lars Rohwedder, Rico Zenklusen, STOC 2027 submission #658 (October 2026), §1.1, Eq. (1), p. 2 (PDF p. 3), and Theorem 2, p. 3 (PDF p. 4)

import Mathlib
import Definitions.Def_SubmodMDP_Policies_Machine

namespace SubmodMDP.Policies

noncomputable section

open Classical

/-! # Submodular Markov decision processes (§1.1, PDF p. 3)

States are `Fin nS`, actions `Fin nA`, times `1, …, H` (stored 0-based in trajectories). The
initial law `init` and the transition laws `trans t s a` (`t ∈ {1, …, H-1}`, Eq. (1)) are given
by non-negative rationals summing to one. Transitions may depend on `t`. -/

/-- An instance of a submodular MDP (the reward function is supplied separately). -/
structure Inst where
  nS : ℕ
  nA : ℕ
  H : ℕ
  init : Fin nS → ℚ
  trans : ℕ → Fin nS → Fin nA → Fin nS → ℚ

/-- Validity: nonempty state and action sets, `H ≥ 1`, and probability vectors for the initial
law and for every transition law `P[s_{t+1} = · | s_t = s, a_t = a]`, `t ∈ {1, …, H-1}`. -/
def Inst.Valid (I : Inst) : Prop :=
  1 ≤ I.nS ∧ 1 ≤ I.nA ∧ 1 ≤ I.H ∧
  (∀ s, 0 ≤ I.init s) ∧ ∑ s, I.init s = 1 ∧
  ∀ t, 1 ≤ t → t ≤ I.H - 1 → ∀ s a, (∀ s', 0 ≤ I.trans t s a s') ∧ ∑ s', I.trans t s a s' = 1

/-- The size parameter `n = |S| + |A| + H`. -/
def Inst.n (I : Inst) : ℕ := I.nS + I.nA + I.H

/-- `⟨p⟩`: the total bit length of the numerators and denominators (in lowest terms) of all
initial and transition probabilities. -/
def Inst.encSize (I : Inst) : ℕ :=
  ∑ s, ratBits (I.init s) +
    ∑ t ∈ Finset.Icc 1 (I.H - 1), ∑ s, ∑ a, ∑ s', ratBits (I.trans t s a s')

/-- The input encoding of an instance: `[nS, nA, H]`, then the initial probabilities, then the
transition probabilities for `t = 1, …, H-1` in lexicographic order of `(t, s, a, s')`, every
rational as `[num, den]`. -/
def Inst.enc (I : Inst) : List ℤ :=
  [(I.nS : ℤ), I.nA, I.H] ++ (List.finRange I.nS).flatMap (fun s => encRat (I.init s)) ++
    (List.range (I.H - 1)).flatMap (fun t =>
      (List.finRange I.nS).flatMap (fun s =>
        (List.finRange I.nA).flatMap (fun a =>
          (List.finRange I.nS).flatMap (fun s' => encRat (I.trans (t + 1) s a s')))))

/-- The ground set `S ⊔ A` of the reward function (states and actions are distinct elements). -/
abbrev Elem (I : Inst) := Fin I.nS ⊕ Fin I.nA

/-- A randomized history-dependent policy: given the completed pairs `(s₁,a₁), …, (s_{t-1},a_{t-1})`
and the current state `s_t`, a weight for every action. -/
abbrev Policy (I : Inst) := List (Fin I.nS × Fin I.nA) → Fin I.nS → Fin I.nA → ℝ

/-- A policy is valid if it gives a probability distribution on actions for every history. -/
def IsPolicy (I : Inst) (π : Policy I) : Prop :=
  ∀ h s, (∀ a, 0 ≤ π h s a) ∧ ∑ a, π h s a = 1

/-- Probability factor of time step `j` (0-based, time `j+1`) of the trajectory `τ`:
the initial (`j = 0`) or transition probability of the state, times the policy's probability of
the action given the history. -/
def stepProb (I : Inst) (π : Policy I) (τ : Fin I.H → Fin I.nS × Fin I.nA) (j : Fin I.H) : ℝ :=
  (if j.val = 0 then (I.init (τ j).1 : ℝ)
    else (I.trans j.val (τ ⟨j.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩).1
      (τ ⟨j.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩).2 (τ j).1 : ℝ)) *
  π ((List.ofFn τ).take j.val) (τ j).1 (τ j).2

/-- The probability of the full trajectory `τ = (s₁,a₁, …, s_H,a_H)` under policy `π`. -/
def trajProb (I : Inst) (π : Policy I) (τ : Fin I.H → Fin I.nS × Fin I.nA) : ℝ :=
  ∏ j, stepProb I π τ j

/-- The set `{s₁, a₁, …, s_H, a_H} ⊆ S ⊔ A` visited by a trajectory. -/
def visited (I : Inst) (τ : Fin I.H → Fin I.nS × Fin I.nA) : Finset (Elem I) :=
  Finset.univ.image (fun j => (Sum.inl (τ j).1 : Elem I)) ∪
    Finset.univ.image (fun j => (Sum.inr (τ j).2 : Elem I))

/-- `V(π) = E[f({s₁, a₁, …, s_H, a_H})]`. -/
def value (I : Inst) (f : Finset (Elem I) → ℚ) (π : Policy I) : ℝ :=
  ∑ τ, trajProb I π τ * (f (visited I τ) : ℝ)

/-- `OPT`: the supremum of `V(π)` over all randomized history-dependent policies. -/
def OPT (I : Inst) (f : Finset (Elem I) → ℚ) : ℝ :=
  sSup {v | ∃ π : Policy I, IsPolicy I π ∧ value I f π = v}

/-! ## Policies computed by programs -/

/-- The value oracle of `f`: element `inl s` has index `s`, element `inr a` has index `nS + a`. -/
def rewardOracle (I : Inst) (f : Finset (Elem I) → ℚ) : Oracle :=
  ⟨I.nS + I.nA, fun X => f (X.map finSumFinEquiv.symm.toEmbedding)⟩

/-- The input of the decision program: the instance, the policy description `σ` (with its
length), the history `(s₁,a₁), …, (s_{t-1},a_{t-1})` (with its length) and the current state. -/
def decInput (I : Inst) (σ : List ℤ) (hist : List (Fin I.nS × Fin I.nA)) (s : Fin I.nS) :
    List ℤ :=
  I.enc ++ [(σ.length : ℤ)] ++ σ ++ [(hist.length : ℤ)] ++
    hist.flatMap (fun p => [((p.1 : ℕ) : ℤ), ((p.2 : ℕ) : ℤ)]) ++ [((s : ℕ) : ℤ)]

/-- The trajectory `s₁, a₁, …, s_{t-1}, a_{t-1}, s_t` as a list of indices; position `2k` is
`s_{k+1}` and position `2k+1` is `a_{k+1}` (0-based). -/
def flatTraj (I : Inst) (hist : List (Fin I.nS × Fin I.nA)) (s : Fin I.nS) : List ℕ :=
  hist.flatMap (fun p => [(p.1 : ℕ), (p.2 : ℕ)]) ++ [(s : ℕ)]

/-- Decode exactly `k` rationals. -/
def decodeVec (k : ℕ) (out : List ℤ) : Option (Fin k → ℚ) :=
  (parseAll ((List.finRange k).mapM (fun _ => pRat)) out).map (fun L a => L.getD a 0)

/-- A probability vector. -/
def IsProbVec {k : ℕ} (q : Fin k → ℚ) : Prop := (∀ a, 0 ≤ q a) ∧ ∑ a, q a = 1

/-- The policy `π_σ` computed by the decision program `Dec` from the description `σ`, with
word length that of the instance and fuel `B` (`0` where `Dec` does not produce a vector). -/
def policyOf (Dec : Program) (I : Inst) (f : Finset (Elem I) → ℚ) (B : ℕ) (σ : List ℤ) :
    Policy I := fun hist s a =>
  match detOutput Dec (rewardOracle I f) (wordLen I.enc (rewardOracle I f)) (decInput I σ hist s) B
    with
  | none => 0
  | some out =>
    match decodeVec I.nA out with
    | none => 0
    | some q => (q a : ℝ)

/-- `(Pre, Dec, K)` is a randomized policy algorithm on instance `I` with reward `f`, cost bound
`B`, approximation ratio `ratio` and success probability `prob`:

1. every run of `Pre` on the encoded instance (oracle access to `f`) halts with cost `≤ B`;
2. for every description `σ` output with positive probability, and every history of length
   `t - 1 < H` and current state, the deterministic program `Dec` halts with cost `≤ B` and
   outputs a probability vector on the actions;
3. (memory) `Dec`'s output depends only on `t` and on the trajectory entries at the positions
   `K H t` (fixed before `σ` and the coins);
4. with probability at least `prob` over the coins of `Pre`, `V(π_σ) ≥ OPT / ratio`. -/
def IsPolicyAlgorithm (Pre Dec : Program) (K : ℕ → ℕ → Finset ℕ) (I : Inst)
    (f : Finset (Elem I) → ℚ) (B : ℕ) (ratio prob : ℝ) : Prop :=
  HaltsWithin Pre (rewardOracle I f) (wordLen I.enc (rewardOracle I f)) I.enc B ∧
  (∀ σ : List ℤ,
    some σ ∈ (outLaw Pre (rewardOracle I f) (wordLen I.enc (rewardOracle I f)) I.enc B).support →
      (∀ hist : List (Fin I.nS × Fin I.nA), hist.length + 1 ≤ I.H → ∀ s : Fin I.nS,
        ∃ out : List ℤ, ∃ q : Fin I.nA → ℚ,
          Computes Dec (rewardOracle I f) (wordLen I.enc (rewardOracle I f))
            (decInput I σ hist s) B out ∧
          decodeVec I.nA out = some q ∧ IsProbVec q) ∧
      (∀ hist hist' : List (Fin I.nS × Fin I.nA), ∀ s s' : Fin I.nS,
        hist.length = hist'.length → hist.length + 1 ≤ I.H →
        (∀ i ∈ K I.H (hist.length + 1), (flatTraj I hist s)[i]? = (flatTraj I hist' s')[i]?) →
        detOutput Dec (rewardOracle I f) (wordLen I.enc (rewardOracle I f))
            (decInput I σ hist s) B =
          detOutput Dec (rewardOracle I f) (wordLen I.enc (rewardOracle I f))
            (decInput I σ hist' s') B)) ∧
  ENNReal.ofReal prob ≤
    (outLaw Pre (rewardOracle I f) (wordLen I.enc (rewardOracle I f)) I.enc B).toOuterMeasure
      {o | ∃ σ, o = some σ ∧ OPT I f / ratio ≤ value I f (policyOf Dec I f B σ)}

end

end SubmodMDP.Policies


