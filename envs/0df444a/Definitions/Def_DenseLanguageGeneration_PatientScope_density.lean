-- Prove2me | Definitions.Def_DenseLanguageGeneration_PatientScope_density
-- name    : DenseLanguageGeneration_PatientScope_density
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T11:48:21.001123+00:00
-- url     : https://prove2.me/theorems/5d00bfc1-353b-438a-9409-795f4e9a6a44
-- title:
--   First-announcement density, target ranks and switch-loss counting
-- statement:
--   Let $G$ be any deterministic finite-history generator, $K$ an infinite language of positive integers, and $a_1,a_2,\ldots$ a received input stream, with response $b_t$. Define generator ownership and prefix counts by
--
--   $$
--   D=\{x:\exists t\ge1,\ b_t=x\ \land\ \forall s\le t,\ a_s\ne x\},
--   \qquad \mu_n(S)=|S\cap\{1,\ldots,n\}|.
--   $$
--
--   The corresponding adversary ownership set consists of inputs with no earlier matching response. A response at the same round cannot precede that round's input. Define eventual generation using the imported nonrepetition correctness predicate, and set
--
--   $$
--   \operatorname{ld}(G,K,a)=\liminf_{n\to\infty}
--   \frac{\mu_n(D\cap K)}{\mu_n(K)}.
--   $$
--
--   For $x\in K$, its one-based rank is $r_K(x)=\mu_x(K)$. The finite set $K[n]$ is constructed by increasing enumeration of $K$; its ownership ratio is $|D\cap K[n]|/n$. No rank is assigned to an output outside $K$.
--
--   For the operational patient-scope run, a switch loss is an input outside the previous end-of-round focus. It is previously unannounced when neither party announced it earlier. Count such distinct integers in $K[n]$ strictly after a specified completed time $T$. The settling predicate records, at every completed time at least $T$, target criticality, inclusion of the target index in the scope, and focus containment in $K$. It is only a predicate; its existence remains a theorem obligation.
--
--   These definitions connect the actual run to Definitions 2.1–2.2 and the analysis of Lemmas 3.12–3.14.
--
--   **Formalization Note** Counts use finite sets; ratios and their liminf are real and bounded in $[0,1]$. A zero denominator gives zero, affecting only finitely many prefixes for infinite $K$. Increasing enumeration uses Mathlib's `Nat.nth`; ranks remain restricted to the subtype $K$. Stream index $t$ is paper round $t+1$, so strict occurrence after completed time $T$ means $T<t+1$.
-- source:
--   Cai, Li, Shen, Wang and Zhang, STOC 2027 submission #335 (October 2026), Definitions 2.1–2.2, printed p.7 (PDF p.9); Definition 3.10, printed p.12 (PDF p.14); proof of Lemma 3.12 and rank convention before Fact 3.13, printed p.15 (PDF p.17); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/335.pdf

import Definitions.Def_DenseLanguageGeneration_PatientScope_algorithm

set_option autoImplicit false
open ActiveLanguageGeneration.Hierarchy
open Filter
noncomputable section

namespace DenseLanguageGeneration.PatientScope

/-- §2 / Definition 2.1, on a fixed run. NR excludes all earlier outputs. -/
def Generates (G : Generator ℕ+) (K : ActiveLanguageGeneration.Hierarchy.Language ℕ+) (a : ℕ → ℕ+) : Prop :=
  ∃ N : ℕ, ∀ t ≥ N, CorrectAt .NR G K a t

/-- Definition 2.2. Existence of a response preceding every input occurrence.
The input at the same round comes first; repeated competitor outputs count once. -/
def defenderOwned (G : Generator ℕ+) (a : ℕ → ℕ+) : Set ℕ+ :=
  {x | ∃ t, outputAt G a t = x ∧ ∀ s ≤ t, a s ≠ x}

/-- The adversary owns an input exactly when no earlier response announced it. -/
def attackerOwned (G : Generator ℕ+) (a : ℕ → ℕ+) : Set ℕ+ :=
  {x | ∃ t, a t = x ∧ ∀ s < t, outputAt G a s ≠ x}

/-- Ambient integer prefix {1,...,n}, empty at n=0. -/
def ambientPrefix (n : ℕ) : Finset ℕ+ := (Finset.range n).image positive

/-- Finite counting, even for arbitrary infinite or noncomputable S. -/
def prefixCount (S : Set ℕ+) (n : ℕ) : ℕ := by
  classical
  exact ((ambientPrefix n).filter (fun x => x ∈ S)).card

/-- Both counts are real numbers. At a zero denominator the ratio is 0.
All ratios lie in [0,1]; for infinite K the denominator eventually is positive. -/
def ratio (G : Generator ℕ+) (K : ActiveLanguageGeneration.Hierarchy.Language ℕ+) (a : ℕ → ℕ+) (n : ℕ) : ℝ :=
  (prefixCount (defenderOwned G a ∩ K.val) n : ℝ) / (prefixCount K.val n : ℝ)

/-- Definition 2.2 uses ambient prefixes, without assuming positive density of K. -/
def lowerDensity (G : Generator ℕ+) (K : ActiveLanguageGeneration.Hierarchy.Language ℕ+) (a : ℕ → ℕ+) : ℝ :=
  Filter.liminf (ratio G K a) atTop

/-- Printed p.15 / PDF p.17: the rank map is defined ONLY on members of K.
Ranks are one-based, in contrast to time and family indices. -/
def rank (K : ActiveLanguageGeneration.Hierarchy.Language ℕ+) (x : K.val) : ℕ :=
  prefixCount K.val x.val.val

/-- K[n], the first n elements of K, in increasing order. Nat.nth uses zero-based
positions in the predicate on positive integers; infinitude is carried by K. -/
def rankPrefix (K : ActiveLanguageGeneration.Hierarchy.Language ℕ+) (n : ℕ) : Finset ℕ+ :=
  (Finset.range n).image (fun j => positive (Nat.nth (fun k => positive k ∈ K.val) j))

/-- Same ownership set, now counted along the rank prefixes for comparison with
Lemma 3.14. The goal itself always uses the ambient-prefix lowerDensity. -/
def rankRatio (G : Generator ℕ+) (K : ActiveLanguageGeneration.Hierarchy.Language ℕ+) (a : ℕ → ℕ+) (n : ℕ) : ℝ := by
  classical
  exact (((rankPrefix K n).filter (fun x => x ∈ defenderOwned G a)).card : ℝ) / (n : ℝ)

/-- Proof of Lemma 3.12: a time furnished by the run, not an algorithm input or
an assumed success property. Target criticality and scope inclusion are the actual
invariants used to obtain the eventual focus-subset time T*. -/
def SettledFrom (L : Family) (i : ℕ) (a : ℕ → ℕ+) (T : ℕ) : Prop :=
  ∀ t ≥ T, Critical L (history a t) i ∧ i < (stateAt L a t).scope ∧
    focusAt L a t ⊆ (L i).val

/-- Definition 3.10. Stream index t is paper round t+1; stateAt t is the
previous end-of-round focus, including the initial focus for the first input. -/
def SwitchLoss (L : Family) (a : ℕ → ℕ+) (t : ℕ) : Prop :=
  a t ∉ focusAt L a t

/-- Previously unannounced BEFORE the current input, hence the adversary owns it.
Future inputs are permitted to equal earlier outputs. -/
def UnannouncedInput (G : Generator ℕ+) (a : ℕ → ℕ+) (t : ℕ) : Prop :=
  (∀ s < t, a s ≠ a t) ∧ (∀ s < t, outputAt G a s ≠ a t)

/-- Count distinct integer losses in a finite rank prefix, not an infinite set of
times. Strictly after paper time T means T < t+1 for stream index t. -/
def lossCount (L : Family) (i : ℕ) (a : ℕ → ℕ+) (T n : ℕ) : ℕ := by
  classical
  exact ((rankPrefix (L i) n).filter (fun x => ∃ t, T < t + 1 ∧ a t = x ∧
    SwitchLoss L a t ∧ UnannouncedInput (generator L) a t)).card

end DenseLanguageGeneration.PatientScope


