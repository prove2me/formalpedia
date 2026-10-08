-- Prove2me | Definitions.Def_MechanismDesign_Robust_Voting
-- name    : MechanismDesign_Robust_Voting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T05:05:20.901294+00:00
-- url     : https://prove2.me/theorems/f078ca7e-9e05-40a4-91d2-5431f42ad5d1
-- title:
--   Voting with three candidates: unanimity, random dictatorship, random dictatorship with compromise, ex post equity
-- statement:
--   The setting of §10.11: two agents $i \in \{1,2\}$ and three candidates $C = \{a,b,c\}$; outcomes are lotteries $\delta \in \Delta(C)$. Agent $i$ with payoff type $\theta_i$ has a von Neumann–Morgenstern utility $u_i(\theta_i) : C \to \mathbb R$ (private values), evaluated on lotteries by expectation; $u_i(\theta_i)$ never assigns the same value to two candidates; and every such strict utility is $u_i(\theta_i)$ for some payoff type $\theta_i$.
--
--   For a mechanism $(S_1,S_2,g)$ and strategies $\sigma$, the probability of $x$ at the type profile $\tau$ is $\sum_{s} \sigma_1(\tau_1)[s_1]\,\sigma_2(\tau_2)[s_2]\,g(s)[x]$. They satisfy **positive unanimity** (Definition 10.17) if a candidate most preferred by both agents (given their payoff types) is chosen with probability one, and **negative unanimity** if a candidate least preferred by both is chosen with probability zero. They are a **random dictatorship** (Definition 10.18) if there is $p \in [0,1]$ such that for all $\tau$ and $x$ the probability of $x$ equals
--
--   $$\sum_{i=1,2} \mathbf 1_i(x)\, p_i, \qquad p_1 = p,\ p_2 = 1-p,$$
--
--   where $\mathbf 1_i(x) = 1$ iff $x$ is agent $i$'s most preferred candidate given $\hat\theta_i(\tau_i)$.
--
--   **$p$-random dictatorship** (Definition 10.19) is the mechanism with $S_i = C$, $g(s)(x) = \sum_{i : x = s_i} p_i$, together with the strategies in which every type names her most preferred candidate. **$p$-random dictatorship with compromise** (Definition 10.20) has strategies $s_i = (C_i, R_i)$, where $C_i$ is a nonempty set of "acceptable" candidates and $R_i$ a strict ranking of $C$; if $C_1 \cap C_2 = \emptyset$ then $g(s)(x) = \sum_{i : x R_i x'\ \forall x' \in C} p_i$, and otherwise $g(s)(x) = \sum_{i : x R_i x'\ \forall x' \in C_1\cap C_2} p_i$ for $x \in C_1 \cap C_2$ (and $0$ outside). A strategy is **truthful** (p.198) if $C_i$ contains the agent's most preferred candidate and $R_i$ is her true preference. **Ex post equity** (Definition 10.21) scores a candidate $1$ if it is most preferred by both agents, $0$ if it is least preferred by one of them, and $\tfrac12$ otherwise; a lottery is scored by its expected score.
--
--   **Formalization Note** The book's agents $1,2$ are `0, 1 : Fin 2`. A ranking is a bijection `C ≃ Fin 3` (rank `0` is the top), and "$x R_i x'$ for all $x' \in D$" is read as "$x$ is the $R_i$-best element of $D$" (a strict ranking cannot compare $x$ with itself). Mechanisms map strategy profiles directly to lotteries over $C$, as in the book's notation $g(s)[x]$.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, pp.195–200, §10.11, Definitions 10.17–10.21

import Mathlib
import Definitions.Def_MechanismDesign_Robust_Mechanisms

open scoped ENNReal NNReal

namespace MechanismDesign.Robust

universe u v w

/-- The three candidates `C = {a, b, c}` of §10.11 (p.195). -/
inductive Candidate
  | a
  | b
  | c
  deriving DecidableEq, Inhabited

instance : Fintype Candidate :=
  ⟨{Candidate.a, Candidate.b, Candidate.c}, fun x => by cases x <;> simp⟩

/-- The standing assumptions of §10.11 (p.195) on the two agents' payoff types: agent `i`'s
von Neumann–Morgenstern utility over candidates at payoff type `θ_i` is `vu i θ_i`
(private values); it never assigns the same value to two candidates; and every such strict
utility function arises from some payoff type ("the space of payoff types is large"). -/
def IsVotingEnvironment {Θ : Fin 2 → Type u} (vu : ∀ i, Θ i → Candidate → ℝ) : Prop :=
  (∀ i (θi : Θ i), Function.Injective (vu i θi)) ∧
    ∀ i (w : Candidate → ℝ), Function.Injective w → ∃ θi : Θ i, vu i θi = w

/-- The expected utility of a lottery `δ ∈ Δ(C)` is `∑_x δ(x) u_i(θ_i)(x)`; as a utility on
outcomes `x ∈ C` for the general framework: `u_i(x, θ) = vu_i(θ_i)(x)`. -/
def votingUtility {Θ : Fin 2 → Type u} (vu : ∀ i, Θ i → Candidate → ℝ) :
    Fin 2 → Candidate → (∀ i, Θ i) → ℝ :=
  fun i x θ => vu i (θ i) x

/-- A most preferred candidate of a utility function (unique when it is injective). -/
noncomputable def topCand (w : Candidate → ℝ) : Candidate :=
  Classical.choose (Finite.exists_max w)

/-- A least preferred candidate of a utility function (unique when it is injective). -/
noncomputable def bottomCand (w : Candidate → ℝ) : Candidate :=
  Classical.choose (Finite.exists_min w)

variable {Θ : Fin 2 → Type u} {T : Fin 2 → Type v} {S : Fin 2 → Type w}

/-- The probability `p_i` of agent `i` in a random dictatorship: `p_1 = p`, `p_2 = 1 − p` (the
book's agents `1, 2` are `0, 1 : Fin 2`). -/
def dictatorWeight (p : ℝ) (i : Fin 2) : ℝ := if i = 0 then p else 1 - p

/-- **Definition 10.17** (p.195–196) (i) positive unanimity: at every type profile, a candidate
that is most preferred by both agents (given their payoff types) is chosen with probability one;
the probability of `x` is `∑_s σ_1(τ_1)[s_1] σ_2(τ_2)[s_2] g(s)[x]`. -/
def PositiveUnanimity (ts : TypeSpace Θ T) (vu : ∀ i, Θ i → Candidate → ℝ)
    (M : Mechanism S Candidate) (σ : ∀ i, T i → PMF (S i)) : Prop :=
  ∀ (τ : ∀ i, T i) (x : Candidate), (∀ i, x = topCand (vu i (ts.θhat i (τ i)))) →
    eqOutcome M σ τ x = 1

/-- **Definition 10.17** (ii) negative unanimity: a candidate that is least preferred by both
agents is chosen with probability zero. -/
def NegativeUnanimity (ts : TypeSpace Θ T) (vu : ∀ i, Θ i → Candidate → ℝ)
    (M : Mechanism S Candidate) (σ : ∀ i, T i → PMF (S i)) : Prop :=
  ∀ (τ : ∀ i, T i) (x : Candidate), (∀ i, x = bottomCand (vu i (ts.θhat i (τ i)))) →
    eqOutcome M σ τ x = 0

/-- **Definition 10.18** (p.196). The mechanism and equilibrium are a random dictatorship: there
is `p ∈ [0, 1]` such that for every type profile `τ` and candidate `x`, the probability of `x` is
`∑_i 1_i(x) p_i`, where `1_i(x) = 1` iff `x` is agent `i`'s most preferred candidate given
`θ̂_i(τ_i)`, `p_1 = p`, `p_2 = 1 − p`. -/
def IsRandomDictatorship (ts : TypeSpace Θ T) (vu : ∀ i, Θ i → Candidate → ℝ)
    (M : Mechanism S Candidate) (σ : ∀ i, T i → PMF (S i)) : Prop :=
  ∃ p : ℝ, 0 ≤ p ∧ p ≤ 1 ∧ ∀ (τ : ∀ i, T i) (x : Candidate),
    (eqOutcome M σ τ x).toReal =
      ∑ i, (if x = topCand (vu i (ts.θhat i (τ i))) then dictatorWeight p i else 0)

/-- The coin that shows `true` (agent `1` is dictator) with probability `p` and `false` with
probability `1 − p`. -/
noncomputable def coin (p : ℝ≥0) (hp : p ≤ 1) : PMF Bool :=
  PMF.ofFintype (fun bit => if bit then (p : ℝ≥0∞) else 1 - (p : ℝ≥0∞)) (by
    simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false]
    exact add_tsub_cancel_of_le (by exact_mod_cast hp))

/-- **Definition 10.19** (p.197), the mechanism of `p`-random dictatorship: `S_i = C` and
`g(s)(x) = ∑_{i : x = s_i} p_i`. -/
noncomputable def rdMechanism (p : ℝ≥0) (hp : p ≤ 1) : Mechanism (fun _ : Fin 2 => Candidate) Candidate :=
  ⟨fun _ => ⟨Candidate.a⟩, fun s => (coin p hp).map (fun bit => if bit then s 0 else s 1)⟩

/-- **Definition 10.19** (iii), the equilibrium of `p`-random dictatorship: every type names her
most preferred candidate. -/
noncomputable def rdStrategy (ts : TypeSpace Θ T) (vu : ∀ i, Θ i → Candidate → ℝ) :
    ∀ i, T i → PMF Candidate :=
  fun i τi => PMF.pure (topCand (vu i (ts.θhat i τi)))

/-- A strict ranking of the candidates: `r x` is the rank of `x` (`0` is the top). `x R x'` iff
`r x < r x'`. -/
abbrev Ranking : Type := Candidate ≃ Fin 3

/-- The `R`-best candidate of a set `D` (the `x ∈ D` with `x R x'` for all other `x' ∈ D`);
only used for nonempty `D`. -/
noncomputable def bestIn (r : Ranking) (D : Finset Candidate) : Candidate :=
  if h : D.Nonempty then Classical.choose (D.exists_min_image r h) else Candidate.a

/-- A strategy of `p`-random dictatorship with compromise: a nonempty set `C_i` of acceptable
candidates and a strict ranking `R_i`. -/
abbrev CompromiseStrategy : Type := {D : Finset Candidate // D.Nonempty} × Ranking

/-- **Definition 10.20** (p.197). `p`-random dictatorship with compromise: `S_i = 𝒞 × ℛ`; if
`C_1 ∩ C_2 = ∅` then `g(s, x) = ∑_{i : x R_i x' ∀ x' ∈ C} p_i`; otherwise, for `x ∈ C_1 ∩ C_2`,
`g(s, x) = ∑_{i : x R_i x' ∀ x' ∈ C_1 ∩ C_2} p_i` (and `0` outside `C_1 ∩ C_2`). -/
noncomputable def compromiseMechanism (p : ℝ≥0) (hp : p ≤ 1) :
    Mechanism (fun _ : Fin 2 => CompromiseStrategy) Candidate :=
  ⟨fun _ => ⟨(⟨Finset.univ, Finset.univ_nonempty⟩, Equiv.refl _ |>.trans (Fintype.equivFin Candidate))⟩,
    fun s =>
      let D : Finset Candidate :=
        if (s 0).1.1 ∩ (s 1).1.1 = ∅ then Finset.univ else (s 0).1.1 ∩ (s 1).1.1
      (coin p hp).map (fun bit => if bit then bestIn (s 0).2 D else bestIn (s 1).2 D)⟩

/-- A truthful strategy (p.198) of a type with utility `w`: the acceptable set contains the most
preferred candidate and the ranking is the true preference. -/
def IsTruthfulStrategy (w : Candidate → ℝ) (s : CompromiseStrategy) : Prop :=
  topCand w ∈ s.1.1 ∧ ∀ x y, s.2 x < s.2 y ↔ w y < w x

/-- Every type plays (only) truthful strategies. -/
def IsTruthfulProfile (ts : TypeSpace Θ T) (vu : ∀ i, Θ i → Candidate → ℝ)
    (σ : ∀ i, T i → PMF CompromiseStrategy) : Prop :=
  ∀ i (τi : T i) s, σ i τi s ≠ 0 → IsTruthfulStrategy (vu i (ts.θhat i τi)) s

/-- **Definition 10.21** (p.200), ex post equity of a candidate `x` for agents with utilities
`w 0`, `w 1`: `1` if `x` is most preferred by both, `0` if it is least preferred by one of them,
`0.5` otherwise. -/
noncomputable def equityScore (w : Fin 2 → Candidate → ℝ) (x : Candidate) : ℝ :=
  if ∀ i, x = topCand (w i) then 1 else if ∃ i, x = bottomCand (w i) then 0 else 1 / 2

/-- **Definition 10.21**, ex post equity welfare at `τ`: the expected equity score of the
equilibrium lottery at `τ`. -/
noncomputable def equityWelfare (ts : TypeSpace Θ T) (vu : ∀ i, Θ i → Candidate → ℝ)
    (M : Mechanism S Candidate) (σ : ∀ i, T i → PMF (S i)) (τ : ∀ i, T i) : ℝ :=
  ∑ x, (eqOutcome M σ τ x).toReal * equityScore (fun i => vu i (ts.θhat i (τ i))) x

end MechanismDesign.Robust


