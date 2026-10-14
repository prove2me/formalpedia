-- Prove2me | Definitions.Def_FirstPriceLearning_Stochastic_Algorithm3
-- name    : FirstPriceLearning_Stochastic_Algorithm3
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:28:02.243983+00:00
-- url     : https://prove2.me/theorems/0d2935fb-8ade-468f-9dff-954cad3d4a00
-- title:
--   Algorithm 3, p. 17 — arm elimination for partially ordered contextual bandits
-- statement:
--   **Algorithm 3** takes the horizon $T$, contexts $\mathcal C=[M]$, actions $\mathcal A=[K]$, the feedback graph $G$, the partial orders $\preceq_G$ and $\preceq_{\mathcal C}$, a failure probability $\delta\in(0,1)$, and a topological ordering of $\mathcal C$. It keeps an active set $\mathcal A_{\mathrm{act},c}$ and a minimum count $N_c$ per context, an observation count $n_a$ per action (shared by all contexts) and empirical rewards $\bar r_{c,a}$. In round $t$:
--
--   1. ($\star$) receive $c_t$ and play $a_t$ chosen uniformly at random among the actions of $\mathcal A_{\mathrm{act},c_t}$ with no parent in the restriction of $G$ to $\mathcal A_{\mathrm{act},c_t}$;
--   2. observe $r_{t,c,a}$ for all $c$ and all $a\in I_t=\{a_t\}\cup\{a:(a_t,a)\in E\}$ and update $n_a$, $\bar r_{c,a}$;
--   3. for each $c$ in the topological ordering: ($\star\star$) eliminate every $a$ from $\mathcal A_{\mathrm{act},c}$ for which some $c'\preceq_{\mathcal C}c$ has no $a'\in\mathcal A_{\mathrm{act},c'}$ with $a'\preceq_G a$; then, if $\min_{a\in\mathcal A_{\mathrm{act},c}}n_a>N_c$, set $N_c$ to that minimum and keep only the actions with
--   $$
--   \bar r_{c,a}\ \ge\ \max_{a'\in\mathcal A_{\mathrm{act},c}}\bar r_{c,a'}-6\sqrt{\frac{\log(2T)\log(MKT/\delta)}{N_c}}.
--   $$
--
--   The algorithm is defined as a deterministic function of the context sequence, the reward vectors and one uniform $u_t\in[0,1]$ per round.
--
--   **Formalization Note.** The uniform choice in ($\star$) is the $\lfloor u_t n\rfloor$-th of the $n$ candidates in increasing order, which has probability $1/n$ for each candidate when $u_t$ is uniform. The topological ordering is an argument (an enumeration of `Fin M`); the theorems require it to be topological and hold for every such ordering. Off the good event, ($\star\star$) could empty an active set: the minimum over an empty set is $+\infty$ (`⊤ : ℕ∞`), and with no candidate the action $0$ is played. $\bar r_{c,a}=0$ while $n_a=0$, as initialized. The reward vector is an input, but only its entries in $I_t$ are read.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 17, Algorithm 3

import Mathlib
import Definitions.Def_FirstPriceLearning_Stochastic_ContextualBandit

namespace FirstPriceLearning.Stochastic

open MeasureTheory

/-- The inputs of Algorithm 3 (p. 17): the horizon `T`, the failure probability `δ`, the feedback
graph `E` on `𝒜 = Fin K`, the partial order `leC` on `𝒞 = Fin M`, and the "given topological
ordering of `𝒞`" as an enumeration `ord` (the `i`-th context processed is `ord i`; a selection
argument, see `IsTopoOrder`). `hK` makes the action set nonempty. -/
structure Alg3Params (M K : ℕ) where
  T : ℕ
  δ : ℝ
  E : Fin K → Fin K → Prop
  leC : Fin M → Fin M → Prop
  ord : Fin M ≃ Fin M
  hK : 0 < K

/-- `ord` lists the contexts in a topological ordering of `leC`: if `ord i ⪯_𝒞 ord j` then
`i ≤ j`. -/
def IsTopoOrder {M : ℕ} (leC : Fin M → Fin M → Prop) (ord : Fin M ≃ Fin M) : Prop :=
  ∀ i j, leC (ord i) (ord j) → i ≤ j

/-- The state of Algorithm 3 after some rounds: the active sets `𝒜_{act,c}`, the minimum counts
`N_c` (in `ℕ∞`: the minimum over an empty active set is `⊤`, see `ctxStep`), the action counts
`n_a` (shared by all contexts: cross learning) and the reward sums `∑ r_{s,c,a}` over the rounds
`s` in which `a` was observed. -/
structure Alg3State (M K : ℕ) where
  act : Fin M → Finset (Fin K)
  Nmin : Fin M → ℕ∞
  cnt : Fin K → ℕ
  rsum : Fin M → Fin K → ℝ

namespace Alg3

variable {M K : ℕ}

/-- Initialization: `𝒜_{act,c} = 𝒜`, `N_c = 0`, and all (empirical reward, count) pairs `(0, 0)`. -/
def init : Alg3State M K where
  act := fun _ => Finset.univ
  Nmin := fun _ => 0
  cnt := fun _ => 0
  rsum := fun _ _ => 0

/-- The empirical reward `r̄_{c,a} = (∑ observed r_{s,c,a}) / n_a` (it is `0` while `n_a = 0`,
as initialized). -/
noncomputable def empMean (st : Alg3State M K) (c : Fin M) (a : Fin K) : ℝ :=
  st.rsum c a / st.cnt a

open scoped Classical in
/-- The actions of `𝒜_{act,c}` with no parent in the restriction `G_{act,c}` of `G` to
`𝒜_{act,c}`. -/
noncomputable def sources (p : Alg3Params M K) (st : Alg3State M K) (c : Fin M) : Finset (Fin K) :=
  (st.act c).filter (fun a => ∀ a' ∈ st.act c, ¬ p.E a' a)

/-- Line (⋆): the action played in context `c`, a uniformly random element of `sources`, read
off one uniform `u ∈ [0, 1]`: the `⌊u·n⌋`-th element (in increasing order) of the `n` candidates.
Each candidate has probability `1/n` when `u` is uniform. If there is no candidate (an empty
active set, possible only off the good event) the default action `0` is played. -/
noncomputable def chooseAction (p : Alg3Params M K) (st : Alg3State M K) (c : Fin M)
    (u : unitInterval) : Fin K :=
  let l := (sources p st c).sort (· ≤ ·)
  l.getD ⌊(u : ℝ) * l.length⌋₊ ⟨0, p.hK⟩

open scoped Classical in
/-- The feedback step: the learner observes `r_{t,c,a}` for every `c` and every `a ∈ I_t =
{a_t} ∪ {a : (a_t, a) ∈ E}`, and updates the counts and reward sums of exactly those `a`. Entries
of `r` outside `I_t` are never read. -/
noncomputable def observe (p : Alg3Params M K) (st : Alg3State M K) (a : Fin K)
    (r : Fin M → Fin K → ℝ) : Alg3State M K :=
  { st with
    cnt := fun a' => if a' = a ∨ p.E a a' then st.cnt a' + 1 else st.cnt a'
    rsum := fun c a' => if a' = a ∨ p.E a a' then st.rsum c a' + r c a' else st.rsum c a' }

/-- The elimination width `6 √(log(2T) log(MKT/δ) / N_c)`. -/
noncomputable def width (p : Alg3Params M K) (N : ℕ∞) : ℝ :=
  6 * Real.sqrt (Real.log (2 * p.T) * Real.log (M * K * p.T / p.δ) / (N.toNat : ℝ))

open scoped Classical in
/-- The body of the inner loop for context `c`:
* (⋆⋆) remove from `𝒜_{act,c}` every `a` for which some `c' ⪯_𝒞 c` has no `a' ∈ 𝒜_{act,c'}` with
  `a' ⪯_G a` (the active sets of the contexts already processed this round are the updated ones);
* if `min_{a ∈ 𝒜_{act,c}} n_a > N_c`, set `N_c` to that minimum and keep only the actions with
  `r̄_{c,a} ≥ max_{a' ∈ 𝒜_{act,c}} r̄_{c,a'} - 6 √(log(2T) log(MKT/δ) / N_c)`.
The minimum over an empty active set is `⊤` (then the set stays empty). -/
noncomputable def ctxStep (p : Alg3Params M K) (st : Alg3State M K) (c : Fin M) :
    Alg3State M K :=
  let act1 := (st.act c).filter
    (fun a => ∀ c', p.leC c' c → ∃ a' ∈ st.act c', LeG p.E a' a)
  let mn : ℕ∞ := act1.inf (fun a => (st.cnt a : ℕ∞))
  if st.Nmin c < mn then
    let rmax : ℝ := if h : act1.Nonempty then act1.sup' h (empMean st c) else 0
    { st with
      act := Function.update st.act c (act1.filter (fun a => rmax - width p mn ≤ empMean st c a))
      Nmin := Function.update st.Nmin c mn }
  else
    { st with act := Function.update st.act c act1 }

/-- One round after the action `a` has been played and the reward vector `r` drawn: observe,
then run the inner loop over the contexts in the order `ord 0, ord 1, …, ord (M-1)`. -/
noncomputable def roundUpdate (p : Alg3Params M K) (st : Alg3State M K) (a : Fin K)
    (r : Fin M → Fin K → ℝ) : Alg3State M K :=
  (List.finRange M).foldl (fun s i => ctxStep p s (p.ord i)) (observe p st a r)

/-- The state of Algorithm 3 after the first `n` rounds, on the contexts `cs`, the reward vectors
`rs` and the uniforms `us` of the rounds (rounds `n ≥ T` do nothing). The state after `n` rounds
is the paper's state at the end of round `n` (superscript `n`). -/
noncomputable def state (p : Alg3Params M K) {T : ℕ} (cs : Fin T → Fin M)
    (rs : Fin T → Fin M → Fin K → ℝ) (us : Fin T → unitInterval) : ℕ → Alg3State M K
  | 0 => init
  | n + 1 =>
    if h : n < T then
      roundUpdate p (state p cs rs us n)
        (chooseAction p (state p cs rs us n) (cs ⟨n, h⟩) (us ⟨n, h⟩)) (rs ⟨n, h⟩)
    else state p cs rs us n

/-- The actions `a_t` played by Algorithm 3 (round `t` of the paper is `t.val + 1`). -/
noncomputable def actions (p : Alg3Params M K) {T : ℕ} (cs : Fin T → Fin M)
    (rs : Fin T → Fin M → Fin K → ℝ) (us : Fin T → unitInterval) (t : Fin T) : Fin K :=
  chooseAction p (state p cs rs us t.val) (cs t) (us t)

end Alg3

end FirstPriceLearning.Stochastic


