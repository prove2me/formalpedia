-- Prove2me | Definitions.Def_LogitRankDistill_Algorithms
-- name    : LogitRankDistill_Algorithms
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:58:54.803907+00:00
-- url     : https://prove2.me/theorems/8df2229e-2567-44ab-b606-5e61b05d46a7
-- title:
--   Algorithm 1 with DistSpanner (Algorithm 3), the program (14a)–(14c), G_t and Q_t, the events E_spanner and E_oracle, Algorithm 2 and its output law M̂, and the §5.2 parameter settings
-- statement:
--   **Parameters** (§5.2, Require line of Algorithm 1): the number of epochs $K$, the number $n$ of trajectories, $\beta$, the threshold $\gamma_{\mathrm{thres}}$, the spanner parameters $\eta,\delta$, and DistSpanner's sample count $m(N)$ for dimension $N$ (Algorithm 3: $m=\Theta((N/\eta)^2\log(N/(\delta\eta)))$, called with $\eta,\delta/(10KT)$).
--
--   **The program (14a)–(14c)** at step $t$ for $y_{1:t}$, sets $\hat F_s$ and vectors $L_{s,1},\dots,L_{s,\bar d}$: variables $c_s\in\mathbb R^{\bar d}$ ($s\in[t]$) and $\hat L_s\in\mathbb R^{\hat F_s}$ with $\hat L_s(f)=\sum_ic_{s,i}L_{s,i}(f)$ on $\hat F_s$, $c_1=e_1$, $\|c_s\|_\infty\le\beta$, $\hat L_{s+1}(f)=\sum_ic_{s,i}L_{s,i}(y_s\circ f)$ on $\hat F_{s+1}$. $G_t$ (Definition 5.4) is the set of $y_{1:t}$ for which it is feasible.
--
--   **Algorithm 1.** Line 1 draws $y\sim M$ and sets $\hat F_t=\{y_t\}$. Each epoch $k=1,\dots,K$: $\tilde F_t=\hat F_t\cup(\Sigma\circ\hat F_{t+1})$, $\bar d=\max_t|\tilde F_t|$; $L_{1,i}=L_{\mathrm{oracle}}(\cdot)$ on $\tilde F_1$; for $t=2,\dots,T$, DistSpanner draws $m(|\tilde F_t|)$ prefixes $y_{1:t-1}\sim M$, forms the vectors $(L_{\mathrm{oracle}}(y_{1:t-1}\circ f))_{f\in\tilde F_t}$ and returns a 2-barycentric spanner of them of size $|\tilde F_t|$, padded to $\bar d$ vectors $L_{t,i}=L_{\mathrm{oracle}}(h_{t,i}\circ\cdot)$; Line 8 draws $n$ trajectories; for $t=1,\dots,T-1$ the program is solved for every trajectory (infeasible for some: next epoch), then Line 14 tests $|\hat L_{t,s,u}(y_{s:r-1,u}\circ y'_r)-\sum_ic_{t,s,u,i}L_{s,i}(y_{s:r-1,u}\circ y'_r)|>\gamma_{\mathrm{thres}}$, with the Line 13 extension $\hat L_{t,s,u}(f)=\sum_ic_{t,s-1,u,i}L_{s-1,i}(y_{s-1,u}\circ f)$; a violation adds the witness $y_{s:r-1,u}\circ y'_r$ to $\hat F_s$ and ends the epoch. If every step passes, Line 17 stores $L_{\mathrm{oracle}}(h_{t,i}\circ f)$ for $f\in\Sigma$ and $f\in\Sigma^2$ and Line 18 returns $(\hat F_t,\tilde F_t,\bar d,$ the values$)$. If no epoch returns, the output is $\bot$.
--
--   **Choice rules.** Three choices are left open by the paper: the spanner (Algorithm 3, Line 2), the solution of the program (Line 10 of Algorithm 1 and Line 3 of Algorithm 2: one shared rule, a function of the program's data), and the Line 15 witness. A rule set is **admissible** if the spanner is a 2-barycentric spanner of the drawn vectors, the solution rule returns a feasible point exactly when the program is feasible, and the witness is a violating one.
--
--   **Events.** $E_{\mathrm{spanner}}$ (§5.4): at every executed epoch and every $t\in\{2,\dots,T\}$, $L_{t,1:\bar d}$ is an $(\eta,\beta)$-distributional spanner for $P_t$, the law of $(L_{\mathrm{oracle}}(y_{1:t-1}\circ f))_{f\in\tilde F_t}$ under $y\sim M$. $E_{\mathrm{oracle}}$ (Definition 5.6): the execution trace is $\varepsilon_{\mathrm{apx}}$-approximately $\alpha$-bounded of rank $d$. The integrand of (21) and the integrand of Lemma 5.8 are expectations under $Q_t(L_{1:t,1:\bar d})$ (Definition 5.5): draw $y\sim M$ and take the rule's solution of the program at $y_{1:t}$ ($0$ if infeasible).
--
--   **Algorithm 2 and $\hat M$.** On the returned data, $\hat P_1\propto\exp(L_{1,1}(\cdot))$; for $t=1,\dots,T-1$ solve the program at the sampled $y_{1:t}$ (infeasible: fail), set $\hat L_{t,t+1}(y)=\sum_ic_{t,i}L_{t,i}(y_t\circ y)$ and sample $y_{t+1}\sim\mathrm{softmax}(\hat L_{t,t+1})$. $\hat M$ is its output law on $\Sigma^T\cup\{\mathrm{fail}\}$; $M$ is compared to it on the same space.
--
--   **§5.2 settings:** $\beta=2$, $\gamma=4K\varepsilon_{\mathrm{apx}}$, $\gamma_{\mathrm{thres}}=\gamma\sqrt{C_{5.1}d\log(2\beta K\alpha^2/\gamma)}$, $K=\lceil C_KTd\log(\beta d\alpha T/(\varepsilon_{\mathrm{apx}}\delta))\rceil$, $n=\lceil C_n\log(TK/\delta)/\gamma_{\mathrm{thres}}\rceil$, $\eta=\varepsilon/(3T^2n)$, $m(N)=\lceil C_m(N/\eta)^2\log(N/(\delta'\eta))\rceil$, $\delta'=\delta/(10KT)$.
--
--   **Formalization Note.** A run reads a stream $\omega:\mathbb N\to\Sigma^T$ of draws (Line 1, then per epoch the DistSpanner draws for $t=2,\dots,T$ and the $n$ Line 8 draws); `streamLaw M` makes the cells i.i.d. $\sim M$. Every evaluation of $L_{\mathrm{oracle}}$ is one recorded oracle call (the paper's count). Readings: $\hat F_{T+1}=\emptyset$; DistSpanner's spanner may repeat indices and is padded with its first member; Line 14 ranges over $2\le s\le t$ (at $s=1$ the difference is $0$, at $s=t+1$ there is no $c_{t+1}$); Line 17 also stores the length-2 futures that Algorithm 2 Line 6 reads (finding I5); $\bot$ and fail are `none`. Lean's $\log$ is `Real.log` ($\log x=0$ for $x\le0$).
-- source:
--   Golowich, Liu, Shetty, Provably Distilling from Modern Language Models via Low Logit Rank, manuscript of November 3, 2026 (arXiv:2512.09892; sha256 2ce0606e…), pp. 19–20 Algorithms 1, 2; p. 23 Algorithm 3 and §5.2; pp. 23–24 Eqs. (14a)–(14c), Definitions 5.4–5.6; p. 24 E_spanner

import Mathlib
import Definitions.Def_LogitRankDistill_Models
import Definitions.Def_LogitRankDistill_Spanners

namespace LogitRankDistill

/-!
# Algorithm 1 (learning), DistSpanner (Algorithm 3), the program (14a)–(14c) and Algorithm 2

Golowich, Liu, Shetty, *Provably Distilling from Modern Language Models via Low Logit Rank*,
manuscript of November 3, 2026 (arXiv:2512.09892; sha256 2ce0606e…): Algorithm 1 (p. 19),
Algorithm 2 (p. 20), Algorithm 3 (p. 23), §5.2 (parameters, p. 23), §5.3 (the program
(14a)–(14c), Definitions 5.4–5.6, pp. 23–24), §5.4 (`E_spanner`, p. 24).

**Randomness.** All randomness of Algorithm 1 is in its draws from `M`. A run reads a stream
`ω : ℕ → (Fin T → Tok)` of full sequences: `ω 0` is the Line 1 draw; each epoch then reads, in
order, the `m(|F̃_t|)` draws of DistSpanner for `t = 2, …, T`, then the `n` draws of Line 8. Under
`streamLaw M` the cells are i.i.d. `∼ M`, so the stream is the law of fresh draws.

**Choice rules.** The paper leaves three choices open: which 2-barycentric spanner DistSpanner
returns (Algorithm 3, Line 2), which solution of the program is taken (Line 10 of Algorithm 1 and
Line 3 of Algorithm 2: the *same* rule, a function of the program's data), and which witness Line 15
adds. `Rules` holds one deterministic rule for each, and `Rules.Admissible` says each picks what
the paper allows.

**Oracle calls.** Every evaluation of `L_oracle(y_{1:t})` is one call `O(y_{1:t−1})`, recorded in
the trace (the paper's count, "1 query per future", proof of Lemma 5.10).

**Readings** (see the mission's Formalization scope):
* `F̂_{T+1} = ∅`, so `F̃_T = F̂_T`.
* DistSpanner's `m` is a parameter `m : ℕ → ℕ` of the dimension `N = |F̃_t|`; its spanner may repeat
  indices; it is padded to `d̄` vectors by repeating its first member.
* Line 14 ranges over `2 ≤ s ≤ t`, `s ≤ r ≤ t + 1`: at `s = 1` the tested difference is
  `L̂_1 − ∑_i c_{1,i} L_{1,i} = 0` (as `c_1 = e_1`, `L_{1,i} = L_oracle(·)`), and at `s = t + 1` the
  coefficients `c_{t+1}` do not exist. `L̂_{t,s,u}` is extended to all futures by Line 13.
* Line 17 stores `L_oracle(h_{t,i} ∘ f)` for `f ∈ Σ` (every `t`) and `f ∈ Σ²` (`t ≤ T − 1`), the
  values Algorithm 2, Line 6 reads (finding I5).
* Algorithm 1 returns `none` (`⊥`) if no epoch returns; Algorithm 2's `fail` is `none` in the
  output law on `Option (Fin T → Tok)`.
-/

open Classical

variable {Tok : Type*} [Fintype Tok] [DecidableEq Tok]

/-- The parameters of Algorithm 1 (Require line, p. 19; §5.2): the number of epochs `K`, the number
`n` of Line 8 samples, `β` of (10b), the threshold `γ_thres` of Line 14, the spanner parameters `η`
and `δ` (DistSpanner is called with `η, δ/(10KT)`), and DistSpanner's sample count `m(N)` for
dimension `N` (Algorithm 3, Line 1: `m = Θ((N/η)² log(N/(δη)))`). -/
structure Params where
  /-- number of epochs -/
  K : ℕ
  /-- number of trajectories drawn on Line 8 -/
  n : ℕ
  /-- coefficient bound of (10b)/(14b) -/
  β : ℝ
  /-- threshold of Line 14 -/
  γthres : ℝ
  /-- spanner mass parameter -/
  η : ℝ
  /-- failure-probability parameter -/
  δ : ℝ
  /-- DistSpanner's number of samples, as a function of the dimension `N = |F̃_t|` -/
  m : ℕ → ℕ

/-- The data defining the program (14a)–(14c) at step `t` (§5.3): the symbols `ys = y_{1:t}`, the
sets `F̂_s`, the number `d̄` of spanner vectors, the vectors `L_{s,i}` as `L s i f` (the algorithm
passes their values on `F̃_s` and `0` elsewhere), and `β`. Indices `i ∈ [d̄]` are `0, …, d̄ − 1`. -/
structure ProgData (Tok : Type*) where
  /-- the step `t` -/
  t : ℕ
  /-- the prefix `y_{1:t}` -/
  ys : List Tok
  /-- the sets of futures `F̂_s` -/
  Fhat : ℕ → Finset (List Tok)
  /-- the number `d̄` of spanner vectors -/
  dbar : ℕ
  /-- the spanner vectors `L_{s,i}(f)` -/
  L : ℕ → ℕ → List Tok → ℝ
  /-- the coefficient bound `β` -/
  β : ℝ

/-- `c = (c_{s,i})` is a feasible point of the program (14a)–(14c). The variables `L̂_s` are
determined by `c` through (14a) and (14c), so feasibility is: `c_1 = e_1`, `‖c_s‖_∞ ≤ β` for
`s ∈ [t]` (14b), and, for `s ∈ [t − 1]` and `f ∈ F̂_{s+1}`, the two values of `L̂_{s+1}(f)` agree:
`∑_i c_{s+1,i} L_{s+1,i}(f) = ∑_i c_{s,i} L_{s,i}(y_s ∘ f)`. (Then `L̂_s(f) := ∑_i c_{s,i} L_{s,i}(f)`
on `F̂_s` and `L̂_{t+1}(f) := ∑_i c_{t,i} L_{t,i}(y_t ∘ f)` on `F̂_{t+1}` solve (14a), (14c).) -/
def ProgData.Feasible (D : ProgData Tok) (c : ℕ → ℕ → ℝ) : Prop :=
  0 < D.dbar ∧ (∀ i < D.dbar, c 1 i = if i = 0 then 1 else 0) ∧
  (∀ s, 1 ≤ s → s ≤ D.t → ∀ i < D.dbar, |c s i| ≤ D.β) ∧
  ∀ s, 1 ≤ s → s + 1 ≤ D.t → ∀ f ∈ D.Fhat (s + 1),
    ∑ i ∈ Finset.range D.dbar, c (s + 1) i * D.L (s + 1) i f =
      ∑ i ∈ Finset.range D.dbar, c s i * D.L s i ((D.ys.drop (s - 1)).take 1 ++ f)

/-- `y_{1:t} ∈ G_t(L_{1:t,1:d̄})` (Definition 5.4): the program is feasible. -/
def ProgData.InG (D : ProgData Tok) : Prop :=
  ∃ c, D.Feasible c

/-- The three choice rules left open by the paper. `span k t F m w` returns the indices
`i ↦ j_i` (for `i < |F|`) of the spanner chosen among the DistSpanner samples `w_0, …, w_{m−1}`
(vectors on `F`) at epoch `k`, step `t`; `lp D` returns a solution `c` of the program with data
`D` or `none`; `wit k t W` picks the Line 15 witness `(s, y_{s:r−1,u} ∘ y'_r)` from the set `W` of
violating ones. -/
structure Rules (Tok : Type*) where
  /-- DistSpanner's choice of spanner (Algorithm 3, Line 2) -/
  span : ℕ → ℕ → Finset (List Tok) → ℕ → (ℕ → List Tok → ℝ) → ℕ → ℕ
  /-- the solution rule of the program, shared by Algorithm 1 (Line 10) and Algorithm 2 (Line 3) -/
  lp : ProgData Tok → Option (ℕ → ℕ → ℝ)
  /-- the choice of witness on Line 15 -/
  wit : ℕ → ℕ → Finset (ℕ × List Tok) → ℕ × List Tok

/-- The rules choose what the paper allows: the spanner indices lie among the `m ≥ 1` samples and
the chosen vectors form a 2-barycentric spanner of the samples (Algorithm 3, Line 2); the solution
rule returns a feasible point whenever the program is feasible and `none` exactly when it is
infeasible; the witness rule returns an element of any nonempty set of witnesses. -/
def Rules.Admissible (R : Rules Tok) : Prop :=
  (∀ (k t : ℕ) (F : Finset (List Tok)) (m : ℕ) (w : ℕ → List Tok → ℝ), 0 < m →
      (∀ i < F.card, R.span k t F m w i < m) ∧
      IsBarySpanner 2 (fun (i : Fin F.card) (f : F) => w (R.span k t F m w i) f)
        {v | ∃ j < m, v = fun f : F => w j f}) ∧
  (∀ D : ProgData Tok, match R.lp D with
      | some c => D.Feasible c
      | none => ∀ c, ¬ D.Feasible c) ∧
  ∀ (k t : ℕ) (W : Finset (ℕ × List Tok)), W.Nonempty → R.wit k t W ∈ W

/-- `F̃_t = F̂_t ∪ (Σ ∘ F̂_{t+1})` (Algorithm 1, Line 3). -/
def tilde (Fhat : ℕ → Finset (List Tok)) (t : ℕ) : Finset (List Tok) :=
  Fhat t ∪ Finset.univ.biUnion (fun y : Tok => (Fhat (t + 1)).image (fun f => y :: f))

/-- How an epoch ends: the program is infeasible at step `t` (Line 11), the Line 14 test fires at
step `t` and the witness `(s, f)` is added to `F̂_s` (Line 15), or every step passes (Line 18). -/
inductive Outcome (Tok : Type*)
  | infeasible (t : ℕ)
  | violated (t s : ℕ) (f : List Tok)
  | passed

/-- The data returned by Algorithm 1 (Line 18): the sets `F̂_t`, `F̃_t`, the number `d̄`, and the
values `L_{t,i}(f)` (as `vals t i f`) on `F̃_t` and on the Line 17 futures; `0` elsewhere. -/
structure Learned (Tok : Type*) where
  /-- the sets `F̂_t` -/
  Fhat : ℕ → Finset (List Tok)
  /-- the sets `F̃_t` -/
  Ftil : ℕ → Finset (List Tok)
  /-- the number of spanner vectors `d̄` -/
  dbar : ℕ
  /-- the stored values `L_{t,i}(f)` -/
  vals : ℕ → ℕ → List Tok → ℝ

/-- The context of one run of Algorithm 1: the horizon `T`, the logit oracle `O`, the stream `ω`
of draws from `M`, the parameters and the choice rules. -/
structure Ctx (Tok : Type*) where
  /-- the sequence length -/
  T : ℕ
  /-- the logit oracle -/
  O : List Tok → Tok → ℝ
  /-- the stream of draws from `M` -/
  ω : ℕ → Fin T → Tok
  /-- the parameters -/
  p : Params
  /-- the choice rules -/
  R : Rules Tok

namespace Ctx

variable (C : Ctx Tok)

/-- `d̄ = max_{t ∈ [T]} |F̃_t|` (Line 3). -/
def dbar (Fhat : ℕ → Finset (List Tok)) : ℕ :=
  (Finset.Icc 1 C.T).sup fun t => (tilde Fhat t).card

/-- Stream position of the first DistSpanner draw at step `t ≥ 2` of an epoch started at `cur`. -/
def spanOff (Fhat : ℕ → Finset (List Tok)) (cur t : ℕ) : ℕ :=
  cur + ∑ t' ∈ Finset.Ico 2 t, C.p.m (tilde Fhat t').card

/-- DistSpanner's `j`-th sample vector at step `t` (Line 4): `f ↦ L_oracle(y_{1:t−1} ∘ f)`. -/
noncomputable def spanVec (Fhat : ℕ → Finset (List Tok)) (cur t : ℕ) : ℕ → List Tok → ℝ :=
  fun j f => Lor C.O (pre (C.ω (C.spanOff Fhat cur t + j)) (t - 1) ++ f)

/-- The sample indices chosen by DistSpanner at epoch `k`, step `t`. -/
noncomputable def sel (k : ℕ) (Fhat : ℕ → Finset (List Tok)) (cur t : ℕ) : ℕ → ℕ :=
  C.R.span k t (tilde Fhat t) (C.p.m (tilde Fhat t).card) (C.spanVec Fhat cur t)

/-- The history `h_{t,i}` of the `i`-th spanner vector (`L_{t,i} = L_oracle(h_{t,i} ∘ ·)`): empty
for `t = 1` (Line 5); for `t ≥ 2` the prefix `y_{1:t−1}` of the chosen DistSpanner sample, padded
with duplicates of the first one for `i ≥ |F̃_t|` (Line 7). -/
noncomputable def hist (k : ℕ) (Fhat : ℕ → Finset (List Tok)) (cur t i : ℕ) : List Tok :=
  if t ≤ 1 then [] else
    pre (C.ω (C.spanOff Fhat cur t +
      C.sel k Fhat cur t (if i < (tilde Fhat t).card then i else 0))) (t - 1)

/-- Stream position of the first Line 8 draw. -/
def line8 (Fhat : ℕ → Finset (List Tok)) (cur : ℕ) : ℕ :=
  C.spanOff Fhat cur (C.T + 1)

/-- The vectors `L_{s,i}` on `F̃_s` as passed to the program (`0` off `F̃_s`). -/
noncomputable def Lmask (k : ℕ) (Fhat : ℕ → Finset (List Tok)) (cur : ℕ) :
    ℕ → ℕ → List Tok → ℝ :=
  fun s i f => if f ∈ tilde Fhat s then Lor C.O (C.hist k Fhat cur s i ++ f) else 0

/-- The program's data at step `t` for the prefix `ys`. -/
noncomputable def prog (k : ℕ) (Fhat : ℕ → Finset (List Tok)) (cur t : ℕ) (ys : List Tok) :
    ProgData Tok :=
  ⟨t, ys, Fhat, C.dbar Fhat, C.Lmask k Fhat cur, C.p.β⟩

/-- The `u`-th Line 8 trajectory `y_{1:T,u}`. -/
def traj (Fhat : ℕ → Finset (List Tok)) (cur u : ℕ) : Fin C.T → Tok :=
  C.ω (C.line8 Fhat cur + u)

/-- The solution chosen on Line 10 for trajectory `u` at step `t`. -/
noncomputable def sol (k : ℕ) (Fhat : ℕ → Finset (List Tok)) (cur t u : ℕ) :
    Option (ℕ → ℕ → ℝ) :=
  C.R.lp (C.prog k Fhat cur t (pre (C.traj Fhat cur u) t))

/-- The tested difference of Line 14 for coefficients `c`, trajectory `x`, index `s ≥ 2` and
future `f`: `L̂_{t,s,u}(f) − ∑_i c_{s,i} L_{s,i}(f)` with the Line 13 extension
`L̂_{t,s,u}(f) = ∑_i c_{s−1,i} L_{s−1,i}(y_{s−1,u} ∘ f)` and `L_{s,i}(f) = L_oracle(h_{s,i} ∘ f)`. -/
noncomputable def gap (k : ℕ) (Fhat : ℕ → Finset (List Tok)) (cur : ℕ) (c : ℕ → ℕ → ℝ)
    (x : Fin C.T → Tok) (s : ℕ) (f : List Tok) : ℝ :=
  ∑ i ∈ Finset.range (C.dbar Fhat),
      c (s - 1) i * Lor C.O (C.hist k Fhat cur (s - 1) i ++ seg x (s - 1) (s - 1) ++ f) -
    ∑ i ∈ Finset.range (C.dbar Fhat), c s i * Lor C.O (C.hist k Fhat cur s i ++ f)

/-- Line 11: the program is infeasible for some `u ∈ [n]` at step `t`. -/
def infeasAt (k : ℕ) (Fhat : ℕ → Finset (List Tok)) (cur t : ℕ) : Prop :=
  ∃ u < C.p.n, C.sol k Fhat cur t u = none

/-- The witnesses `(s, y_{s:r−1,u} ∘ y'_r)` violating the Line 14 test at step `t`. -/
noncomputable def witnesses (k : ℕ) (Fhat : ℕ → Finset (List Tok)) (cur t : ℕ) :
    Finset (ℕ × List Tok) :=
  (Finset.range C.p.n).biUnion fun u =>
    (Finset.Icc 2 t).biUnion fun s =>
      (Finset.Icc s (t + 1)).biUnion fun r =>
        ((Finset.univ : Finset Tok).filter fun y' =>
            C.p.γthres < |C.gap k Fhat cur ((C.sol k Fhat cur t u).getD 0) (C.traj Fhat cur u) s
              (seg (C.traj Fhat cur u) s (r - 1) ++ [y'])|).image
          fun y' => (s, seg (C.traj Fhat cur u) s (r - 1) ++ [y'])

/-- The oracle queries of the Line 14 test at step `t` (two `L_oracle` evaluations per
`u, s, r, y'_r, i`). -/
noncomputable def testQueries (k : ℕ) (Fhat : ℕ → Finset (List Tok)) (cur t : ℕ) :
    List (List Tok) :=
  (List.range C.p.n).flatMap fun u =>
    (List.range' 2 (t - 1)).flatMap fun s =>
      (List.range' s (t + 2 - s)).flatMap fun r =>
        (Finset.univ : Finset Tok).toList.flatMap fun _ =>
          (List.range (C.dbar Fhat)).flatMap fun i =>
            [C.hist k Fhat cur (s - 1) i ++ seg (C.traj Fhat cur u) (s - 1) (s - 1) ++
                seg (C.traj Fhat cur u) s (r - 1),
              C.hist k Fhat cur s i ++ seg (C.traj Fhat cur u) s (r - 1)]

/-- The first step `t ∈ [T − 1]` at which the epoch stops (Line 11 or Line 14), if any. -/
noncomputable def firstBad (k : ℕ) (Fhat : ℕ → Finset (List Tok)) (cur : ℕ) : Option ℕ :=
  (List.range' 1 (C.T - 1)).find? fun t =>
    decide (C.infeasAt k Fhat cur t ∨ (C.witnesses k Fhat cur t).Nonempty)

/-- How the epoch ends. -/
noncomputable def outcome (k : ℕ) (Fhat : ℕ → Finset (List Tok)) (cur : ℕ) : Outcome Tok :=
  match C.firstBad k Fhat cur with
  | none => Outcome.passed
  | some t =>
      if C.infeasAt k Fhat cur t then Outcome.infeasible t
      else Outcome.violated t (C.R.wit k t (C.witnesses k Fhat cur t)).1
        (C.R.wit k t (C.witnesses k Fhat cur t)).2

/-- The steps at which the Line 14 test is evaluated. -/
noncomputable def testedSteps (k : ℕ) (Fhat : ℕ → Finset (List Tok)) (cur : ℕ) : List ℕ :=
  match C.firstBad k Fhat cur with
  | none => List.range' 1 (C.T - 1)
  | some t => if C.infeasAt k Fhat cur t then List.range' 1 (t - 1) else List.range' 1 t

/-- All oracle queries of an epoch, in order: Line 5 (`L_oracle(f)`, `f ∈ F̃_1`), the DistSpanner
sample vectors (Line 7), the Line 14 tests, and, if the epoch passes, Line 17. -/
noncomputable def epochQueries (k : ℕ) (Fhat : ℕ → Finset (List Tok)) (cur : ℕ) :
    List (List Tok) :=
  (tilde Fhat 1).toList.map (fun f => f.dropLast) ++
  ((List.range' 2 (C.T - 1)).flatMap fun t =>
    (List.range (C.p.m (tilde Fhat t).card)).flatMap fun j =>
      (tilde Fhat t).toList.map fun f =>
        (pre (C.ω (C.spanOff Fhat cur t + j)) (t - 1) ++ f).dropLast) ++
  ((C.testedSteps k Fhat cur).flatMap fun t => C.testQueries k Fhat cur t) ++
  (match C.outcome k Fhat cur with
    | Outcome.passed =>
        (List.range' 1 C.T).flatMap fun t =>
          (List.range (C.dbar Fhat)).flatMap fun i =>
            ((Finset.univ : Finset Tok).toList.map fun _ => C.hist k Fhat cur t i) ++
            (if t + 1 ≤ C.T then
              (Finset.univ : Finset Tok).toList.flatMap fun y =>
                (Finset.univ : Finset Tok).toList.map fun _ => C.hist k Fhat cur t i ++ [y]
            else [])
    | _ => [])

/-- The data returned on Line 18 if the epoch passes. -/
noncomputable def learned (k : ℕ) (Fhat : ℕ → Finset (List Tok)) (cur : ℕ) : Learned Tok :=
  ⟨Fhat, tilde Fhat, C.dbar Fhat, fun s i f =>
    if f ∈ tilde Fhat s ∨ f.length = 1 ∨ (f.length = 2 ∧ s + 1 ≤ C.T) then
      Lor C.O (C.hist k Fhat cur s i ++ f) else 0⟩

end Ctx

/-- The record of one epoch `k` of a run: the sets `F̂_t` at its start, the stream position `cur`
of its first draw, how it ended and the oracle queries it made. -/
structure Epoch (Tok : Type*) where
  /-- the epoch index `k` -/
  k : ℕ
  /-- the sets `F̂_t` during the epoch -/
  Fhat : ℕ → Finset (List Tok)
  /-- the stream position of its first draw -/
  cur : ℕ
  /-- how it ended -/
  outcome : Outcome Tok
  /-- its oracle queries -/
  queries : List (List Tok)

/-- The state of Algorithm 1 between epochs. -/
structure AlgState (Tok : Type*) where
  /-- current sets `F̂_t` -/
  Fhat : ℕ → Finset (List Tok)
  /-- next unread stream position -/
  cur : ℕ
  /-- all oracle queries so far -/
  trace : List (List Tok)
  /-- the epochs executed so far -/
  epochs : List (Epoch Tok)
  /-- the returned data, once an epoch passed -/
  out : Option (Learned Tok)
  /-- whether the algorithm has returned -/
  stopped : Bool

namespace Ctx

variable (C : Ctx Tok)

/-- Line 1: `F̂_t ← {y_t}` for one draw `y_{1:T} = ω 0`, `t ∈ [T]`. -/
def initState : AlgState Tok :=
  ⟨fun t => if 1 ≤ t ∧ t ≤ C.T then {seg (C.ω 0) t t} else ∅, 1, [], [], none, false⟩

/-- One epoch `k` (Lines 3–18). -/
noncomputable def epochStep (st : AlgState Tok) (k : ℕ) : AlgState Tok :=
  if st.stopped then st else
    let o := C.outcome k st.Fhat st.cur
    { Fhat := match o with
        | Outcome.violated _ s f => Function.update st.Fhat s (insert f (st.Fhat s))
        | _ => st.Fhat
      cur := C.line8 st.Fhat st.cur + C.p.n
      trace := st.trace ++ C.epochQueries k st.Fhat st.cur
      epochs := st.epochs ++ [⟨k, st.Fhat, st.cur, o, C.epochQueries k st.Fhat st.cur⟩]
      out := match o with
        | Outcome.passed => some (C.learned k st.Fhat st.cur)
        | _ => none
      stopped := match o with
        | Outcome.passed => true
        | _ => false }

/-- The final state of Algorithm 1 after the epochs `k = 1, …, K`. -/
noncomputable def run : AlgState Tok :=
  (List.range' 1 C.p.K).foldl C.epochStep C.initState

/-- Algorithm 1's output: `some` of the Line 18 data, or `none` (`⊥`) if no epoch returned. -/
noncomputable def output : Option (Learned Tok) :=
  C.run.out

/-- The number of calls to the logit oracle made by the run. -/
noncomputable def numQueries : ℕ :=
  C.run.trace.length

/-- The spanner vectors `L_{t,i}` of epoch `e` as functions on `F̃_t` (index `i ∈ Fin d̄`). -/
noncomputable def spanVecs (e : Epoch Tok) (t : ℕ) : Fin (C.dbar e.Fhat) → (tilde e.Fhat t) → ℝ :=
  fun i f => Lor C.O (C.hist e.k e.Fhat e.cur t i ++ f.1)

/-- `E_spanner` (§5.4, p. 24): at every executed epoch and every step `t ∈ {2, …, T}` the
DistSpanner output `L_{t,1:d̄}` is an `(η, β)`-distributional spanner for `P_t`, the law of
`(L_oracle(y_{1:t−1} ∘ f))_{f ∈ F̃_t}` with `y ∼ M` (Line 4). -/
def SpannerEvent [MeasurableSpace Tok] (M : PMF (Fin C.T → Tok)) : Prop :=
  ∀ e ∈ C.run.epochs, ∀ t, 2 ≤ t → t ≤ C.T →
    IsDistSpanner M.toMeasure (fun x (f : tilde e.Fhat t) => Lor C.O (pre x (t - 1) ++ f.1))
      (C.spanVecs e t) C.p.η C.p.β

/-- `E_oracle` (Definition 5.6): the execution trace of the run is `ε_apx`-approximately
`α`-bounded of rank `d` (Definition 4.4). -/
def OracleEvent (d : ℕ) (α εapx : ℝ) : Prop :=
  TraceBoundedRank C.T d α εapx C.O C.run.trace

/-- The program of epoch `e` at step `t` for the prefix `y_{1:t}` of `x` (as in Definition 5.5). -/
noncomputable def progAt (e : Epoch Tok) (t : ℕ) (x : Fin C.T → Tok) : ProgData Tok :=
  C.prog e.k e.Fhat e.cur t (pre x t)

/-- The integrand of (21) (Lemma 5.7) at epoch `e`, step `t`, for `y ∼ M` (the draw of
`Q_t(L_{1:t,1:d̄})`, Definition 5.5, whose solution is the rule's, `0` if infeasible):
`1{y_{1:t} ∈ G_t} · min{1, max_{s,r,y'_r} |L̂_s(y_{s:r−1}, y'_r) − ∑_i c_{s,i} L_{s,i}(y_{s:r−1}, y'_r)|}`
with `2 ≤ s ≤ t`, `s ≤ r ≤ t + 1`, `y'_r ∈ Σ`. -/
noncomputable def integrand21 (e : Epoch Tok) (t : ℕ) (x : Fin C.T → Tok) : ℝ :=
  (if (C.progAt e t x).InG then 1 else 0) *
    min 1 ((((Finset.Icc 2 t).biUnion fun s => (Finset.Icc s (t + 1)).biUnion fun r =>
        (Finset.univ : Finset Tok).image fun y' => (s, seg x s (r - 1) ++ [y'])).sup
      fun sf => Real.toNNReal |C.gap e.k e.Fhat e.cur ((C.R.lp (C.progAt e t x)).getD 0) x sf.1
        sf.2| : NNReal) : ℝ)

/-- The integrand of Lemma 5.8 at epoch `e`, step `t`:
`1{y_{1:t} ∈ G_t} · min{1, max_{y'} |L(y_{1:t} ∘ y') − L̂_{t+1}(y')|}` with
`L̂_{t+1}(y') = ∑_i c_{t,i} L_{t,i}(y_t ∘ y')` (the extension of (14c)) and `L = L_M`. -/
noncomputable def integrand58 (M : PMF (Fin C.T → Tok)) (e : Epoch Tok) (t : ℕ)
    (x : Fin C.T → Tok) : ℝ :=
  (if (C.progAt e t x).InG then 1 else 0) *
    min 1 (((Finset.univ : Finset Tok).sup fun y' =>
      Real.toNNReal |logit M (pre x t) y' -
        ∑ i ∈ Finset.range (C.dbar e.Fhat), (C.R.lp (C.progAt e t x)).getD 0 t i *
          Lor C.O (C.hist e.k e.Fhat e.cur t i ++ seg x t t ++ [y'])| : NNReal) : ℝ)

end Ctx

/-- `E_{y∼M}[g(y)] = ∑_x M(x) g(x)`. -/
noncomputable def expect {T : ℕ} (M : PMF (Fin T → Tok)) (g : (Fin T → Tok) → ℝ) : ℝ :=
  ∑ x, (M x).toReal * g x

/-- The i.i.d. stream law: the cells of `ω : ℕ → (Fin T → Tok)` are independent with law `M`. -/
noncomputable def streamLaw [MeasurableSpace Tok] {T : ℕ} (M : PMF (Fin T → Tok)) :
    MeasureTheory.Measure (ℕ → Fin T → Tok) :=
  MeasureTheory.Measure.infinitePi fun _ : ℕ => M.toMeasure

/-- The program of Algorithm 2 (Line 3) at step `t` for the prefix `ys`, built from the data `D`
returned by Algorithm 1 (values on `F̃_s`, `0` elsewhere) and `β`. -/
def Learned.prog (D : Learned Tok) (β : ℝ) (t : ℕ) (ys : List Tok) : ProgData Tok :=
  ⟨t, ys, D.Fhat, D.dbar, fun s i f => if f ∈ D.Ftil s then D.vals s i f else 0, β⟩

/-- The probability that Algorithm 2, run on `D` with solution rule `lp`, outputs the sequence `x`
(Lines 1–8): `P̂_1(y_1) ∏_{t=1}^{T−1} P̂_{t+1}(y_{t+1})`, with `P̂_1 = softmax(L_{1,1}(·))`,
`P̂_{t+1} = softmax(L̂_{t,t+1})`, `L̂_{t,t+1}(y) = ∑_i c_{t,t,i} L_{t,i}(y_t ∘ y)` (Line 6, values
passed as input), and factor `0` when the program at `y_{1:t}` is infeasible (Line 5: `fail`).
The factor of position `j` (0-based) is the probability of `x_{j+1}`. -/
noncomputable def alg2Prob {T : ℕ} (lp : ProgData Tok → Option (ℕ → ℕ → ℝ)) (β : ℝ)
    (D : Learned Tok) (x : Fin T → Tok) : ℝ :=
  ∏ j : Fin T,
    if (j : ℕ) = 0 then softmax (fun y => D.vals 1 0 [y]) (x j)
    else match lp (D.prog β j (pre x j)) with
      | none => 0
      | some c => softmax (fun y => ∑ i ∈ Finset.range D.dbar,
          c j i * D.vals j i (seg x j j ++ [y])) (x j)

/-- The output law `M̂` of Algorithm 2 on `Option (Fin T → Tok)`: `some x` has probability
`alg2Prob … x`, and `none` (`fail`) the remaining mass. -/
noncomputable def alg2Law {T : ℕ} (lp : ProgData Tok → Option (ℕ → ℕ → ℝ)) (β : ℝ)
    (D : Learned Tok) : Option (Fin T → Tok) → ℝ :=
  fun o => match o with
    | some x => alg2Prob lp β D x
    | none => 1 - ∑ x : Fin T → Tok, alg2Prob lp β D x

/-- The law of `M` on `Option (Fin T → Tok)` (no mass on `none`). -/
noncomputable def modelLaw {T : ℕ} (M : PMF (Fin T → Tok)) : Option (Fin T → Tok) → ℝ :=
  fun o => match o with
    | some x => (M x).toReal
    | none => 0

/-- DistSpanner's sample count is at least `C_m (N/η)² log(N/(δ'η))` with `δ' = δ/(10KT)`, for every
dimension `N ≥ 1` (Algorithm 3, Line 1, called with `η, δ/(10KT)` on Line 7). -/
def MLower (Cm : ℝ) (T : ℕ) (p : Params) : Prop :=
  ∀ N : ℕ, 1 ≤ N → Cm * ((N : ℝ) / p.η) ^ 2 *
      Real.log ((N : ℝ) / (p.δ / (10 * p.K * T) * p.η)) ≤ (p.m N : ℝ)

/-- DistSpanner's sample count is at most `C_m (N/η)² log(N/(δ'η)) + C_m` with `δ' = δ/(10KT)`
(the upper half of `m = Θ((N/η)² log(N/(δη)))`, Algorithm 3, Line 1). -/
def MUpper (Cm : ℝ) (T : ℕ) (p : Params) : Prop :=
  ∀ N : ℕ, (p.m N : ℝ) ≤
    Cm * ((N : ℝ) / p.η) ^ 2 * Real.log ((N : ℝ) / (p.δ / (10 * p.K * T) * p.η)) + Cm

/-- The parameter settings of §5.2 (p. 23) other than `K`, for the rank `d`, the bound `α`, the
oracle error `ε_apx`, the target error `ε` and failure probability `δ`, with the constant `C51` of
Lemma 5.1, `C_n` (Lemma 5.7) and DistSpanner's constant `C_m`: `β = 2`, `γ = 4Kε_apx`,
`γ_thres = γ √(C51 d log(2βKα²/γ))`, `n = ⌈C_n log(TK/δ)/γ_thres⌉`, `η = ε/(3T²n)`, the spanner
parameter `δ`, and `m(N) = ⌈C_m (N/η)² log(N/(δ'η))⌉` with `δ' = δ/(10KT)`. (`K` and `n` are
integers, so the real formulas are rounded up.) -/
def Section52Rest (C51 Cn Cm : ℝ) (T d : ℕ) (α εapx ε δ : ℝ) (p : Params) : Prop :=
  p.β = 2 ∧ p.δ = δ ∧
  p.γthres = 4 * p.K * εapx *
    Real.sqrt (C51 * d * Real.log (2 * p.β * p.K * α ^ 2 / (4 * p.K * εapx))) ∧
  p.n = ⌈Cn * Real.log (T * p.K / δ) / p.γthres⌉₊ ∧
  p.η = ε / (3 * T ^ 2 * p.n) ∧
  ∀ N : ℕ, p.m N = ⌈Cm * ((N : ℝ) / p.η) ^ 2 *
    Real.log ((N : ℝ) / (δ / (10 * p.K * T) * p.η))⌉₊

/-- All parameter settings of §5.2 (p. 23), including `K = ⌈C_K T d log(βdαT/(ε_apx δ))⌉`. -/
def Section52 (C51 CK Cn Cm : ℝ) (T d : ℕ) (α εapx ε δ : ℝ) (p : Params) : Prop :=
  Section52Rest C51 Cn Cm T d α εapx ε δ p ∧
  p.K = ⌈CK * T * d * Real.log (2 * d * α * T / (εapx * δ))⌉₊

end LogitRankDistill


