-- Prove2me | Definitions.Def_HolleyLiggett_Duality_Setting
-- name    : HolleyLiggett_Duality_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T09:24:09.223741+00:00
-- url     : https://prove2.me/theorems/1365cbb9-0982-4937-aa9b-55237aa4af7e
-- title:
--   §1, pp. 643–645 — S = {0,1}^I, C(η) (1.2), α(i, η) (1.3), the proximity transition Q (1.1) and its n-step law, the b.p.i. transition Q̃ (1.4) and its n-step probabilities, B(F) (1.5)
-- statement:
--   This file sets up the two Markov chains of Holley and Liggett (1975): the discrete-time **proximity process** and the discrete-time **branching process with interference** (b.p.i.), together with the §4 example on $\mathbb Z$.
--
--   **Data.** $I$ is a countable set of sites. For each $i\in I$ there is a sequence $N_{i,0}=\emptyset, N_{i,1}, N_{i,2},\dots$ of **finite** subsets of $I$, and a probability distribution $f_i$ on the nonnegative integers. A finite collection $\{N_{i,0},\dots,N_{i,m}\}$ is the case $f_i(k)=0$ for $k>m$ (the sets $N_{i,k}$ with $k>m$ then play no role).
--
--   **Configurations.** $S=\{0,1\}^I$ with the product $\sigma$-algebra; a configuration is $\eta:I\to\{0,1\}$. Its occupied set is
--   $$C(\eta)=\{i\in I:\ \eta(i)=1\}.\qquad(1.2)$$
--
--   **Proximity process.** For $\eta\in S$ and $i\in I$ put $D(i,\eta)=\{k:\ N_{i,k}\cap C(\eta)\neq\emptyset\}$ and
--   $$\alpha(i,\eta)=\sum_{k\in D(i,\eta)} f_i(k).\qquad(1.3)$$
--   The one-step transition function is the product measure
--   $$Q(\eta,\cdot)=\prod_{i\in I}\nu_{\alpha(i,\eta),i},\qquad(1.1)$$
--   where $\nu_{\rho,i}$ is the probability on $\{0,1\}$ putting mass $\rho$ on $1$. The law of the chain at time $n$ started at $\eta$ is $P_\eta(\eta_n\in\cdot)$: the point mass at $\eta$ for $n=0$, and $P_\eta(\eta_{n+1}\in\cdot)=\int Q(\zeta,\cdot)\,P_\eta(\eta_n\in d\zeta)$.
--
--   **Branching process with interference.** Its state space is the collection $\mathcal T$ of finite subsets of $I$, and its transition function is
--   $$\tilde Q(A,B)=\sum{}'\prod_{i\in A} f_i(k_i),\qquad(1.4)$$
--   the sum over all sequences $(k_i)_{i\in A}$ of nonnegative integers with $\bigcup_{i\in A}N_{i,k_i}=B$. The $n$-step probabilities $P_F(A_n=B)$ are given by $P_F(A_0=B)=\mathbf 1[F=B]$ and $P_F(A_{n+1}=B)=\sum_{G\in\mathcal T}P_F(A_n=G)\,\tilde Q(G,B)$. From them: $P_F(A_n\cap C(\eta)=\emptyset)$, $P_F(A_n\neq\emptyset)$ and the expected size $E_F|A_n|$.
--
--   **Dual sets.** For $F\in\mathcal T$,
--   $$B(F)=\{\eta\in S:\ \eta(i)=0\ \text{for all } i\in F\},\qquad(1.5)$$
--   so $B(\emptyset)=S$.
--
--   **The §4 example** (p. 653): $I=\mathbb Z$, $N_{i,0}=\emptyset$, $N_{i,1}=\{i-1,i+1\}$, $f_i(0)=1-\lambda$, $f_i(1)=\lambda$ for a parameter $\lambda\in[0,1]$.
--
--   These objects are the vocabulary of the duality theorem (1.6) and of its applications, Corollaries (3.1) and (4.1).
--
--   **Formalization Note.** $\{0,1\}$ is `Bool` (`true` = 1); $\mathcal T$ is `Finset I`; probabilities are in $[0,\infty]$ (`ℝ≥0∞`), and every $\sum'$ over sequences is an unconditional sum over the countable type of functions $A\to\mathbb N$, which needs no summability hypothesis. The page prints $C(\eta)=\{i:\eta(1)=1\}$; this is a slip for $\eta(i)=1$, which is what is formalized. $Q(\eta,\cdot)$ is Mathlib's `Measure.infinitePi`, which is a genuine product of probability measures because $\alpha(i,\eta)\le1$. The $n$-step law uses `Measure.bind`, which is correct because $\eta\mapsto Q(\eta,\cdot)$ is measurable (a fact, not an assumption). The b.p.i. $n$-step probabilities are defined by the last-step (Chapman–Kolmogorov) recursion. In the §4 example the sets $N_{i,k}$ for $k\ge2$, which carry no mass, are taken empty. The standing assumptions "$I$ countable" and "$N_{i,0}=\emptyset$" are hypotheses of every theorem of the mission rather than part of the definitions.
-- source:
--   Holley and Liggett, Ergodic theorems for weakly interacting infinite systems and the voter model, Ann. Probab. 3 (1975), pp. 643–645, (1.1)–(1.5); p. 653 (§4 example); DOI 10.1214/aop/1176996306

import Mathlib

namespace HolleyLiggett.Duality

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {I : Type*} [DecidableEq I]

/-- The state space `S = {0,1}^I` (`true` = 1, `false` = 0), with the product σ-algebra. -/
abbrev Config (I : Type*) := I → Bool

/-- (1.2) `C(η) = {i ∈ I : η(i) = 1}`, the set of occupied sites. -/
def occupied (η : Config I) : Set I := {i | η i = true}

/-- (1.3) `α(i, η) = Σ_{k ∈ D(i,η)} f_i(k)`, where `D(i, η) = {k : N_{i,k} ∩ C(η) ≠ ∅}`. -/
noncomputable def alpha (N : I → ℕ → Finset I) (f : I → PMF ℕ) (i : I) (η : Config I) : ℝ≥0∞ :=
  ∑' k, {k | ((N i k : Set I) ∩ occupied η).Nonempty}.indicator (fun k => f i k) k

/-- (1.1) The transition function of the discrete-time proximity process,
`Q(η, ·) = ∏_{i ∈ I} ν_{α(i,η), i}`, where `ν_{ρ,i}` puts mass `ρ` on `1`. -/
noncomputable def proxStep (N : I → ℕ → Finset I) (f : I → PMF ℕ) (η : Config I) :
    Measure (Config I) :=
  Measure.infinitePi
    (fun i => alpha N f i η • Measure.dirac true + (1 - alpha N f i η) • Measure.dirac false)

/-- The law at time `n` of the proximity process started at `η`: `P_η(η_n ∈ ·)`.
Time 0 is the point mass at `η`; each further step applies the transition function (1.1). -/
noncomputable def proxLaw (N : I → ℕ → Finset I) (f : I → PMF ℕ) (η : Config I) :
    ℕ → Measure (Config I)
  | 0 => Measure.dirac η
  | n + 1 => (proxLaw N f η n).bind (proxStep N f)

/-- (1.5) `B(F) = {η ∈ S : η(i) = 0 for all i ∈ F}` (so `B(∅) = S`). -/
def zeroOn (F : Finset I) : Set (Config I) := {η | ∀ i ∈ F, η i = false}

/-- (1.4) The transition function of the branching process with interference,
`Q̃(A, B) = Σ′ ∏_{i ∈ A} f_i(k_i)`, the sum over all sequences `(k_i)_{i ∈ A}` with
`⋃_{i ∈ A} N_{i,k_i} = B`. -/
noncomputable def bpiStep (N : I → ℕ → Finset I) (f : I → PMF ℕ) (A B : Finset I) : ℝ≥0∞ :=
  ∑' k : (↥A → ℕ),
    if Finset.univ.biUnion (fun i : ↥A => N i (k i)) = B then ∏ i : ↥A, f i (k i) else 0

/-- The `n`-step transition probabilities of the b.p.i.: `bpiProb N f n F B = P_F(A_n = B)`,
by the recursion `P_F(A_{n+1} = B) = Σ_G P_F(A_n = G) Q̃(G, B)`. -/
noncomputable def bpiProb (N : I → ℕ → Finset I) (f : I → PMF ℕ) :
    ℕ → Finset I → Finset I → ℝ≥0∞
  | 0, F, B => if F = B then 1 else 0
  | n + 1, F, B => ∑' G, bpiProb N f n F G * bpiStep N f G B

open Classical in
/-- `P_F(A_n ∩ C(η) = ∅)`. -/
noncomputable def dualProb (N : I → ℕ → Finset I) (f : I → PMF ℕ) (n : ℕ) (F : Finset I)
    (η : Config I) : ℝ≥0∞ :=
  ∑' B, bpiProb N f n F B * (if Disjoint (B : Set I) (occupied η) then 1 else 0)

open Classical in
/-- `P_F(A_n ≠ ∅)`. -/
noncomputable def survProb (N : I → ℕ → Finset I) (f : I → PMF ℕ) (n : ℕ) (F : Finset I) :
    ℝ≥0∞ :=
  ∑' B, bpiProb N f n F B * (if B.Nonempty then 1 else 0)

/-- `E_F |A_n|`. -/
noncomputable def expSize (N : I → ℕ → Finset I) (f : I → PMF ℕ) (n : ℕ) (F : Finset I) :
    ℝ≥0∞ :=
  ∑' B, bpiProb N f n F B * (B.card : ℝ≥0∞)

/-- §4 example (p. 653): `I = ℤ`, `N_{i,0} = ∅`, `N_{i,1} = {i − 1, i + 1}`
(the sets `N_{i,k}`, `k ≥ 2`, carry no mass and are taken empty). -/
def stavN : ℤ → ℕ → Finset ℤ := fun i k => if k = 1 then {i - 1, i + 1} else ∅

/-- §4 example (p. 653): `f_i(0) = 1 − λ`, `f_i(1) = λ` for every site `i`. -/
noncomputable def stavF (lam : ℝ≥0) (h : lam ≤ 1) : ℤ → PMF ℕ :=
  fun _ => (PMF.ofFintype (fun b : Bool => if b then (lam : ℝ≥0∞) else 1 - (lam : ℝ≥0∞))
      (by simp [add_tsub_cancel_of_le (ENNReal.coe_le_one_iff.mpr h)])).map
    (fun b => if b then 1 else 0)

end HolleyLiggett.Duality


