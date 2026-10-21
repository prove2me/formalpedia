-- Prove2me | Definitions.Def_BatchTesting_PTAS_Model
-- name    : BatchTesting_PTAS_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:49:04.846197+00:00
-- url     : https://prove2.me/theorems/fe5b1276-aa48-43e0-955d-805fa8d67ec0
-- title:
--   §1.1, §2–§4, pp. 4–20 — sequential batch testing: testing schemes, expected cost, cost classes, the count-vector DP, nice- and great-looking states, and the §3.4/§4.3/§4.5 constructions
-- statement:
--   **The sequential batch testing problem** (Segev & Shaposhnik, §1.1). Let $X_1,\dots,X_n$ be independent Bernoulli random variables with $\Pr[X_i=1]=p_i$. Testing $X_i$ costs $c_i>0$, and every batch of tests also pays a set-up cost $\beta\ge 0$. A **testing scheme** is a sequence $S=(S_1,\dots,S_T)$ of pairwise-disjoint subsets of $[n]$ whose union is $[n]$. Batch $S_t$ is inspected only if every earlier batch found no zero, which happens with probability $\varphi(S,t)=\prod_{\tau<t}\prod_{i\in S_\tau}p_i$, so the **expected cost** is
--
--   $$E(S)=\sum_{t=1}^{T}\varphi(S,t)\Big(\beta+\sum_{i\in S_t}c_i\Big).$$
--
--   **Cost classes** (§2.1). The costs are normalized by $c_{\min}=\min_i c_i$, and each normalized cost $c_i/c_{\min}$ is rounded up to the nearest power $(1+\epsilon)^{r_i}$ of $1+\epsilon$; $r_i$ is the class of $i$, $C_r=\{i : r_i=r\}$, and $R=\max_i r_i$. Within a class, the variables are ordered by non-decreasing $p_i$ (ties broken by index), and $C_r[1,N_r]$ denotes the first $N_r$ of them.
--
--   **The dynamic program** (§2.2). A state is a vector $N=(N_0,\dots,N_R)$ in $F=\{0,\dots,|C_0|\}\times\cdots\times\{0,\dots,|C_R|\}$; state $N$ has tested $\biguplus_r C_r[1,N_r]$, and $P_0(N)$ is the product of the $p_i$ of those variables. An action $\Delta\gneq 0$ costs $C(\Delta)=\beta/c_{\min}+\sum_r\Delta_r(1+\epsilon)^r$ (normalized units). For a set of states $G$, a **$G$-path** is a sequence $0=N^{(0)}\to\cdots\to N^{(T)}=N^{(\mathrm{all})}=(|C_0|,\dots,|C_R|)$ of states in $G$ with every step $N^{(t)}-N^{(t-1)}\gneq0$; its cost is $\sum_t P_0(N^{(t-1)})\,C(N^{(t)}-N^{(t-1)})$, and it is optimal if no $G$-path is cheaper. The testing scheme of a path tests, at step $t$, the variables in $\biguplus_r C_r[N^{(t-1)}_r+1,N^{(t)}_r]$.
--
--   **Nice- and great-looking states** (§3.3, §4.2). $\psi(N)$ is the largest $r$ with $N_r\ge1$ ($\psi(0)=-\infty$), and $\kappa=\lceil\log_{1+\epsilon}(n/\epsilon)\rceil$. $N$ is **nice-looking** if $N_r=|C_r|$ for every $r\le\psi(N)-\kappa$. It is **great-looking** if moreover there are an integer $0\le\rho\le R+\lceil\log_{1+\epsilon}n\rceil$ and non-negative integers $\mu_r$ on the middle classes $\psi(N)-\kappa<r\le\psi(N)$ with $\sum\mu_r\le3\kappa/\epsilon^2$ and
--
--   $$N_r=\min\Big\{\Big\lfloor\frac{\mu_r\cdot(\epsilon^2/\kappa)\cdot P_2[(1+\epsilon)^\rho]}{(1+\epsilon)^r}\Big\rfloor,\ |C_r|\Big\}$$
--
--   on every middle class, where $P_2[x]$ rounds $x>0$ down to a power of $2$. The explicit constant $K(\epsilon)=(1+3\epsilon)(1+\epsilon)^2+2\epsilon(1+\epsilon)^4$ is the factor $1+O(\epsilon)$ of Theorem 3.
--
--   **The constructions of the proofs.** (§3.4) From a path $N^*$: $\bar\Delta^{(t)}=[N^{*(t)}-N^{(t-1)}]^+$, and $\Delta^{(t)}_r$ is $0$ for $r>\psi(\bar\Delta^{(t)})$, $\bar\Delta^{(t)}_r$ for $\psi(\bar\Delta^{(t)})-\kappa<r\le\psi(\bar\Delta^{(t)})$, and $|C_r|-N^{(t-1)}_r$ for $r\le\psi(\bar\Delta^{(t)})-\kappa$, with $N^{(t)}=N^{(t-1)}+\Delta^{(t)}$. (§4.3) The bucketing keeps $N^{\diamond(0)}=0$, the last state, and every state at which the bucket $\ell$ with $P_0\in((1+\epsilon)^{-\ell},(1+\epsilon)^{-(\ell-1)}]$ changes. (§4.5) From the bucketed sequence, $\rho_m=\lceil\log_{1+\epsilon}\sum_{r\le\psi(N^{\diamond(m)})}N^{\diamond(m)}_r(1+\epsilon)^r\rceil$, $\mu^{(m)}_r$ is the least integer with $\mu\,(\epsilon^2/\kappa)\,P_2[(1+\epsilon)^{\rho_m}]\ge N^{\diamond(m)}_r(1+\epsilon)^r$, and $\Delta^{(m)}$ is $|C_r|-N^{(m-1)}_r$ below the middle, the displayed $\min\{\cdot\}$ minus $N^{(m-1)}_r$ on the middle, and $0$ above.
--
--   These are the objects of every statement of the mission.
--
--   **Formalization Note.** Standing assumptions bundled in `Standing`: $0<n$, $p_i\in[0,1]$, $c_i>0$, $\beta\ge0$ ($0<n$, $p_i\in[0,1]$ and $\beta\ge 0$ are added; $c_i>0$ is the paper's own, p. 8). Class arithmetic is in $\mathbb Z$, and $\psi(0)=-\infty$ is encoded as $-1$, which is equivalent because every class index is $\ge 0$. "$\ell$-lowest probability" uses the order $(p_i,i)$, lexicographic. Paths and schemes are lists; schemes may contain empty batches. The normalization $\min_i c_i=1$ of p. 8 is performed by the definitions (`cmin`), never assumed. The §3.4 and §4.5 sequences may repeat a state (zero actions). Steps with $P_0=0$ form one extra last bucket. The §4.5 action is defined in $\mathbb Z$ (`greatDeltaZ`) so that its non-negativity (Lemma 5) is a real claim; the states are written coordinatewise by the same three cases. At $\kappa=0$ (only $n=1$, $\epsilon=1$) the factor $\epsilon^2/\kappa$ is $0$ in Lean, but then the middle range is empty and the factor is never used.
-- source:
--   Segev & Shaposhnik, A Polynomial-Time Approximation Scheme for Sequential Batch Testing of Series Systems, SSRN preprint 3277805 (Nov. 2018), pp. 4–5 (§1.1), 8–10 (§2.1–2.2, eq. (1)), 11 (§3.1, eq. (2)), 12–13 (§3.3–3.4), 16 (§4.2), 17–18 (§4.3), 20 (§4.5, eqs. (4)–(5))

import Mathlib

namespace BatchTesting.PTAS

/-! Segev & Shaposhnik, *A Polynomial-Time Approximation Scheme for Sequential Batch Testing of
Series Systems*, SSRN preprint 3277805 (Nov. 2018): the model of §1.1 (pp. 4–5), the cost classes
and the dynamic program of §2 (pp. 8–10), nice-looking states (§3.3, p. 12) with the construction
of §3.4 (p. 13), great-looking states (§4.2, p. 16), the bucketing of §4.3 (pp. 17–18) and the
construction of §4.5 (p. 20). -/

/-- An instance of sequential batch testing on `n` Bernoulli variables (§1.1, p. 4):
`p i = Pr[X_i = 1]`, `c i` the individual testing cost, `beta` the set-up cost `β`. -/
structure Instance (n : ℕ) where
  p : Fin n → ℝ
  c : Fin n → ℝ
  beta : ℝ

/-- Standing assumptions: `[n]` non-empty (added), `p_i ∈ [0,1]` (Bernoulli, added),
`c_i > 0` (§2.1, p. 8), `β ≥ 0` (a set-up cost, added). -/
def Instance.Standing {n : ℕ} (I : Instance n) : Prop :=
  0 < n ∧ (∀ i, 0 ≤ I.p i ∧ I.p i ≤ 1) ∧ (∀ i, 0 < I.c i) ∧ 0 ≤ I.beta

/-- A testing scheme (p. 4): a sequence of pairwise-disjoint subsets of `[n]` whose union is `[n]`. -/
def IsTestingScheme {n : ℕ} (S : List (Finset (Fin n))) : Prop :=
  S.Pairwise Disjoint ∧ ∀ i, ∃ A ∈ S, i ∈ A

/-- `φ(S, t+1) = ∏_{τ ≤ t} ∏_{i ∈ S_τ} p_i` (0-based `t`): the probability that the first `t`
batches detect no zero (p. 5). -/
def phi {n : ℕ} (I : Instance n) (S : List (Finset (Fin n))) (t : ℕ) : ℝ :=
  ∏ τ ∈ Finset.range t, ∏ i ∈ S.getD τ ∅, I.p i

/-- `C(A) = β + ∑_{i ∈ A} c_i`, with individual costs `c` (p. 4). -/
def batchCost {n : ℕ} (I : Instance n) (c : Fin n → ℝ) (A : Finset (Fin n)) : ℝ :=
  I.beta + ∑ i ∈ A, c i

/-- `E(S) = ∑_t φ(S,t) · C(S_t)` computed with individual costs `c` (p. 5). -/
def expectedCostWith {n : ℕ} (I : Instance n) (c : Fin n → ℝ) (S : List (Finset (Fin n))) : ℝ :=
  ∑ t ∈ Finset.range S.length, phi I S t * batchCost I c (S.getD t ∅)

/-- The expected cost `E(S)` of a testing scheme with the instance's own costs (p. 5). -/
def expectedCost {n : ℕ} (I : Instance n) (S : List (Finset (Fin n))) : ℝ :=
  expectedCostWith I I.c S

/-- `min_i c_i`, the normalization constant of p. 8 (attained when `0 < n`). -/
noncomputable def cmin {n : ℕ} (I : Instance n) : ℝ := ⨅ i, I.c i

/-- Cost class of `i` (p. 8): the exponent of the power of `1+ε` to which the normalized cost
`c_i / min_j c_j` is rounded up. -/
noncomputable def classOf {n : ℕ} (I : Instance n) (eps : ℝ) (i : Fin n) : ℕ :=
  ⌈Real.logb (1 + eps) (I.c i / cmin I)⌉₊

/-- `R = ⌈log_{1+ε}(max_i c_i)⌉` (normalized costs), the largest class index (p. 8). -/
noncomputable def R {n : ℕ} (I : Instance n) (eps : ℝ) : ℕ := Finset.univ.sup (classOf I eps)

/-- The rounded cost of `X_i` in the original units: `min_j c_j · (1+ε)^{class(i)}` (p. 8). -/
noncomputable def roundedCost {n : ℕ} (I : Instance n) (eps : ℝ) (i : Fin n) : ℝ :=
  cmin I * (1 + eps) ^ classOf I eps i

/-- The cost class `C_r = {i : class(i) = r}` (p. 8). -/
noncomputable def cls {n : ℕ} (I : Instance n) (eps : ℝ) (r : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => classOf I eps i = r)

/-- The class of `i` as an index in `Fin (R+1)`. -/
noncomputable def classIdx {n : ℕ} (I : Instance n) (eps : ℝ) (i : Fin n) : Fin (R I eps + 1) :=
  ⟨classOf I eps i, Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))⟩

/-- Within-class rank of `i` (0-based) in the order of non-decreasing probability, ties broken
by index: the number of `j ∈ C_{class(i)}` with `(p_j, j) < (p_i, i)` lexicographically.
Thus `C_r[1, N_r] = {i ∈ C_r : rank i < N_r}` (p. 9). -/
noncomputable def rank {n : ℕ} (I : Instance n) (eps : ℝ) (i : Fin n) : ℕ :=
  ((cls I eps (classOf I eps i)).filter
    (fun j => toLex (I.p j, j) < toLex (I.p i, i))).card

/-- DP states (p. 9): vectors `N = (N_0, …, N_R)` of tested counts per class. -/
abbrev State {n : ℕ} (I : Instance n) (eps : ℝ) := Fin (R I eps + 1) → ℕ

/-- The feasible states `F = {0,…,|C_0|} × ⋯ × {0,…,|C_R|}` (p. 9). -/
noncomputable def F {n : ℕ} (I : Instance n) (eps : ℝ) : Finset (State I eps) :=
  Fintype.piFinset (fun r => Finset.range ((cls I eps r).card + 1))

/-- The terminal state `N^(all) = (|C_0|, …, |C_R|)` (p. 10). -/
noncomputable def Nall {n : ℕ} (I : Instance n) (eps : ℝ) : State I eps :=
  fun r => (cls I eps r).card

/-- The variables tested at state `N`: `⊎_r C_r[1, N_r]` (p. 9). -/
noncomputable def tested {n : ℕ} (I : Instance n) (eps : ℝ) (N : State I eps) : Finset (Fin n) :=
  Finset.univ.filter (fun i => rank I eps i < N (classIdx I eps i))

/-- `P_0(N)`: the probability that every variable tested at state `N` evaluates to 1 (p. 13). -/
noncomputable def P0 {n : ℕ} (I : Instance n) (eps : ℝ) (N : State I eps) : ℝ :=
  ∏ i ∈ tested I eps N, I.p i

/-- `C(∆) = β + ∑_r ∆_r (1+ε)^r` (p. 10), in the normalized units of p. 8 (costs and `β`
divided by `min_i c_i`). -/
noncomputable def stepCost {n : ℕ} (I : Instance n) (eps : ℝ) (Δ : State I eps) : ℝ :=
  I.beta / cmin I + ∑ r, (Δ r : ℝ) * (1 + eps) ^ (r : ℕ)

/-- A path of the dynamic program (1)/(2) restricted to the state set `G` (p. 11):
`N^(none) = 0 → ⋯ → N^(all)`, every state in `G`, every action `∆ = M − N ⪈ 0`. -/
def IsPath {n : ℕ} (I : Instance n) (eps : ℝ) (G : Finset (State I eps))
    (π : List (State I eps)) : Prop :=
  π.head? = some 0 ∧ π.getLast? = some (Nall I eps) ∧ (∀ N ∈ π, N ∈ G) ∧
    π.IsChain (fun N M => N ≤ M ∧ N ≠ M)

/-- The cost of a path, in the form (3) (p. 13): `∑_t P_0(N^(t−1)) · C(N^(t) − N^(t−1))`.
(`M - N` is coordinatewise; on a path `N ≤ M`, so it is the action `∆`.) -/
noncomputable def pathCost {n : ℕ} (I : Instance n) (eps : ℝ) (π : List (State I eps)) : ℝ :=
  ((π.zip π.tail).map (fun NM => P0 I eps NM.1 * stepCost I eps (NM.2 - NM.1))).sum

/-- An optimal path of the dynamic program restricted to `G`, i.e. one attaining `OPT_G(N^(none))`. -/
def IsOptPath {n : ℕ} (I : Instance n) (eps : ℝ) (G : Finset (State I eps))
    (π : List (State I eps)) : Prop :=
  IsPath I eps G π ∧ ∀ π', IsPath I eps G π' → pathCost I eps π ≤ pathCost I eps π'

/-- The testing scheme read off a path: batch `t` is `⊎_r C_r[N_r^(t−1)+1, N_r^(t)]` (p. 10). -/
noncomputable def schemeOf {n : ℕ} (I : Instance n) (eps : ℝ) (π : List (State I eps)) :
    List (Finset (Fin n)) :=
  (π.zip π.tail).map (fun NM => tested I eps NM.2 \ tested I eps NM.1)

/-- `ψ(N)`: the maximal index `r` with `N_r ≥ 1`, and `−1` (standing for `−∞`) when `N = 0`
(p. 12). Computed as `max {r + 1 : N_r ≠ 0} − 1` with `max ∅ = 0`. -/
def psi {m : ℕ} (N : Fin m → ℕ) : ℤ :=
  (((Finset.univ.filter (fun r => N r ≠ 0)).sup (fun r => (r : ℕ) + 1) : ℕ) : ℤ) - 1

/-- `κ = ⌈log_{1+ε}(n/ε)⌉` (p. 12). -/
noncomputable def kappa (n : ℕ) (eps : ℝ) : ℤ := ⌈Real.logb (1 + eps) ((n : ℝ) / eps)⌉

/-- Nice-looking states (p. 12): `N_r = |C_r|` for every `r ≤ ψ(N) − κ`. -/
def IsNice {n : ℕ} (I : Instance n) (eps : ℝ) (N : State I eps) : Prop :=
  ∀ r : Fin (R I eps + 1), (r : ℤ) ≤ psi N - kappa n eps → N r = (cls I eps r).card

/-- `P_2[x]`: `x` rounded down to the nearest (integer) power of 2 (p. 16). -/
noncomputable def P2 (x : ℝ) : ℝ := (2 : ℝ) ^ ⌊Real.logb 2 x⌋

/-- The middle classes `ψ − κ < r ≤ ψ` (p. 16). -/
def IsMiddle (ψ κ : ℤ) (r : ℕ) : Prop := ψ - κ < r ∧ (r : ℤ) ≤ ψ

instance (ψ κ : ℤ) (r : ℕ) : Decidable (IsMiddle ψ κ r) := by
  unfold IsMiddle; infer_instance

/-- Great-looking states (p. 16): nice-looking, and there are an integer
`0 ≤ ρ ≤ R + ⌈log_{1+ε} n⌉` and a non-negative integer vector `µ` on the middle classes with
`‖µ‖₁ ≤ 3κ/ε²` such that `N_r = min{⌊µ_r (ε²/κ) P_2[(1+ε)^ρ] / (1+ε)^r⌋, |C_r|}` on every
middle class `ψ(N) − κ < r ≤ ψ(N)`. -/
def IsGreat {n : ℕ} (I : Instance n) (eps : ℝ) (N : State I eps) : Prop :=
  IsNice I eps N ∧
    ∃ ρ : ℕ, ρ ≤ R I eps + ⌈Real.logb (1 + eps) (n : ℝ)⌉₊ ∧
      ∃ μ : Fin (R I eps + 1) → ℕ,
        (∑ r ∈ Finset.univ.filter (fun r : Fin (R I eps + 1) =>
            IsMiddle (psi N) (kappa n eps) r), (μ r : ℝ)) ≤ 3 * (kappa n eps : ℝ) / eps ^ 2 ∧
        ∀ r : Fin (R I eps + 1), IsMiddle (psi N) (kappa n eps) r →
          N r = min ⌊(μ r : ℝ) * (eps ^ 2 / (kappa n eps : ℝ)) * P2 ((1 + eps) ^ ρ) /
            (1 + eps) ^ (r : ℕ)⌋₊ (cls I eps r).card

/-- `F_nice` (p. 12). -/
noncomputable def FNice {n : ℕ} (I : Instance n) (eps : ℝ) : Finset (State I eps) :=
  by classical exact (F I eps).filter (IsNice I eps)

/-- `F_great` (p. 16). -/
noncomputable def FGreat {n : ℕ} (I : Instance n) (eps : ℝ) : Finset (State I eps) :=
  by classical exact (F I eps).filter (IsGreat I eps)

/-- The explicit form of Theorem 3's factor `1 + O(ε)`, read off the chain on pp. 19–20:
`K(ε) = (1+3ε)(1+ε)² + 2ε(1+ε)⁴`. -/
def K (eps : ℝ) : ℝ := (1 + 3 * eps) * (1 + eps) ^ 2 + 2 * eps * (1 + eps) ^ 4

/-! ### The construction of §3.4 (p. 13) -/

/-- The action `∆^(t)` of §3.4 from the previous state `N^(t−1)` and the target `N^∗(t)`:
with `∆̄ = [N^∗(t) − N^(t−1)]^+`, `∆_r = 0` if `r > ψ(∆̄)`, `∆̄_r` if `ψ(∆̄) − κ < r ≤ ψ(∆̄)`,
and `|C_r| − N_r^(t−1)` if `r ≤ ψ(∆̄) − κ`. -/
noncomputable def niceDelta {n : ℕ} (I : Instance n) (eps : ℝ) (Nprev Nstar : State I eps) :
    State I eps :=
  fun r =>
    if psi (Nstar - Nprev) < (r : ℤ) then 0
    else if psi (Nstar - Nprev) - kappa n eps < (r : ℤ) then (Nstar - Nprev) r
    else (cls I eps r).card - Nprev r

/-- `N^(t) = N^(t−1) + ∆^(t)`, iterated along the tail `N^∗(1), …, N^∗(T)`. -/
noncomputable def niceSeqAux {n : ℕ} (I : Instance n) (eps : ℝ) :
    State I eps → List (State I eps) → List (State I eps)
  | _, [] => []
  | Nprev, Nstar :: rest =>
      (Nprev + niceDelta I eps Nprev Nstar) :: niceSeqAux I eps (Nprev + niceDelta I eps Nprev Nstar) rest

/-- The §3.4 sequence `N^(0) = 0, N^(1), …, N^(T)` built from a path `N^∗(0), …, N^∗(T)`
(it may repeat states: zero actions are allowed). -/
noncomputable def niceSeq {n : ℕ} (I : Instance n) (eps : ℝ) (π : List (State I eps)) :
    List (State I eps) :=
  0 :: niceSeqAux I eps 0 π.tail

/-! ### The bucketing of §4.3 (pp. 17–18) -/

/-- The bucket of a probability `x`: the `ℓ ≥ 1` with `x ∈ (1/(1+ε)^ℓ, 1/(1+ε)^{ℓ−1}]`; all
`x ≤ 0` (in a path: `P_0 = 0`) form one extra last bucket `⊤`. -/
noncomputable def bucketIndex (eps x : ℝ) : WithTop ℕ :=
  if x ≤ 0 then ⊤ else ((⌊-Real.logb (1 + eps) x⌋₊ + 1 : ℕ) : WithTop ℕ)

/-- The bucketed subsequence `N^⋄(0) = 0, N^⋄(1), …, N^⋄(M) = N^∗(T)` of a path `N^∗`: the states
`N^∗(t)` with `t = 0`, `t = T`, or step `t` (bucket of `P_0(N^∗(t−1))`) and step `t+1` (bucket of
`P_0(N^∗(t))`) in different buckets (pp. 17–18). Then `∆^⋄(m) = N^⋄(m) − N^⋄(m−1)` is the sum of the
actions of the `m`-th non-empty bucket. -/
noncomputable def bucketed {n : ℕ} (I : Instance n) (eps : ℝ) (π : List (State I eps)) :
    List (State I eps) :=
  by classical exact
  (List.range π.length).filterMap (fun t =>
    if t = 0 ∨ t + 1 = π.length ∨
        bucketIndex eps (P0 I eps (π.getD (t - 1) 0)) ≠ bucketIndex eps (P0 I eps (π.getD t 0))
    then some (π.getD t 0) else none)

/-! ### The construction of §4.5 (p. 20) -/

/-- `ρ_m = ⌈log_{1+ε} ∑_{r ≤ ψ(N^⋄(m))} N_r^⋄(m) (1+ε)^r⌉`, the unique integer with
`(1+ε)^{ρ_m} ∈ [1, 1+ε) · ∑_{r ≤ ψ(N^⋄(m))} N_r^⋄(m) (1+ε)^r` (eq. (4)). -/
noncomputable def rhoOf {n : ℕ} (I : Instance n) (eps : ℝ) (Nd : State I eps) : ℤ :=
  ⌈Real.logb (1 + eps)
    (∑ r ∈ Finset.univ.filter (fun r : Fin (R I eps + 1) => (r : ℤ) ≤ psi Nd),
      (Nd r : ℝ) * (1 + eps) ^ (r : ℕ))⌉

/-- `µ_r^(m)`: the minimal (non-negative) integer with
`µ · (ε²/κ) · P_2[(1+ε)^{ρ_m}] ≥ N_r^⋄(m) (1+ε)^r` (eq. (5)). -/
noncomputable def muOf {n : ℕ} (I : Instance n) (eps : ℝ) (Nd : State I eps)
    (r : Fin (R I eps + 1)) : ℕ :=
  ⌈(Nd r : ℝ) * (1 + eps) ^ (r : ℕ) /
    ((eps ^ 2 / (kappa n eps : ℝ)) * P2 ((1 + eps) ^ rhoOf I eps Nd))⌉₊

/-- The middle-class target `min{⌊µ_r^(m) (ε²/κ) P_2[(1+ε)^{ρ_m}] / (1+ε)^r⌋, |C_r|}` (p. 20). -/
noncomputable def greatTarget {n : ℕ} (I : Instance n) (eps : ℝ) (Nd : State I eps)
    (r : Fin (R I eps + 1)) : ℕ :=
  min ⌊(muOf I eps Nd r : ℝ) * (eps ^ 2 / (kappa n eps : ℝ)) * P2 ((1 + eps) ^ rhoOf I eps Nd) /
    (1 + eps) ^ (r : ℕ)⌋₊ (cls I eps r).card

/-- The action `∆^(m)` of §4.5 (p. 20), integer-valued, from `N^(m−1)` and `N^⋄(m)`:
`|C_r| − N_r^(m−1)` if `r ≤ ψ(N^⋄(m)) − κ`; the middle-class target minus `N_r^(m−1)` if
`ψ(N^⋄(m)) − κ + 1 ≤ r ≤ ψ(N^⋄(m))`; `0` if `r > ψ(N^⋄(m))`. -/
noncomputable def greatDeltaZ {n : ℕ} (I : Instance n) (eps : ℝ) (Nprev Nd : State I eps)
    (r : Fin (R I eps + 1)) : ℤ :=
  if (r : ℤ) ≤ psi Nd - kappa n eps then ((cls I eps r).card : ℤ) - Nprev r
  else if (r : ℤ) ≤ psi Nd then (greatTarget I eps Nd r : ℤ) - Nprev r
  else 0

/-- `N^(m) = N^(m−1) + ∆^(m)` (p. 20), written coordinatewise. -/
noncomputable def greatNext {n : ℕ} (I : Instance n) (eps : ℝ) (Nprev Nd : State I eps) :
    State I eps :=
  fun r =>
    if (r : ℤ) ≤ psi Nd - kappa n eps then (cls I eps r).card
    else if (r : ℤ) ≤ psi Nd then greatTarget I eps Nd r
    else Nprev r

/-- Iterate `greatNext` along `N^⋄(1), …, N^⋄(M)`. -/
noncomputable def greatSeqAux {n : ℕ} (I : Instance n) (eps : ℝ) :
    State I eps → List (State I eps) → List (State I eps)
  | _, [] => []
  | Nprev, Nd :: rest =>
      greatNext I eps Nprev Nd :: greatSeqAux I eps (greatNext I eps Nprev Nd) rest

/-- The §4.5 sequence `N^(0) = 0, N^(1), …, N^(M)` built from the bucketed sequence
`N^⋄(0), …, N^⋄(M)` (it may repeat states). -/
noncomputable def greatSeq {n : ℕ} (I : Instance n) (eps : ℝ) (D : List (State I eps)) :
    List (State I eps) :=
  0 :: greatSeqAux I eps 0 D.tail

end BatchTesting.PTAS


