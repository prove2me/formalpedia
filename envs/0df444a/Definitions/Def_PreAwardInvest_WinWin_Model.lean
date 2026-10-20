-- Prove2me | Definitions.Def_PreAwardInvest_WinWin_Model
-- name    : PreAwardInvest_WinWin_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:17:20.921761+00:00
-- url     : https://prove2.me/theorems/d4e8acac-52f7-40fc-bcdd-240ae4b9a761
-- title:
--   §3–§4.2, pp. 9–17 — procurement with cost-reduction investigations: costs, reductions, investigation policies, the index policy, BIA and BAI, supplier profits, Bayesian Nash equilibria
-- statement:
--   This file fixes the model of Chen, Beil and Duenyas for a buyer who procures one contract from $N\ge 1$ suppliers $\mathcal N=\{1,\dots,N\}$ and may investigate suppliers for cost-reduction opportunities.
--
--   **Costs and reductions (§3.1, pp. 10–12).** Supplier $i$ has cost $c_i=\Delta^c_i+\epsilon^c_i$, where $\Delta^c_i\ge 0$ is public and $\epsilon^c_i$ is private, with p.d.f. $f$ supported on $[\underline c,\bar c]$ and c.d.f. $F(x)=\int_{-\infty}^x f$. Hence $c_i$ has p.d.f. $f_i(c)=f(c-\Delta^c_i)$, c.d.f. $F_i(c)=F(c-\Delta^c_i)$ and support $C_i=[\underline c_i,\bar c_i]=[\underline c+\Delta^c_i,\bar c+\Delta^c_i]$. An investigation of supplier $i$ costs the buyer $d$ and reveals $t_i=\Delta^t_i+\epsilon^t_i$, where $\Delta^t_i\ge 0$ is public and $\epsilon^t_i$ has p.d.f. $g$ on $[\underline t,\bar t]$. All $c_i$ and $t_j$ are independent. The standing assumptions are: $1\le\hat N\le N$ (the cap on investigations), $d\ge 0$, $\underline c<\bar c$, $\underline t<\bar t$, $f$ and $g$ are probability densities with mean $0$, $f>0$ on $(\underline c,\bar c)$, costs and reductions are nonnegative ($\Delta^c_i+\underline c\ge 0$, $\Delta^t_i+\underline t\ge 0$), and cost always exceeds reduction, $\Delta^t_i+\bar t<\Delta^c_i+\underline c$ (footnote 6). **Assumption 1** says that $F_i/f_i$ is nondecreasing on the support of $c_i$; **Assumption 2** says that $d<\max_i\Delta^t_i$. Suppliers are **ex ante symmetric** when $\Delta^c_i=\Delta^c$ and $\Delta^t_i=\Delta^t$ for all $i$.
--
--   **Investigation policies (§3.3, pp. 14–15).** Given the bid vector $b$, a policy decides in each round, from $b$, the set $I$ of suppliers already investigated and their revealed reductions $(t_j)_{j\in I}$, either to stop or to investigate one more supplier. It runs at most $\hat N$ rounds and stopping is final. $S^\pi(b)$ is the set investigated at the end. A policy is admissible when its decisions depend only on the revealed reductions and are measurable in them. The buyer's realized cost is the lowest **updated bid** plus the investigation cost,
--
--   $$\min_{i\in\mathcal N}\{b_i-\mathbf 1[i\in S^\pi(b)]\,t_i\}+|S^\pi(b)|\,d,$$
--
--   and her problem (1) minimizes its expectation over $t$.
--
--   **Theorem 1's index policy (p. 16).** For a root $\tau$ of $d=\int_\tau^\infty(\epsilon^t-\tau)\,dG(\epsilon^t)$, let $\tau_i=\max\{0,\tau+\Delta^t_i\}$ and $\mu_i(b_i)=b_i-\tau_i$. Rank the suppliers by $\mu_i$ from low to high, $\kappa(i)$ being the rank of $i$ and $\iota(k)$ the supplier of rank $k$. Let $\tilde N=\min\{n:\tau_{\iota(n+1)}=0\}$ ($\tilde N=N$ if no $\tau_i$ vanishes) and $\bar N=\min\{\hat N,\tilde N\}$. Once $\bar N$ suppliers have been investigated the policy stops; otherwise it looks at the uninvestigated supplier $j$ of lowest index and stops if the current lowest updated bid $u$ satisfies $u<\mu_j(b_j)$, and investigates $j$ otherwise.
--
--   **Mechanisms.** In **BIA** (bid, investigate, award) the buyer runs the index policy on the bids and awards the contract to the lowest updated bid. In **BAI** (bid, award, investigate, §3.2) she awards it to the lowest $\lambda_i=b_i-r_i$ with $r_i=\max\{0,\Delta^t_i-d\}$. Ties, in the ranking and in either award, are broken by one uniformly random priority order of the suppliers. $W_i(b)$ is supplier $i$'s winning probability (over $t$ and the priority order). The first-price auction of Proposition 1 awards the contract to the lowest bid.
--
--   **Profits and equilibria (§3.2, §4.2).** A strategy profile $\beta=(\beta_i)$ maps costs to bids in $B_i=[0,\bar c_i]$. With the others bidding $\beta_{-i}(c_{-i})$, supplier $i$ of cost $c$ bidding $b$ earns, as in (5),
--
--   $$u_i(b;c)=(b-c)\,\mathbf E_{c_{-i}}\big[W_i(b,\beta_{-i}(c_{-i}))\big].$$
--
--   A Bayesian Nash equilibrium is a profile of measurable strategies with $\beta_i(C_i)\subseteq B_i$ and $u_i(b;c)\le u_i(\beta_i(c);c)$ for all $i$, $c\in C_i$ and $b\in B_i$. Supplier $i$'s ex ante expected profit is $\mathbf E_{c_i}[u_i(\beta_i(c_i);c_i)]$. The first-price auction of Proposition 1 has costs $\check c_i=c_i-r_i$ and bids in $B_i-r_i=[-r_i,\bar c_i-r_i]$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.**
--   1. Suppliers are `Fin N`; all values are real numbers. `Params` collects $\hat N,d,\Delta^c,\Delta^t,\underline c,\bar c,\underline t,\bar t,f,g$; `Params.Standing` is the list of standing assumptions above.
--   2. $f>0$ on $(\underline c,\bar c)$ is added: Assumption 1 and the identities of the proof of Theorem 2 divide by $f_i$.
--   3. The laws of $c_i$ and $t_i$ are `volume.withDensity` of $f_i$ and $g(\cdot-\Delta^t_i)$; the vectors $c$ and $t$ have the product laws `Measure.pi`. Expectations over $c_{-i}$ integrate over the whole vector $c$ with coordinate $i$ overwritten by the bid, which is the same thing because the law is a product.
--   4. Ties are broken by a priority $\sigma$ (a permutation of the suppliers), and $W_i$ averages over all $\sigma$. The paper says ties in BAI are broken at random and leaves those of BIA unspecified; a uniform random priority keeps both mechanisms invariant under relabelling the suppliers.
--   5. A policy is a function of the bids, the investigated set and the reduction vector; admissibility requires that it read only the reductions of investigated suppliers and that every decision set be measurable. A choice of an already investigated supplier is read as a stop. Since stopping is final, the round number is $|I|+1$ and need not be an argument.
--   6. Bids in both mechanisms lie in $B_i=[0,\bar c_i]$ (§3.2 and §4.2, "$\beta_i:C_i\to B_i$").
-- source:
--   Chen, Beil & Duenyas, Procurement mechanisms with post-auction pre-award cost-reduction investigations, accepted manuscript (Operations Research 70(6), 2022; LBS Research Online eprint 2544), pp. 9–17 (PDF 10–18), §3.1–§3.3, §4.1–§4.2, Assumptions 1–2, footnote 6, (1), Theorem 1, (5); proof of Proposition 1, p. 39 (PDF 40)

import Mathlib

namespace PreAwardInvest.WinWin

open MeasureTheory

/-! # Procurement with post-auction pre-award cost-reduction investigations

Chen, Beil & Duenyas (accepted manuscript, Operations Research 70(6), 2022), §3 (pp. 9–15), §4
(pp. 15–18). Suppliers are `Fin N`; every value is real. -/

/-- The primitive data of §3.1 (pp. 10–12). -/
structure Params (N : ℕ) where
  /-- the cap `N̂` on the number of investigations -/
  Nhat : ℕ
  /-- the cost `d` of one investigation -/
  d : ℝ
  /-- `Δ^c_i = E[c_i]` -/
  dc : Fin N → ℝ
  /-- `Δ^t_i = E[t_i]` -/
  dt : Fin N → ℝ
  /-- the support `[c̲, c̄]` of `ε^c` -/
  cLo : ℝ
  cHi : ℝ
  /-- the support `[t̲, t̄]` of `ε^t` -/
  tLo : ℝ
  tHi : ℝ
  /-- the p.d.f. `f` of `ε^c` -/
  f : ℝ → ℝ
  /-- the p.d.f. `g` of `ε^t` -/
  g : ℝ → ℝ

variable {N : ℕ}

/-- The c.d.f. `F` of `ε^c`. -/
noncomputable def Fc (P : Params N) (x : ℝ) : ℝ := ∫ y in Set.Iic x, P.f y

/-- `F_i(c) = F(c − Δ^c_i)`, the c.d.f. of supplier `i`'s cost. -/
noncomputable def Fi (P : Params N) (i : Fin N) (c : ℝ) : ℝ := Fc P (c - P.dc i)

/-- `f_i(c) = f(c − Δ^c_i)`, the p.d.f. of supplier `i`'s cost. -/
def fi (P : Params N) (i : Fin N) (c : ℝ) : ℝ := P.f (c - P.dc i)

/-- `c̲_i = c̲ + Δ^c_i`. -/
def cLoI (P : Params N) (i : Fin N) : ℝ := P.cLo + P.dc i

/-- `c̄_i = c̄ + Δ^c_i`; `C_i = [c̲_i, c̄_i]` and the bid space is `B_i = [0, c̄_i]`. -/
def cHiI (P : Params N) (i : Fin N) : ℝ := P.cHi + P.dc i

/-- The law of `ε^t` (density `g`). -/
noncomputable def epsT (P : Params N) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (P.g x))

/-- The law of supplier `i`'s cost `c_i` (density `f_i`). -/
noncomputable def costLaw (P : Params N) (i : Fin N) : Measure ℝ :=
  volume.withDensity (fun c => ENNReal.ofReal (fi P i c))

/-- The law of supplier `i`'s cost reduction `t_i` (density `g_i(t) = g(t − Δ^t_i)`). -/
noncomputable def redLaw (P : Params N) (i : Fin N) : Measure ℝ :=
  volume.withDensity (fun t => ENNReal.ofReal (P.g (t - P.dt i)))

/-- The joint law of the cost vector `c` (independent across suppliers). -/
noncomputable def costVecLaw (P : Params N) : Measure (Fin N → ℝ) :=
  Measure.pi (costLaw P)

/-- The joint law of the cost-reduction vector `t` (independent across suppliers, and independent
of `c`: every expectation below integrates `t` and `c` separately). -/
noncomputable def redVecLaw (P : Params N) : Measure (Fin N → ℝ) :=
  Measure.pi (redLaw P)

/-- The standing assumptions of §3.1 (pp. 10–12), including footnote 6, and `f > 0` on the open
support (added). -/
def Params.Standing (P : Params N) : Prop :=
  1 ≤ P.Nhat ∧ P.Nhat ≤ N ∧ 0 ≤ P.d ∧ (∀ i, 0 ≤ P.dc i ∧ 0 ≤ P.dt i) ∧
  P.cLo < P.cHi ∧ P.tLo < P.tHi ∧
  (∀ x, 0 ≤ P.f x) ∧ Measurable P.f ∧ (∀ x, x ∉ Set.Icc P.cLo P.cHi → P.f x = 0) ∧
  ∫ x, P.f x = 1 ∧ ∫ x, x * P.f x = 0 ∧ (∀ x ∈ Set.Ioo P.cLo P.cHi, 0 < P.f x) ∧
  (∀ x, 0 ≤ P.g x) ∧ Measurable P.g ∧ (∀ x, x ∉ Set.Icc P.tLo P.tHi → P.g x = 0) ∧
  ∫ x, P.g x = 1 ∧ ∫ x, x * P.g x = 0 ∧
  (∀ i, 0 ≤ P.dc i + P.cLo ∧ 0 ≤ P.dt i + P.tLo ∧ P.dt i + P.tHi < P.dc i + P.cLo)

/-- Assumption 1 (p. 11): `F_i / f_i` is nondecreasing on the (open) support of `c_i`. -/
def Assumption1 (P : Params N) : Prop :=
  ∀ i, MonotoneOn (fun c => Fi P i c / fi P i c) (Set.Ioo (cLoI P i) (cHiI P i))

/-- Assumption 2 (p. 12): `d < max_i Δ^t_i`. -/
def Assumption2 [NeZero N] (P : Params N) : Prop :=
  P.d < Finset.univ.sup' Finset.univ_nonempty P.dt

/-- Ex ante symmetric suppliers (§5.1, p. 19): `Δ^c_i = Δ^c` and `Δ^t_i = Δ^t` for all `i`. -/
def ExAnteSymmetric (P : Params N) : Prop :=
  ∀ i j, P.dc i = P.dc j ∧ P.dt i = P.dt j

/-! ## Tie-breaking -/

/-- `i` comes no later than `j` in the order "by `key`, ties by the priority `σ`". -/
def LexLE (key : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) (i j : Fin N) : Prop :=
  key i < key j ∨ (key i = key j ∧ σ i ≤ σ j)

/-- The minimizer of `key` over `s`, ties broken by the smallest priority `σ i` (on a nonempty `s`
this element exists and is unique). -/
noncomputable def argminIn [NeZero N] (s : Finset (Fin N)) (key : Fin N → ℝ)
    (σ : Equiv.Perm (Fin N)) : Fin N :=
  Classical.epsilon fun i => i ∈ s ∧ ∀ j ∈ s, LexLE key σ i j

/-! ## BIA: sequential investigation policies (§3.3, pp. 14–15) -/

/-- A sequential investigation policy: given the bids `b`, the set `I` of suppliers already
investigated and the cost-reduction vector `t` (of which only `t_j`, `j ∈ I`, may be used), it either
stops (`none`) or investigates one more supplier (`some j`). -/
def Policy (N : ℕ) := (Fin N → ℝ) → Finset (Fin N) → (Fin N → ℝ) → Option (Fin N)

/-- An admissible policy is nonanticipative (it reads only the revealed reductions) and measurable
in the reductions. -/
def Policy.Admissible (π : Policy N) : Prop :=
  (∀ b I t t', (∀ j ∈ I, t j = t' j) → π b I t = π b I t') ∧
  (∀ b I (o : Option (Fin N)), MeasurableSet {t : Fin N → ℝ | π b I t = o})

/-- Running a policy for at most `k` more rounds from the investigated set `I`. Stopping is final;
a choice of an already investigated supplier is read as a stop. -/
def runInv (π : Policy N) (b t : Fin N → ℝ) : ℕ → Finset (Fin N) → Finset (Fin N)
  | 0, I => I
  | k + 1, I =>
    match π b I t with
    | some j => if j ∈ I then I else runInv π b t k (insert j I)
    | none => I

/-- `S^π(b)`: the set of investigated suppliers after at most `N̂` rounds. -/
def investigated (P : Params N) (π : Policy N) (b t : Fin N → ℝ) : Finset (Fin N) :=
  runInv π b t P.Nhat ∅

/-- The updated bid `b_i − 1[i ∈ S] t_i`. -/
def updatedBid (b t : Fin N → ℝ) (S : Finset (Fin N)) (i : Fin N) : ℝ :=
  b i - if i ∈ S then t i else 0

/-- The buyer's realized total cost in (1): lowest updated bid plus `|S| d`. -/
noncomputable def buyerCost [NeZero N] (P : Params N) (π : Policy N) (b t : Fin N → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (updatedBid b t (investigated P π b t)) +
    ((investigated P π b t).card : ℝ) * P.d

/-- The objective of the buyer's problem (1), p. 15: expected total cost of policy `π` at bids `b`. -/
noncomputable def expCost [NeZero N] (P : Params N) (π : Policy N) (b : Fin N → ℝ) : ℝ :=
  ∫ t, buyerCost P π b t ∂(redVecLaw P)

/-! ## Theorem 1's index policy (p. 16) -/

/-- `τ` solves `d = ∫_τ^∞ (ε^t − τ) dG(ε^t)`. -/
def IsTauRoot (P : Params N) (τ : ℝ) : Prop :=
  P.d = ∫ e in Set.Ici τ, (e - τ) ∂(epsT P)

/-- `τ_i = max{0, τ + Δ^t_i}`. -/
noncomputable def tauI (P : Params N) (τ : ℝ) (i : Fin N) : ℝ := max 0 (τ + P.dt i)

/-- The index `μ_i(b_i) = b_i − τ_i`. -/
noncomputable def mu (P : Params N) (τ : ℝ) (b : Fin N → ℝ) (i : Fin N) : ℝ := b i - tauI P τ i

open Classical in
/-- The rank `κ(i) ∈ {1, …, N}` of supplier `i` when suppliers are ranked by index from low to
high, ties by the priority `σ`. -/
noncomputable def rank (P : Params N) (τ : ℝ) (σ : Equiv.Perm (Fin N)) (b : Fin N → ℝ)
    (i : Fin N) : ℕ :=
  (Finset.univ.filter fun j =>
    mu P τ b j < mu P τ b i ∨ (mu P τ b j = mu P τ b i ∧ σ j < σ i)).card + 1

open Classical in
/-- `Ñ = min{n : τ_{ι(n+1)} = 0}`, with `Ñ = N` when no supplier has `τ_i = 0`. -/
noncomputable def Ntil (P : Params N) (τ : ℝ) (σ : Equiv.Perm (Fin N)) (b : Fin N → ℝ) : ℕ :=
  Nat.find (p := fun n => n = N ∨ ∃ i, tauI P τ i = 0 ∧ rank P τ σ b i = n + 1) ⟨N, Or.inl rfl⟩

/-- `N̄ = min{N̂, Ñ}`. -/
noncomputable def Nbar (P : Params N) (τ : ℝ) (σ : Equiv.Perm (Fin N)) (b : Fin N → ℝ) : ℕ :=
  min P.Nhat (Ntil P τ σ b)

open Classical in
/-- The index policy (3) of Theorem 1(a): stop once `N̄` suppliers have been investigated;
otherwise let `j` be the uninvestigated supplier of lowest index (ties by `σ`), stop if the lowest
updated bid `u_k` is below `μ_j`, and investigate `j` otherwise. -/
noncomputable def indexPolicy [NeZero N] (P : Params N) (τ : ℝ) (σ : Equiv.Perm (Fin N)) :
    Policy N := fun b I t =>
  if Nbar P τ σ b ≤ I.card then none
  else if (Finset.univ \ I).Nonempty then
    if Finset.univ.inf' Finset.univ_nonempty (updatedBid b t I) <
        mu P τ b (argminIn (Finset.univ \ I) (mu P τ b) σ) then none
    else some (argminIn (Finset.univ \ I) (mu P τ b) σ)
  else none

/-! ## Awards and winning probabilities -/

/-- The BIA winner: the lowest updated bid after the index policy has run, ties by `σ`. -/
noncomputable def winnerBIA [NeZero N] (P : Params N) (τ : ℝ) (σ : Equiv.Perm (Fin N))
    (b t : Fin N → ℝ) : Fin N :=
  argminIn Finset.univ (updatedBid b t (investigated P (indexPolicy P τ σ) b t)) σ

/-- Supplier `i`'s BIA allocation probability at bids `b` and realized reductions `t`, averaging
only over the uniformly random tie priority. This is `Aᵢᴮᴵᴬ(b,t)` in the proof of Theorem 2. -/
noncomputable def allocBIA [NeZero N] (P : Params N) (τ : ℝ) (b t : Fin N → ℝ)
    (i : Fin N) : ℝ :=
  (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
    ∑ σ : Equiv.Perm (Fin N), if winnerBIA P τ σ b t = i then (1 : ℝ) else 0

/-- `W_i(b)`: supplier `i`'s BIA winning probability, over `t` and over a uniformly random
priority `σ`. -/
noncomputable def winProbBIA [NeZero N] (P : Params N) (τ : ℝ) (b : Fin N → ℝ) (i : Fin N) : ℝ :=
  (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
    ∑ σ : Equiv.Perm (Fin N), ((redVecLaw P) {t | winnerBIA P τ σ b t = i}).toReal

/-- Winning probability in a first-price sealed-bid (procurement) auction: the lowest bid wins,
ties broken uniformly at random. -/
noncomputable def winProbFPA [NeZero N] (b : Fin N → ℝ) (i : Fin N) : ℝ :=
  (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
    ∑ σ : Equiv.Perm (Fin N), if argminIn Finset.univ b σ = i then (1 : ℝ) else 0

/-- `r_i = max{0, Δ^t_i − d}`, the expected payment reduction in BAI (p. 13). -/
noncomputable def rBAI (P : Params N) (i : Fin N) : ℝ := max 0 (P.dt i - P.d)

/-- BAI winning probability: the award goes to `argmin λ_i`, `λ_i = b_i − r_i`, ties at random. -/
noncomputable def winProbBAI [NeZero N] (P : Params N) (b : Fin N → ℝ) (i : Fin N) : ℝ :=
  winProbFPA (fun j => b j - rBAI P j) i

/-! ## Suppliers' profits and equilibria (§3.2, §4.2) -/

/-- The bid vector `(β_j(c_j))_j` of a strategy profile at the cost vector `c`. -/
def bidProfile (β : Fin N → ℝ → ℝ) (c : Fin N → ℝ) : Fin N → ℝ := fun j => β j (c j)

/-- (5): `u_i(b; c) = (b − c) E_{c_{−i}}[W_i(b, β_{−i}(c_{−i}))]` in BIA. -/
noncomputable def profitBIA [NeZero N] (P : Params N) (τ : ℝ) (β : Fin N → ℝ → ℝ) (i : Fin N)
    (b c : ℝ) : ℝ :=
  (b - c) * ∫ cv, winProbBIA P τ (Function.update (bidProfile β cv) i b) i ∂(costVecLaw P)

/-- `u_i(b; c) = (b − c) P_{c_{−i}}(i wins)` in BAI (p. 13). -/
noncomputable def profitBAI [NeZero N] (P : Params N) (β : Fin N → ℝ → ℝ) (i : Fin N)
    (b c : ℝ) : ℝ :=
  (b - c) * ∫ cv, winProbBAI P (Function.update (bidProfile β cv) i b) i ∂(costVecLaw P)

/-- A pure-strategy Bayesian Nash equilibrium of BIA (buyer on the index policy for root `τ`):
measurable strategies `β_i : C_i → B_i` with no profitable deviation in `B_i = [0, c̄_i]`. -/
def IsEqBIA [NeZero N] (P : Params N) (τ : ℝ) (β : Fin N → ℝ → ℝ) : Prop :=
  (∀ i, Measurable (β i)) ∧
  (∀ i, ∀ c ∈ Set.Icc (cLoI P i) (cHiI P i), β i c ∈ Set.Icc 0 (cHiI P i)) ∧
  ∀ i, ∀ c ∈ Set.Icc (cLoI P i) (cHiI P i), ∀ b ∈ Set.Icc 0 (cHiI P i),
    profitBIA P τ β i b c ≤ profitBIA P τ β i (β i c) c

/-- A pure-strategy Bayesian Nash equilibrium of BAI. -/
def IsEqBAI [NeZero N] (P : Params N) (β : Fin N → ℝ → ℝ) : Prop :=
  (∀ i, Measurable (β i)) ∧
  (∀ i, ∀ c ∈ Set.Icc (cLoI P i) (cHiI P i), β i c ∈ Set.Icc 0 (cHiI P i)) ∧
  ∀ i, ∀ c ∈ Set.Icc (cLoI P i) (cHiI P i), ∀ b ∈ Set.Icc 0 (cHiI P i),
    profitBAI P β i b c ≤ profitBAI P β i (β i c) c

/-- Ex ante expected profit of supplier `i` in BIA: `E_{c_i}[u_i(β_i(c_i); c_i)]`. -/
noncomputable def exAnteBIA [NeZero N] (P : Params N) (τ : ℝ) (β : Fin N → ℝ → ℝ) (i : Fin N) : ℝ :=
  ∫ c, profitBIA P τ β i (β i c) c ∂(costLaw P i)

/-- Ex ante expected profit of supplier `i` in BAI. -/
noncomputable def exAnteBAI [NeZero N] (P : Params N) (β : Fin N → ℝ → ℝ) (i : Fin N) : ℝ :=
  ∫ c, profitBAI P β i (β i c) c ∂(costLaw P i)

/-! ## The first-price auction of Proposition 1 (p. 13): costs `č_i = c_i − r_i` -/

/-- Supplier `i`'s expected profit in the first-price auction with costs `č_j = c_j − r_j`, when he
bids `b` with cost `č` and every `j ≠ i` bids `β̌_j(č_j)`. -/
noncomputable def profitFPA [NeZero N] (P : Params N) (βc : Fin N → ℝ → ℝ) (i : Fin N)
    (b c : ℝ) : ℝ :=
  (b - c) * ∫ cv, winProbFPA (Function.update (fun j => βc j (cv j - rBAI P j)) i b) i
    ∂(costVecLaw P)

/-- A pure-strategy Bayesian Nash equilibrium of that first-price auction: cost types
`[c̲_i − r_i, c̄_i − r_i]`, bids in `[−r_i, c̄_i − r_i] = B_i − r_i`. -/
def IsEqFPA [NeZero N] (P : Params N) (βc : Fin N → ℝ → ℝ) : Prop :=
  (∀ i, Measurable (βc i)) ∧
  (∀ i, ∀ c ∈ Set.Icc (cLoI P i - rBAI P i) (cHiI P i - rBAI P i),
    βc i c ∈ Set.Icc (-rBAI P i) (cHiI P i - rBAI P i)) ∧
  ∀ i, ∀ c ∈ Set.Icc (cLoI P i - rBAI P i) (cHiI P i - rBAI P i),
    ∀ b ∈ Set.Icc (-rBAI P i) (cHiI P i - rBAI P i),
      profitFPA P βc i b c ≤ profitFPA P βc i (βc i c) c

end PreAwardInvest.WinWin


