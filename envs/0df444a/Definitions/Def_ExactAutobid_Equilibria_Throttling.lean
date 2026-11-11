-- Prove2me | Definitions.Def_ExactAutobid_Equilibria_Throttling
-- name    : ExactAutobid_Equilibria_Throttling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:56:17.051255+00:00
-- url     : https://prove2.me/theorems/5e5c2264-cae7-4075-8c91-5d0c49488735
-- title:
--   Second-price throttling equilibria (Definition 2.4), the search problem of Theorem 1.1(iv), and the payment equations of Table 4
-- statement:
--   Bidder $i$ has fixed bids $b_{ij} \ge 0$, a budget $B_i > 0$ and a **participation probability** $\theta_i \in [0,1]$; participation is independent across bidders. Each good is sold by a second-price auction among the participating bidders, ties broken by one fixed **common priority** (part of the instance); the winner pays the highest bid among the other participants ($0$ if alone). $P_i(\theta_{-i})$ is the expected total payment of bidder $i$ **conditional on its participation**:
--   $$P_i(\theta_{-i}) = \sum_{S \subseteq [n]\setminus\{i\}} \Big(\prod_{k\in S}\theta_k \prod_{k\notin S\cup\{i\}} (1-\theta_k)\Big) \sum_j \mathrm{pay}_{ij}(S \cup \{i\}).$$
--   $\theta$ is a **second-price throttling equilibrium** (Definition 2.4) if for every bidder $0 \le \theta_i \le 1$, $\theta_i P_i(\theta_{-i}) \le B_i$, and $\theta_i P_i(\theta_{-i}) < B_i \Rightarrow \theta_i = 1$.
--
--   The real search problem `throttlingProblemOn R` has the well-formed rational markets satisfying $R$ as instances (the priority as a permutation of the bidders) and the equilibria $\theta$ as solutions. The **restricted class** `ThrottleData.Sparse Bids Budgets`: at most three positive bids per good, at most four goods with a positive bid per bidder, every positive bid in `Bids`, every budget in `Budgets`.
--
--   **Table 4** (§7.2). A budget-response system has auxiliary bidders with budgets $B_\ell$ and conditional payments $P_\ell$, and an output bidder with budget $1$; the responses are $\theta = B/\max\{B, P\}$ (7.1). Encoding (7.4) represents $x \in [0,1]$ by the absence probability $q = 1/(2(1+x))$ and participation probability $\theta = (1+2x)/(2(1+x))$; the odds are $r = (1-\theta)/\theta$. `sysC`, `sysD`, `sysH`, `sysI`, `sysG` are the five rows of Table 4 with $\kappa = 1/32$, and `ImplementsEncoded` collects the four claims of Lemma 7.2 for one row.
--
--   **Formalization Note.** A smaller priority rank means higher priority; bidders and goods are `Fin n`, `Fin |J|`, data rational, controls real.
-- source:
--   Huang, Liu, Yan, On the Complexity of Exact Autobidding Equilibria, arXiv:2611.04475 (sha256 270d1b74…), §2.1, p. 5, Definition 2.4; Theorem 1.1(iv), p. 2; §7.1–7.2, pp. 50–52, Table 4, (7.1)–(7.4)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_FixpReciprocal_frame
import Definitions.Def_FixpReciprocal_RealSearch

namespace ExactAutobid.Equilibria

open OnlineCRS.Combine FixpReciprocal

/-! ### Second-price throttling (Definition 2.4) on arbitrary finite bidder and good types -/

section Market

open Classical

variable {β γ : Type} [Fintype β] [Fintype γ]

/-- Bidder `i` wins good `j` in the second-price auction among the participating set `S`: it
participates, and every other participant bids strictly less, or the same with lower priority
(`rank i < rank k`: a smaller rank is a higher priority, one common priority for all goods). -/
def ThrottleWins (b : β → γ → ℝ) (rank : β → ℕ) (S : Finset β) (i : β) (j : γ) : Prop :=
  i ∈ S ∧ ∀ k ∈ S, k ≠ i → b k j < b i j ∨ (b k j = b i j ∧ rank i < rank k)

/-- The payment of bidder `i` for good `j` when the participating set is `S`: the winner pays the
highest bid among the other participants (`0` if it is the only participant); others pay nothing. -/
noncomputable def throttlePay (b : β → γ → ℝ) (rank : β → ℕ) (S : Finset β) (i : β) (j : γ) :
    ℝ :=
  if ThrottleWins b rank S i j then
    (insert 0 ((S.erase i).image (fun k => b k j))).max' (Finset.insert_nonempty _ _)
  else 0

/-- **The conditional payment `P_i(θ_{−i})`**: the expected total payment of `A_i` conditional on
its participation, the other bidders participating independently with probabilities `θ_k`. -/
noncomputable def condPayment (b : β → γ → ℝ) (rank : β → ℕ) (θ : β → ℝ) (i : β) : ℝ :=
  ∑ S ∈ (Finset.univ.erase i).powerset,
    ((∏ k ∈ S, θ k) * ∏ k ∈ (Finset.univ.erase i) \ S, (1 - θ k)) *
      ∑ j, throttlePay b rank (insert i S) i j

/-- **Second-price throttling equilibrium** (Definition 2.4, (2.4)): `θ ∈ [0, 1]^n` and, for every
bidder, `θ_i P_i(θ_{−i}) ≤ B_i` and `θ_i P_i(θ_{−i}) < B_i ⟹ θ_i = 1`.

Huang, Liu, Yan, *On the Complexity of Exact Autobidding Equilibria*, arXiv:2611.04475
(sha256 270d1b74…), §2.1, p. 5, Definition 2.4. -/
def IsThrottlingEq (b : β → γ → ℝ) (B : β → ℝ) (rank : β → ℕ) (θ : β → ℝ) : Prop :=
  ∀ i, (0 ≤ θ i ∧ θ i ≤ 1) ∧ θ i * condPayment b rank θ i ≤ B i ∧
    (θ i * condPayment b rank θ i < B i → θ i = 1)

end Market

/-! ### The search problem -/

/-- The data of a throttling market: `nb` bidders, `ng` goods, the rational bids (one row per
bidder), the budgets, and the common tie priority as the list of bidders from highest to lowest
priority. -/
structure ThrottleData where
  /-- the number of bidders -/
  nb : ℕ
  /-- the number of goods -/
  ng : ℕ
  /-- the bids `b_{ij}`, row `i` for bidder `i` -/
  bids : List (List ℚ)
  /-- the budgets `B_i` -/
  budgets : List ℚ
  /-- the priority: bidders listed from highest to lowest priority -/
  prio : List ℕ

/-- Well-formed data: `nb` rows of `ng` nonnegative bids, `nb` positive budgets, and the priority
a permutation of the bidders `0, …, nb − 1`. -/
def ThrottleData.WellFormed (d : ThrottleData) : Prop :=
  d.bids.length = d.nb ∧ (∀ row ∈ d.bids, row.length = d.ng ∧ ∀ q ∈ row, 0 ≤ q) ∧
    d.budgets.length = d.nb ∧ (∀ q ∈ d.budgets, 0 < q) ∧ d.prio.Perm (List.range d.nb)

/-- The bid `b_{ij}` (`0`-based). -/
def ThrottleData.bid (d : ThrottleData) (i : Fin d.nb) (j : Fin d.ng) : ℝ :=
  (((d.bids.getD i.val []).getD j.val 0 : ℚ) : ℝ)

/-- The budget `B_i`. -/
def ThrottleData.budget (d : ThrottleData) (i : Fin d.nb) : ℝ :=
  ((d.budgets.getD i.val 0 : ℚ) : ℝ)

/-- The priority rank of bidder `i` (its position in the priority list; `0` is highest). -/
def ThrottleData.rank (d : ThrottleData) (i : Fin d.nb) : ℕ := d.prio.idxOf i.val

/-- Binary encoding of the data. -/
def encThrottleData (d : ThrottleData) : List Sym :=
  fNat d.nb ++ fNat d.ng ++ fList (fList fRat) d.bids ++ fList fRat d.budgets ++ fList fNat d.prio

theorem encThrottleData_injective : Function.Injective encThrottleData := by
  rintro ⟨a, b, c, e, f⟩ ⟨a', b', c', e', f'⟩ h
  simp only [encThrottleData, List.append_assoc] at h
  obtain ⟨h1, k1⟩ := fNat_prefixFree h
  obtain ⟨h2, k2⟩ := fNat_prefixFree k1
  obtain ⟨h3, k3⟩ := fRat_prefixFree.fList.fList k2
  obtain ⟨h4, k4⟩ := fRat_prefixFree.fList k3
  have h5 := fNat_prefixFree.fList.injective (by simpa using k4)
  subst h1 h2 h3 h4 h5
  rfl

/-- **Exact second-price throttling equilibrium** (Definition 2.4) on the instances satisfying
`R`, as a real search problem: a solution is the participation vector `θ`.

Huang, Liu, Yan, arXiv:2611.04475 (sha256 270d1b74…), Theorem 1.1(iv), p. 2. -/
def throttlingProblemOn (R : ThrottleData → Prop) : RealSearch where
  Inst := {d : ThrottleData // d.WellFormed ∧ R d}
  enc := fun I => encThrottleData I.1
  enc_injective := fun _ _ h => Subtype.ext (encThrottleData_injective h)
  dim := fun I => I.1.nb
  Sol := fun I => {θ | IsThrottlingEq I.1.bid I.1.budget I.1.rank θ}

/-- **The restricted class of Theorem 1.1(iv)**: at most three positive bids per good, at most four
goods with a positive bid per bidder, every positive bid in `Bids` and every budget in `Budgets`. -/
def ThrottleData.Sparse (Bids Budgets : Finset ℚ) (d : ThrottleData) : Prop :=
  (∀ j : Fin d.ng, (Finset.univ.filter (fun i : Fin d.nb => 0 < d.bid i j)).card ≤ 3) ∧
    (∀ i : Fin d.nb, (Finset.univ.filter (fun j : Fin d.ng => 0 < d.bid i j)).card ≤ 4) ∧
    (∀ (i : Fin d.nb) (j : Fin d.ng), 0 < d.bid i j → ∃ q ∈ Bids, d.bid i j = (q : ℝ)) ∧
    ∀ q ∈ d.budgets, q ∈ Budgets

/-! ### The payment equations of Table 4 (§7.2) -/

/-- **A budget-response system** with `k` inputs: `a` auxiliary bidders with budgets `B_ℓ` and
conditional payments `P_ℓ(q_in, θ)`, and an output bidder with budget one and conditional payment
`P_out(q_in, θ)`, where `q_in` are the input absence probabilities and `θ` the auxiliary
participation probabilities. -/
structure ThrottleSystem (k : ℕ) where
  /-- the number of auxiliary bidders -/
  a : ℕ
  /-- the auxiliary budgets -/
  budget : Fin a → ℝ
  /-- the auxiliary conditional payments -/
  pay : (Fin k → ℝ) → (Fin a → ℝ) → Fin a → ℝ
  /-- the output conditional payment -/
  payOut : (Fin k → ℝ) → (Fin a → ℝ) → ℝ

/-- The participation probabilities `(θ_aux, θ_out)` are the budget responses (7.1),
`θ = B / max{B, P}`, of the system at the input absence probabilities `q_in`. -/
def ThrottleSystem.Responds {k : ℕ} (s : ThrottleSystem k) (qin : Fin k → ℝ) (θ : Fin s.a → ℝ)
    (θout : ℝ) : Prop :=
  (∀ l, θ l = s.budget l / max (s.budget l) (s.pay qin θ l)) ∧ θout = 1 / max 1 (s.payOut qin θ)

/-- The encoding (7.4) of `x ∈ [0, 1]`: absence probability `q = 1/(2(1 + x))`. -/
noncomputable def encQ (x : ℝ) : ℝ := 1 / (2 * (1 + x))

/-- The encoding (7.4) of `x ∈ [0, 1]`: participation probability `θ = (1 + 2x)/(2(1 + x))`. -/
noncomputable def encTheta (x : ℝ) : ℝ := (1 + 2 * x) / (2 * (1 + x))

/-- The odds `r = q/θ = (1 − θ)/θ` of a participation probability `θ`. -/
noncomputable def odds (θ : ℝ) : ℝ := (1 - θ) / θ

/-- `κ = 1/32`. -/
noncomputable def kappa : ℝ := 1 / 32

/-- Table 4, row `C`: budgets `κ, κ²`; `P₁ = κ(1/2 + 5q_{in,1}/2)`, `P₂ = 9κ²q₁`,
`P_out = 11/10 + 9θ₂/10`. -/
noncomputable def sysC : ThrottleSystem 1 :=
  ⟨2, ![kappa, kappa ^ 2],
    fun q θ => ![kappa * (1 / 2 + 5 * q 0 / 2), 9 * kappa ^ 2 * (1 - θ 0)],
    fun _ θ => 11 / 10 + 9 * θ 1 / 10⟩

/-- Table 4, row `D`: budgets `κ, 1, κ`; `P₁ = κ(2/3 + q_{in,1})`, `P₂ = 1/2 + 2θ₁/3`,
`P₃ = 15κq₂`, `P_out = 3/4 + 5θ₃/4`. -/
noncomputable def sysD : ThrottleSystem 1 :=
  ⟨3, ![kappa, 1, kappa],
    fun q θ => ![kappa * (2 / 3 + q 0), 1 / 2 + 2 * θ 0 / 3, 15 * kappa * (1 - θ 1)],
    fun _ θ => 3 / 4 + 5 * θ 2 / 4⟩

/-- Table 4, row `H`: budgets `κ, κ`; `P₁ = 4κq_{in,1}`, `P₂ = 2κθ₁`, `P_out = 1 + θ₂`. -/
noncomputable def sysH : ThrottleSystem 1 :=
  ⟨2, ![kappa, kappa], fun q θ => ![4 * kappa * q 0, 2 * kappa * θ 0], fun _ θ => 1 + θ 1⟩

/-- Table 4, row `I`: budget `κ`; `P₁ = κ(1 + 4q_{in,1})`, `P_out = 1 + θ₁`. -/
noncomputable def sysI : ThrottleSystem 1 :=
  ⟨1, ![kappa], fun q _ => ![kappa * (1 + 4 * q 0)], fun _ θ => 1 + θ 0⟩

/-- Table 4, row `G`: budgets `κ` for all five; `P₁ = 4κq_{in,1}`, `P₂ = 4κq_{in,2}`,
`P₃ = 2κ(θ₁ + θ₂)`, `P₄ = 3κθ₃`, `P₅ = 3κθ₄`, `P_out = 1 + θ₅`. -/
noncomputable def sysG : ThrottleSystem 2 :=
  ⟨5, ![kappa, kappa, kappa, kappa, kappa],
    fun q θ => ![4 * kappa * q 0, 4 * kappa * q 1, 2 * kappa * (θ 0 + θ 1), 3 * kappa * θ 2,
      3 * kappa * θ 3],
    fun _ θ => 1 + θ 4⟩

/-- **The four claims of Lemma 7.2 for one row of Table 4** implementing `f`:
* (encoded identity) for every encoded input `x ∈ [0, 1]^k` (`q_{in,j} = 1/(2(1 + x_j))`), every
  solution of the budget responses has output `θ_out = (1 + 2f(x))/(2(1 + f(x)))`;
* (odds range) for arbitrary input absence probabilities in `[0, 1]`, every solution has output
  odds at most one, and at least `1/3` when all input absence probabilities are at most `1/2`;
* (uniqueness) for fixed inputs in `[0, 1]^k`, the responses determine the auxiliary and output
  probabilities uniquely;
* (extension) every encoded input extends to a solution with the encoded output `f(x)`. -/
def ThrottleSystem.ImplementsEncoded {k : ℕ} (s : ThrottleSystem k) (f : (Fin k → ℝ) → ℝ) :
    Prop :=
  (∀ x : Fin k → ℝ, (∀ j, x j ∈ Set.Icc (0 : ℝ) 1) → ∀ θ θout,
      s.Responds (fun j => encQ (x j)) θ θout → θout = encTheta (f x)) ∧
    (∀ qin : Fin k → ℝ, (∀ j, qin j ∈ Set.Icc (0 : ℝ) 1) → ∀ θ θout, s.Responds qin θ θout →
      odds θout ≤ 1 ∧ ((∀ j, qin j ≤ 1 / 2) → 1 / 3 ≤ odds θout)) ∧
    (∀ qin : Fin k → ℝ, (∀ j, qin j ∈ Set.Icc (0 : ℝ) 1) →
      ∃! p : (Fin s.a → ℝ) × ℝ, s.Responds qin p.1 p.2) ∧
    ∀ x : Fin k → ℝ, (∀ j, x j ∈ Set.Icc (0 : ℝ) 1) →
      ∃ θ, s.Responds (fun j => encQ (x j)) θ (encTheta (f x))

end ExactAutobid.Equilibria


