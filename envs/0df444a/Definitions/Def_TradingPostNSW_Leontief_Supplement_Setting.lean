-- Prove2me | Definitions.Def_TradingPostNSW_Leontief_Supplement_Setting
-- name    : TradingPostNSW_Leontief_Supplement_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T20:30:03.300133+00:00
-- url     : https://prove2.me/theorems/09bd41fc-7911-4578-9015-cff9f548c721
-- title:
--   §2–§4, Def. 3.1, App. D, pp. 6–8, 12, 25–28 — general utilities, CES, Fisher market equilibrium and mechanism, mixed strategies of Trading Post
-- statement:
--   Objects used by the companion theorems of Brânzei, Gkatzelis and Mehta, on top of the published base definitions (Leontief instance $\langle v,B\rangle$, strategy sets $S_i$, effective bids, the Trading Post allocation $x(b)$ of $TP(\Delta)$, the Leontief utility $u_i$, feasibility, $NSW$, $\varepsilon$-market equilibria).
--
--   1. **Bundles.** The box $[0,1]^m$ (the domain of utilities, §2) and the orthant $\mathbb R^m_{\ge0}$ (reports and affordable bundles).
--   2. **Standing assumptions.** For general utilities: $m\ge1$ and $B_i\ge1$. For linear valuations additionally $v_{i,j}\ge0$; unlike the Leontief standing assumption, an agent may value no good.
--   3. **Utilities.** The linear utility $u_i(y)=\sum_j v_{i,j}y_j$; the general class of §2: concave, non-decreasing and non-negative on $[0,1]^m$; the CES utility of p. 7,
--   $$u_i(x)=\Big(\sum_{j:\,v_{i,j}>0} v_{i,j}x_j^{\rho}\Big)^{1/\rho}\quad(\rho\le1,\ \rho\ne0),$$
--   equal to $0$ when $\rho<0$ and some good with $v_{i,j}>0$ is absent, and the Cobb–Douglas utility $\prod_j x_j^{v_{i,j}}$ for $\rho=0$.
--   4. **Competition conditions.** Perfect competition for general utilities (§4, p. 12): every good $j$ matters to two distinct agents, where $f$ *depends on* $j$ if two bundles of the box differing only in coordinate $j$ have different values. Enough competition (Appendix D.3): every good $j$ has two distinct agents whose right difference quotient $(f(x+te_j)-f(x))/t$ tends to $+\infty$ as $t\downarrow0$ at every bundle with $x_j=0$.
--   5. **Welfare and Trading Post equilibria.** $NSW_U(x)=\big(\prod_i U_i(x_i)^{B_i}\big)^{1/B}$ and the pure Nash equilibria of $TP(\Delta)$ for a utility profile $U$ ($\Delta=0$ is the game without fee).
--   6. **Fisher markets (p. 7).** $(p,x)$ is a market equilibrium of budgets $B$ and utilities $w$ over a bundle domain if $p,x\ge0$, $\sum_i x_{i,j}\le1$ with equality when $p_j>0$, $\sum_j x_{i,j}p_j=B_i$, and $w_i(y)\le w_i(x_i)$ for every affordable $y$ of the domain.
--   7. **Fisher Market Mechanism (Definition 3.1).** Reported linear or Leontief markets, with the goods nobody reports removed (price $0$, unallocated); a source *total outcome rule* returns an equilibrium at every admissible report; a separately named *partial outcome rule* returns one wherever an equilibrium exists; the *selection clause* asks it to return an equilibrium that every agent (true utilities) weakly prefers to every other equilibrium when such an equilibrium exists; a *pure Nash equilibrium* of the mechanism is a report profile with an equilibrium at which no agent gains, in true utility, by a unilateral change of report.
--   8. **Mixed strategies (Appendix D).** Independent Borel probability measures on bid vectors, concentrated almost surely on $S_i$. Expected utility is the integral of $U_i(x_i(s))$ against the product distribution. The equilibrium predicate requires integrability of the compared payoffs, and no profitable pure deviation; purity means Dirac marginals. These definitions include atomless distributions.
--   9. **Refutation instances.** `linearRefutationInstance` has three agents, two goods, budgets one and valuations $(1,0),(1/10,1),(0,1)$. `feeRefutationInstance` has two agents and two goods, all valuations and budgets one. `LinearPurityFails` asserts a non-pure mixed equilibrium in the first; `LeontiefPurityFails` asserts one in the second at fee $2$.
--
--   **Formalization Note** CES uses an explicit zero branch for a missing demanded good when $\rho<0$. Theorems 3.3, 3.6 and 3.9 explicitly generalize to partial outcome rules, while Theorem 5.1 uses the source total rule. For a total rule, every admissible profile has an equilibrium; all existence guards in the Nash condition therefore hold, recovering precisely the source game. A total rule may fail to exist (e.g. all-zero linear reports remove every good and cannot spend positive budgets); the generalizations make that specification issue visible rather than relying solely on a vacuous total-rule hypothesis.
--
--   Differences from the source:
--   - generalization: Definition 3.1 total equilibrium-valued outcome rule → both the exact total class IsOutcomeRule and the explicitly broader IsPartialOutcomeRule; reason: every source total rule is partial; all existence guards in IsMechPNE hold under a source total rule, recovering the exact source game
--   - generalization: Appendix D.3 conditions on the nonnegative orthant → utilities and zero-coordinate marginal conditions only on the allocation box; reason: every source orthant utility restricts to these conditions; all admissible allocations lie in the box
--   - encoding: independent probability distributions, with the payoffs (20)–(23) written as sums → arbitrary Borel probability measures and product-measure integrals, with integrable compared payoffs in IsMixedNE; reason: includes discrete and atomless mixed strategies; the integrability clauses prevent totalized integrals from defining fake expectations
--   - reading: negative-rho CES and the rho=0 member included by Theorem 4.11 → explicit zero branch for an absent positively weighted good at negative rho, Cobb–Douglas at rho=0; reason: the continuous boundary convention and p. 24 Cobb–Douglas case; avoids Real.rpow totality at zero
--   - reading: demand for a free good in the perfect-competition condition → DependsOn on the box for each of two distinct buyers; reason: the brief pinned this coordinate-dependence reading to match the source positive-coefficient equivalence for linear and Leontief utilities
--   - reading: infinite partial derivative at zero and non-satiation → one-sided difference quotient tending to positive infinity, and StrictMonoOn in the product order; reason: utilities need not be differentiable; this is the source one-sided marginal and exact coordinatewise strict-order condition
--   - reading: affordable bundles and a possible zero Leontief report → nonnegative bundles (box for concave reports), and the published base u convention assigning utility zero to an empty demand set; reason: bundles are physical quantities; the source does not define a minimum over an empty demand set
--   - encoding: false universal purity claims D.2 and D.8 → explicit fixed counterexample instances and predicates LinearPurityFails/LeontiefPurityFails; reason: these predicates expose all source assumptions and the existence of a non-pure mixed equilibrium, used by the formal refutations
-- source:
--   Brânzei, Gkatzelis, Mehta, Nash Social Welfare Approximation for Strategic Agents, arXiv:1607.01569v3, pp. 6–8, 12, 25–28, §2, §3 (Definition 3.1), §4, Appendix D (Definition D.4, D.3)

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting

open Filter Topology MeasureTheory

namespace TradingPostNSW.Leontief.Supplement

open TradingPostNSW.Leontief

variable {n m : ℕ}

/-- The bundle box `[0,1]^m`, the domain of the utility functions (§2, p. 6). -/
def box (m : ℕ) : Set (Fin m → ℝ) := Set.Icc 0 1

/-- The nonnegative orthant `ℝ^m_{≥0}`: report vectors (Definition 3.1) and the bundles `y ≥ 0`
of the optimal-bundle condition for linear and Leontief utilities (p. 7). -/
def orthant (m : ℕ) : Set (Fin m → ℝ) := {y | ∀ j, 0 ≤ y j}

/-- Standing assumptions for a general utility profile (§2, p. 6): at least one good and budgets
`B_i ≥ 1`. The valuation field `v` of the instance is not used by general utilities. -/
structure GenStanding (I : Instance n m) : Prop where
  pos_m : 0 < m
  one_le_B : ∀ i, 1 ≤ I.B i

/-- Standing assumptions for linear (additive) valuations (§2, p. 6): at least one good,
`v_i ∈ ℝ^m_+` and budgets `B_i ≥ 1`. Unlike the base `Standing`, no agent is required to value
a good. -/
structure LinStanding (I : Instance n m) : Prop where
  pos_m : 0 < m
  v_nonneg : ∀ i j, 0 ≤ I.v i j
  one_le_B : ∀ i, 1 ≤ I.B i

/-- Linear (additive) utility `u_i(y) = Σ_j v_{i,j} y_j` (p. 6). -/
def linU (I : Instance n m) (i : Fin n) (y : Fin m → ℝ) : ℝ := ∑ j, I.v i j * y j

/-- The general utility class of §2 (p. 6): concave, non-decreasing and non-negative on the box
`[0,1]^m`. -/
def IsConcaveUtility (f : (Fin m → ℝ) → ℝ) : Prop :=
  ConcaveOn ℝ (box m) f ∧ MonotoneOn f (box m) ∧ ∀ x ∈ box m, 0 ≤ f x

/-- `f` depends on good `j`: two bundles of the box that differ only in coordinate `j` have
different utilities. -/
def DependsOn (f : (Fin m → ℝ) → ℝ) (j : Fin m) : Prop :=
  ∃ x ∈ box m, ∃ x' ∈ box m, (∀ k, k ≠ j → x k = x' k) ∧ f x ≠ f x'

/-- Perfect competition for a general utility profile (§4, p. 12): every good matters to two
distinct agents. For linear and Leontief valuations this is `v_{i,j} > 0, v_{k,j} > 0`. -/
def PerfectCompetitionU (U : Fin n → (Fin m → ℝ) → ℝ) : Prop :=
  ∀ j, ∃ i k, i ≠ k ∧ DependsOn (U i) j ∧ DependsOn (U k) j

/-- Infinite marginal utility of good `j` at zero (Appendix D.3, p. 28): at every bundle of the
box with `x_j = 0`, the right difference quotient in direction `e_j` tends to `+∞`. -/
def InfMarginalAtZero (f : (Fin m → ℝ) → ℝ) (j : Fin m) : Prop :=
  ∀ x ∈ box m, x j = 0 →
    Tendsto (fun t : ℝ => (f (x + t • (Pi.single j (1 : ℝ) : Fin m → ℝ)) - f x) / t)
      (𝓝[>] 0) atTop

/-- Enough competition (Appendix D.3, p. 28): every good has two distinct agents with infinite
marginal utility for it at zero. -/
def EnoughCompetition (U : Fin n → (Fin m → ℝ) → ℝ) : Prop :=
  ∀ j, ∃ i k, i ≠ k ∧ InfMarginalAtZero (U i) j ∧ InfMarginalAtZero (U k) j

/-- Weighted Nash social welfare `NSW_U(x) = (Π_i U_i(x_i)^{B_i})^{1/B}` of an allocation for a
utility profile `U` (p. 6); the base `NSW` is the Leontief case. -/
noncomputable def NSWU (I : Instance n m) (U : Fin n → (Fin m → ℝ) → ℝ)
    (x : Fin n → Fin m → ℝ) : ℝ :=
  (∏ i, (U i (x i)) ^ (I.B i)) ^ (1 / totalBudget I)

/-- Pure Nash equilibrium of the Trading Post game `TP(Δ)` for a utility profile `U` (`Δ = 0`
is the game without entrance fee, p. 12): every agent plays a strategy of `S_i`, and no
unilateral deviation within `S_i` raises its utility. The base `IsPNE` is the Leontief case. -/
def IsPNEU (I : Instance n m) (U : Fin n → (Fin m → ℝ) → ℝ) (Δ : ℝ)
    (b : Fin n → Fin m → ℝ) : Prop :=
  (∀ i, Strategy I i (b i)) ∧
    ∀ i (b' : Fin m → ℝ), Strategy I i b' →
      U i (tpAlloc Δ (Function.update b i b') i) ≤ U i (tpAlloc Δ b i)

/-- CES utility with parameter `ρ` (p. 7): `(Σ_{j ∈ D_i} v_{i,j} x_j^ρ)^{1/ρ}` for `ρ ≠ 0`,
with the continuous extension `0` when `ρ < 0` and some demanded good is absent; for `ρ = 0`
the Cobb–Douglas member `Π_j x_j^{v_{i,j}}`. -/
noncomputable def ces (I : Instance n m) (ρ : ℝ) (i : Fin n) (x : Fin m → ℝ) : ℝ :=
  if ρ = 0 then ∏ j, x j ^ I.v i j
  else if ρ < 0 ∧ ∃ j, 0 < I.v i j ∧ x j = 0 then 0
  else (∑ j ∈ D I i, I.v i j * x j ^ ρ) ^ (1 / ρ)

/-- Fisher market equilibrium (p. 7, conditions (1)–(2)) of budgets `B` and utilities `w`, with
the optimal-bundle condition over the bundles `y ∈ dom`: prices and allocation are nonnegative,
no good is oversold, every good with a positive price is sold, every buyer spends its budget, and
every affordable bundle of `dom` is worth at most the buyer's own. -/
structure IsMarketEq (B : Fin n → ℝ) (w : Fin n → (Fin m → ℝ) → ℝ) (dom : Set (Fin m → ℝ))
    (p : Fin m → ℝ) (x : Fin n → Fin m → ℝ) : Prop where
  p_nonneg : ∀ j, 0 ≤ p j
  x_nonneg : ∀ i j, 0 ≤ x i j
  supply : ∀ j, ∑ i, x i j ≤ 1
  sold : ∀ j, 0 < p j → ∑ i, x i j = 1
  budget : ∀ i, ∑ j, x i j * p j = B i
  opt : ∀ i, ∀ y ∈ dom, ∑ j, p j * y j ≤ B i → w i y ≤ w i (x i)

/-- Reported linear utilities `y ↦ Σ_j s_{i,j} y_j` of a report profile `s`. -/
def linRep (s : Fin n → Fin m → ℝ) (i : Fin n) (y : Fin m → ℝ) : ℝ := ∑ j, s i j * y j

/-- Reported Leontief utilities of a report profile `s`: the base Leontief utility of the
instance with coefficients `s` and the true budgets. -/
noncomputable def leoRep (I : Instance n m) (s : Fin n → Fin m → ℝ) (i : Fin n)
    (y : Fin m → ℝ) : ℝ :=
  u ⟨s, I.B⟩ i y

/-- An outcome of the Fisher Market Mechanism (Definition 3.1, p. 7) at report profile `s`: a
market equilibrium of the reported market `⟨B_i, s_i⟩` after removing the goods `j` with
`Σ_i s_i(j) = 0`, written on all goods with price `0` and nobody holding a removed good. -/
def IsMechEq (B : Fin n → ℝ) (rep : (Fin n → Fin m → ℝ) → Fin n → (Fin m → ℝ) → ℝ)
    (s : Fin n → Fin m → ℝ) (p : Fin m → ℝ) (x : Fin n → Fin m → ℝ) : Prop :=
  IsMarketEq B (rep s) (orthant m) p x ∧ ∀ j, ∑ i, s i j = 0 → p j = 0 ∧ ∀ i, x i j = 0

/-- Fisher Market Mechanism outcomes for linear reports. -/
def linMechEq (I : Instance n m) (s : Fin n → Fin m → ℝ) (p : Fin m → ℝ)
    (x : Fin n → Fin m → ℝ) : Prop :=
  IsMechEq I.B linRep s p x

/-- Fisher Market Mechanism outcomes for Leontief reports. -/
def leoMechEq (I : Instance n m) (s : Fin n → Fin m → ℝ) (p : Fin m → ℝ)
    (x : Fin n → Fin m → ℝ) : Prop :=
  IsMechEq I.B (leoRep I) s p x

/-- Fisher market equilibria for reported concave utility functions `W` (bundles in the box). -/
def concaveMarketEq (I : Instance n m) (W : Fin n → (Fin m → ℝ) → ℝ) (p : Fin m → ℝ)
    (x : Fin n → Fin m → ℝ) : Prop :=
  IsMarketEq I.B W (box m) p x

/-- The total equilibrium-valued outcome rule of Definition 3.1.
This specification may be unsatisfiable (e.g. the all-zero linear report removes every good).
The supplement separately names a broader partial-rule class rather than silently changing this one. -/
def IsOutcomeRule {R : Type*} (Adm : R → Prop)
    (E : (Fin n → R) → (Fin m → ℝ) → (Fin n → Fin m → ℝ) → Prop)
    (O : (Fin n → R) → (Fin m → ℝ) × (Fin n → Fin m → ℝ)) : Prop :=
  ∀ s : Fin n → R, (∀ i, Adm (s i)) → E s (O s).1 (O s).2

/-- Generalized partial outcome rules: at every admissible profile whose reported market has
an equilibrium, the rule returns one. Every source total outcome rule satisfies this predicate. -/
def IsPartialOutcomeRule {R : Type*} (Adm : R → Prop)
    (E : (Fin n → R) → (Fin m → ℝ) → (Fin n → Fin m → ℝ) → Prop)
    (O : (Fin n → R) → (Fin m → ℝ) × (Fin n → Fin m → ℝ)) : Prop :=
  ∀ s : Fin n → R, (∀ i, Adm (s i)) → (∃ p x, E s p x) → E s (O s).1 (O s).2

/-- The selection clause of Definition 3.1: if some equilibrium of the reported market is weakly
preferred by every agent, with respect to the true utilities `U`, to every other equilibrium,
then the rule returns such an equilibrium. -/
def SelectsPreferred {R : Type*} (Adm : R → Prop)
    (E : (Fin n → R) → (Fin m → ℝ) → (Fin n → Fin m → ℝ) → Prop)
    (U : Fin n → (Fin m → ℝ) → ℝ)
    (O : (Fin n → R) → (Fin m → ℝ) × (Fin n → Fin m → ℝ)) : Prop :=
  ∀ s : Fin n → R, (∀ i, Adm (s i)) →
    (∃ p x, E s p x ∧ ∀ p' x', E s p' x' → ∀ i, U i (x' i) ≤ U i (x i)) →
      ∀ p' x', E s p' x' → ∀ i, U i (x' i) ≤ U i ((O s).2 i)

/-- Pure Nash equilibrium of the Fisher Market Mechanism with outcome rule `O` and true
utilities `U`: the reports are admissible, the reported market has an equilibrium, and no agent
gains by a unilateral change to another admissible report at which the mechanism is defined.
For a source total outcome rule all existence guards hold, so this is exactly the source Nash condition. -/
def IsMechPNE {R : Type*} (Adm : R → Prop)
    (E : (Fin n → R) → (Fin m → ℝ) → (Fin n → Fin m → ℝ) → Prop)
    (U : Fin n → (Fin m → ℝ) → ℝ)
    (O : (Fin n → R) → (Fin m → ℝ) × (Fin n → Fin m → ℝ)) (s : Fin n → R) : Prop :=
  (∀ i, Adm (s i)) ∧ (∃ p x, E s p x) ∧
    ∀ i (r : R), Adm r → (∃ p x, E (Function.update s i r) p x) →
      U i ((O (Function.update s i r)).2 i) ≤ U i ((O s).2 i)

/-- Point mass, viewed as a probability measure on the Borel space of bid vectors. -/
noncomputable def pureBid (b : Fin m → ℝ) : ProbabilityMeasure (Fin m → ℝ) :=
  ⟨Measure.dirac b, Measure.dirac.isProbabilityMeasure⟩

/-- Independent joint distribution of general (possibly atomless) mixed strategies. -/
noncomputable def joint (σ : Fin n → ProbabilityMeasure (Fin m → ℝ)) :
    Measure (Fin n → Fin m → ℝ) :=
  Measure.pi (fun k => (σ k : Measure (Fin m → ℝ)))

/-- Expected utility in TP(Δ), with no countability restriction on mixed strategies. -/
noncomputable def expPay (U : Fin n → (Fin m → ℝ) → ℝ) (Δ : ℝ)
    (σ : Fin n → ProbabilityMeasure (Fin m → ℝ)) (i : Fin n) : ℝ :=
  ∫ s, U i (tpAlloc Δ s i) ∂joint σ

/-- Mixed Nash equilibrium: bids are admissible almost surely; every expected payoff being
compared exists as an integrable real random variable; no pure deviation is profitable.
Integrability expresses that these are actual expectations rather than totalized integral junk. -/
def IsMixedNE (I : Instance n m) (U : Fin n → (Fin m → ℝ) → ℝ) (Δ : ℝ)
    (σ : Fin n → ProbabilityMeasure (Fin m → ℝ)) : Prop :=
  (∀ i, ∀ᵐ b ∂(σ i : Measure (Fin m → ℝ)), Strategy I i b) ∧
    (∀ i, Integrable (fun s => U i (tpAlloc Δ s i)) (joint σ)) ∧
    ∀ i (b' : Fin m → ℝ), Strategy I i b' →
      Integrable (fun s => U i (tpAlloc Δ s i))
        (joint (Function.update σ i (pureBid b'))) ∧
      expPay U Δ (Function.update σ i (pureBid b')) i ≤ expPay U Δ σ i

/-- Purity means every marginal distribution is a point mass. -/
def IsPure (σ : Fin n → ProbabilityMeasure (Fin m → ℝ)) : Prop :=
  ∀ i, ∃ b, σ i = pureBid b

/-- The nonzero-demand linear counterexample to Theorems D.2 and 4.12. -/
noncomputable def linearRefutationInstance : Instance 3 2 where
  v := fun i j => if i = 0 then (if j = 0 then 1 else 0)
    else if i = 1 then (if j = 0 then 1/10 else 1)
    else (if j = 0 then 0 else 1)
  B := fun _ => 1

/-- The large-fee Leontief counterexample to Theorems D.8 and 4.12. -/
def feeRefutationInstance : Instance 2 2 where
  v := fun _ _ => 1
  B := fun _ => 1

/-- Full refutation, preserving the source assumptions, rather than a restricted purity claim. -/
def LinearPurityFails : Prop :=
  let I := linearRefutationInstance
  LinStanding I ∧ PerfectCompetition I ∧ (∀ i, ∃ j, 0 < I.v i j) ∧
    ∃ σ : Fin 3 → ProbabilityMeasure (Fin 2 → ℝ),
      IsMixedNE I (linU I) 0 σ ∧ ¬ IsPure σ

/-- Fee 2 is positive and exceeds both budgets, so no effective bid is possible. -/
def LeontiefPurityFails : Prop :=
  let I := feeRefutationInstance
  Standing I ∧ PerfectCompetition I ∧
    ∃ σ : Fin 2 → ProbabilityMeasure (Fin 2 → ℝ),
      IsMixedNE I (u I) 2 σ ∧ ¬ IsPure σ

end TradingPostNSW.Leontief.Supplement


