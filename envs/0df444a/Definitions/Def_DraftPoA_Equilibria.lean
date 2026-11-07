-- Prove2me | Definitions.Def_DraftPoA_Equilibria
-- name    : DraftPoA_Equilibria
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:38:14.861476+00:00
-- url     : https://prove2.me/theorems/15881004-cf82-411c-b76d-18df46fcc588
-- title:
--   Pure, mixed, correlated, Bayes–Nash and subgame-perfect equilibria; the price of anarchy
-- statement:
--   Equilibrium concepts of the draft auction and its price of anarchy.
--
--   1. **Pure Nash.** $u_i(b)\ge u_i(b_i',b_{-i})$ for every bidder $i$ and every pure strategy $b_i'$.
--   2. **Pure SPE.** The same inequality in the subgame at every legal node at which an item remains. A *one-shot deviation* at a node changes a bidder's action at that node only.
--   3. **Mixed Nash.** Each bidder draws her pure strategy $b_i(\omega_i)$ from a private probability space $(\Omega_i,\mu_i)$, independently; $\mathbb E[u_i(b)]\ge\mathbb E[u_i(b_i',b_{-i})]$ for every (possibly mixed) deviation $b_i'$, a function of $\omega_i$.
--   4. **Correlated.** A pure profile $b(\omega)$ is drawn from $(\Omega,\mu)$ and each bidder is told her $b_i$; $\mathbb E[u_i(b)]\ge\mathbb E[u_i(g(b_i),b_{-i})]$ for every function $g$ from pure strategies to pure strategies.
--   5. **Bayes–Nash.** Types $t_i$ are drawn independently from priors $F_i$, bidder $i$ of type $t_i$ has valuation $V_i(t_i)$, and a (mixed) strategy maps types to strategies; for every $i$, every type $t_i$ and every pure strategy $s$, the conditional expectation of $u_i$ given $t_i$ under $(b_i(t_i),b_{-i}(\cdot))$ is at least that under $(s,b_{-i}(\cdot))$.
--
--   For a class of instances and a concept, the **price of anarchy** is
--
--   $$\mathrm{PoA}=\sup\frac{\mathbb E[\mathrm{OPT}]}{\mathbb E[\mathrm{SW}]},$$
--
--   the supremum over all numbers of bidders, priority orders, caps $\bar M$, instances of the class capped by $\bar M$, and equilibria of the concept.
--
--   **Formalization Note** With $\delta=0$ the node space is uncountable, so random profiles are probability spaces mapping to pure profiles, with the outcome map (buyer and price of every item) measurable, as the paper requires ("strategies are measurable, so that the expectations below are defined", p.18). No measurability is imposed on deviations: the inequality is required in lower-integral form, $\int h\le\mathbb E[u_i(b)]$ for every bounded measurable $h$ below the deviation's utility, which is the printed inequality whenever the deviation's utility is measurable. The conditional expectation given $t_i$ is the integral over the product law with $i$'s type frozen at $t_i$. PoA is computed in $[0,\infty]$, with $a/0=\infty$ for $a>0$ and $0/0=0$.
-- source:
--   Truong, Thach, Chan, Guo, The Price of Anarchy of Draft Auctions, STOC 2027 submission (manuscript sha256 270ffdaa…), §2 "Equilibrium concepts" and "Price of anarchy", p.5 (PDF 6); App. A.3, p.18 (PDF 19); App. E, pp.32–33 (PDF 33–34)

import Mathlib
import Definitions.Def_DraftPoA_Auction

open MeasureTheory

namespace DraftPoA

/-!
# Equilibrium concepts and the price of anarchy of the draft auction

H. T. Truong, N. Thach, H. Chan, M. Guo, *The Price of Anarchy of Draft Auctions*, STOC 2027
submission (manuscript sha256 270ffdaa…), §2 "Equilibrium concepts" and "Price of anarchy and
price of stability", p.5 (PDF 6); App. A.3 "Bayes–Nash equilibria: assumptions", p.18 (PDF 19);
App. E, pp.32–33 (PDF 33–34).

**Formalization Note.**
* *Pure Nash* and *pure SPE* compare against every pure strategy of the deviator. For a pure
  profile, a mixed or behavior deviation is an average of pure ones, so this is the printed
  condition. `IsPureSPE` asks for it in the subgame at every legal node at which an item remains;
  strategies live on public nodes, so these are the perfect public equilibria of App. E.
* *Random profiles.* With `δ = 0` the node space is uncountable and evaluation of a strategy at a
  random node is not jointly measurable for any useful σ-algebra on strategies, so a random
  profile is a probability space `(Ω, μ)` with a map to pure profiles, and the outcome map
  `ω ↦ (buyer, price of every item)` is required to be measurable (App. A.3: "strategies are
  measurable, so that the expectations below are defined").
  - Mixed Nash: one device `(Ω_i, μ_i)` per bidder, product law; bidder `i` may deviate to any
    function `Ω_i → Strategy` (a mixed strategy on her device; pure ones are the constants).
  - Correlated: one device `(Ω, μ)`; bidder `i` may deviate to `g ∘ b_i` for **every function**
    `g` from pure strategies to pure strategies, as printed.
  - Bayes–Nash: types `T_i` with independent priors `F_i`, valuations `V_i t`, a device
    `(Ω_i, μ_i)` for mixing, strategies `b_i : T_i → Ω_i → Strategy`; for every bidder, **every**
    type and every pure deviation, the conditional expectation given the type is compared. The
    conditional expectation given `t_i` is the integral over the full product with bidder `i`'s
    type coordinate replaced by `t_i` (independence of the priors).
  - No measurability is imposed on deviations. The inequality "E[u(deviation)] ≤ E[u(b)]" is
    written in lower-integral form: every bounded measurable `h` below the deviation's utility has
    `∫ h ≤ E[u(b)]`. Whenever the deviation's utility is measurable this is exactly the printed
    inequality (take `h` equal to it; utilities are bounded by `m M̄` in absolute value).
* `outcomes c cls m δ` is the set of pairs `(E[OPT], E[SW])` over all numbers `n + 1 ≥ 1` of
  bidders, all priority orders, all caps `M̄`, all instances of the class capped by `M̄` (every
  type, in the Bayesian case) and all equilibria of concept `c` on the grid `(δ, M̄)`.
* `poa c cls m δ = sup E[OPT]/E[SW]` is computed in `ℝ≥0∞`: `a/0 = ⊤` for `a > 0`, and the
  degenerate all-zero ratio `0/0` counts as `0` (the paper does not discuss it; every bound in
  the paper is at least `1`).
-/

open ComplementFreeCA.CFRounding

variable {n m : ℕ}

/-- A pure Nash equilibrium: no bidder gains by switching to another pure strategy (p.5). -/
def IsPureNash [NeZero n] {δ Mbar : ℝ} (prio : Equiv.Perm (Fin n))
    (v : Fin n → Finset (Fin m) → ℝ) (b : Fin n → Strategy n m δ Mbar) : Prop :=
  ∀ (i : Fin n) (s : Strategy n m δ Mbar), u prio v (Function.update b i s) i ≤ u prio v b i

/-- A pure subgame-perfect equilibrium: a pure Nash equilibrium of the subgame at every legal
node at which an item remains (p.5; App. E). -/
def IsPureSPE [NeZero n] {δ Mbar : ℝ} (prio : Equiv.Perm (Fin n))
    (v : Fin n → Finset (Fin m) → ℝ) (b : Fin n → Strategy n m δ Mbar) : Prop :=
  ∀ ν : Node n m, IsNode δ Mbar ν → (remaining ν).Nonempty →
    ∀ (i : Fin n) (s : Strategy n m δ Mbar),
      uFrom prio v (Function.update b i s) ν i ≤ uFrom prio v b ν i

/-- Bidder `i` has no profitable one-shot deviation at node `ν`: no strategy that differs from
`b i` only at `ν` raises her utility in the subgame at `ν` (p.5). -/
def NoProfitableOneShot [NeZero n] {δ Mbar : ℝ} (prio : Equiv.Perm (Fin n))
    (v : Fin n → Finset (Fin m) → ℝ) (b : Fin n → Strategy n m δ Mbar) (i : Fin n)
    (ν : Node n m) : Prop :=
  ∀ s : Strategy n m δ Mbar, (∀ ν', ν' ≠ ν → s.act ν' = (b i).act ν') →
    uFrom prio v (Function.update b i s) ν i ≤ uFrom prio v b ν i

/-- A mixed Nash equilibrium on devices `(Ω_i, μ_i)` with the product law (p.5; reading of
App. A.3). -/
def IsMixedNash [NeZero n] {δ Mbar : ℝ} (prio : Equiv.Perm (Fin n))
    (v : Fin n → Finset (Fin m) → ℝ) {Ω : Fin n → Type*} [∀ i, MeasurableSpace (Ω i)]
    (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (b : ∀ i, Ω i → Strategy n m δ Mbar) : Prop :=
  Measurable (fun ω : (∀ i, Ω i) => outcomeMap (play prio fun j => b j (ω j))) ∧
  ∀ (i : Fin n) (dev : Ω i → Strategy n m δ Mbar) (h : (∀ j, Ω j) → ℝ),
    Measurable h → (∃ C, ∀ ω, |h ω| ≤ C) →
    (∀ ω, h ω ≤ u prio v (Function.update (fun j => b j (ω j)) i (dev (ω i))) i) →
    ∫ ω, h ω ∂(Measure.pi μ) ≤ ∫ ω, u prio v (fun j => b j (ω j)) i ∂(Measure.pi μ)

/-- A correlated equilibrium: a law `μ` on `Ω` and a recommended pure profile `rec ω`; each
bidder, told her own strategy, cannot gain by any function `g` of it (p.5). -/
def IsCorrelatedEq [NeZero n] {δ Mbar : ℝ} (prio : Equiv.Perm (Fin n))
    (v : Fin n → Finset (Fin m) → ℝ) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (rec : Ω → Fin n → Strategy n m δ Mbar) : Prop :=
  Measurable (fun ω => outcomeMap (play prio (rec ω))) ∧
  ∀ (i : Fin n) (g : Strategy n m δ Mbar → Strategy n m δ Mbar) (h : Ω → ℝ),
    Measurable h → (∃ C, ∀ ω, |h ω| ≤ C) →
    (∀ ω, h ω ≤ u prio v (Function.update (rec ω) i (g (rec ω i))) i) →
    ∫ ω, h ω ∂μ ≤ ∫ ω, u prio v (rec ω) i ∂μ

/-- The joint law of types and devices: `⊗_i (F_i ⊗ μ_i)`. -/
noncomputable def typeDeviceLaw {T Ω : Fin n → Type*} [∀ i, MeasurableSpace (T i)]
    [∀ i, MeasurableSpace (Ω i)] (F : ∀ i, Measure (T i)) (μ : ∀ i, Measure (Ω i))
    [∀ i, SigmaFinite (F i)] [∀ i, SigmaFinite (μ i)] : Measure (∀ i, T i × Ω i) :=
  Measure.pi fun i => (F i).prod (μ i)

/-- The pure profile realized at a draw `x` of types and device states. -/
def profileAt {δ Mbar : ℝ} {T Ω : Fin n → Type*} (b : ∀ i, T i → Ω i → Strategy n m δ Mbar)
    (x : ∀ i, T i × Ω i) : Fin n → Strategy n m δ Mbar :=
  fun j => b j (x j).1 (x j).2

/-- A Bayes–Nash equilibrium with independent priors `F_i` on type spaces `T_i`, valuations
`V_i t`, mixing devices `(Ω_i, μ_i)` and strategies `b_i : T_i → Ω_i → Strategy` (p.5; App. A.3,
p.18). For every bidder `i`, every type `t` and every pure strategy `s`, the expected utility of
type `t` under `(b_i(t), b_{−i}(·))` is at least that under `(s, b_{−i}(·))`. -/
def IsBayesNash [NeZero n] {δ Mbar : ℝ} (prio : Equiv.Perm (Fin n))
    {T Ω : Fin n → Type*} [∀ i, MeasurableSpace (T i)] [∀ i, MeasurableSpace (Ω i)]
    (F : ∀ i, Measure (T i)) (μ : ∀ i, Measure (Ω i))
    [∀ i, IsProbabilityMeasure (F i)] [∀ i, IsProbabilityMeasure (μ i)]
    (V : ∀ i, T i → Finset (Fin m) → ℝ) (b : ∀ i, T i → Ω i → Strategy n m δ Mbar) : Prop :=
  Measurable (fun x : (∀ i, T i × Ω i) => outcomeMap (play prio (profileAt b x))) ∧
  ∀ (i : Fin n) (t : T i) (s : Strategy n m δ Mbar) (h : (∀ j, T j × Ω j) → ℝ),
    Measurable h → (∃ C, ∀ x, |h x| ≤ C) →
    (∀ x, h x ≤ uAt (V i t) (play prio (Function.update (profileAt b x) i s)) i) →
    ∫ x, h x ∂(typeDeviceLaw F μ) ≤
      ∫ x, uAt (V i t) (play prio (profileAt b (Function.update x i (t, (x i).2)))) i
        ∂(typeDeviceLaw F μ)

/-- The equilibrium concepts of §2: pure Nash, mixed Nash, correlated, Bayes–Nash and pure SPE. -/
inductive Concept
  | pureNash
  | mixedNash
  | correlated
  | bayesNash
  | pureSPE

/-- The pairs `(E[OPT], E[SW])` of all equilibria of concept `c` with `m` items, valuations in
`cls`, bid increment `δ`, over every number of bidders `n + 1 ≥ 1`, every priority order and every
cap `M̄` (pp.4–5). -/
def outcomes (c : Concept) (cls : ValClass) (m : ℕ) (δ : ℝ) : Set (ℝ × ℝ) :=
  {x | ∃ (n : ℕ) (prio : Equiv.Perm (Fin (n + 1))) (Mbar : ℝ),
    match c with
    | .pureNash => ∃ (v : Fin (n + 1) → Finset (Fin m) → ℝ) (b : Fin (n + 1) → Strategy (n + 1) m δ Mbar),
        (∀ i, cls.Mem (v i)) ∧ IsCapped v Mbar ∧ IsPureNash prio v b ∧ x = (OPT v, SW prio v b)
    | .pureSPE => ∃ (v : Fin (n + 1) → Finset (Fin m) → ℝ) (b : Fin (n + 1) → Strategy (n + 1) m δ Mbar),
        (∀ i, cls.Mem (v i)) ∧ IsCapped v Mbar ∧ IsPureSPE prio v b ∧ x = (OPT v, SW prio v b)
    | .mixedNash => ∃ (v : Fin (n + 1) → Finset (Fin m) → ℝ) (Ω : Fin (n + 1) → Type)
        (_ : ∀ i, MeasurableSpace (Ω i)) (μ : ∀ i, Measure (Ω i))
        (_ : ∀ i, IsProbabilityMeasure (μ i)) (b : ∀ i, Ω i → Strategy (n + 1) m δ Mbar),
        (∀ i, cls.Mem (v i)) ∧ IsCapped v Mbar ∧ IsMixedNash prio v μ b ∧
        x = (OPT v, ∫ ω, SW prio v (fun j => b j (ω j)) ∂(Measure.pi μ))
    | .correlated => ∃ (v : Fin (n + 1) → Finset (Fin m) → ℝ) (Ω : Type) (_ : MeasurableSpace Ω)
        (μ : Measure Ω) (_ : IsProbabilityMeasure μ) (rec : Ω → Fin (n + 1) → Strategy (n + 1) m δ Mbar),
        (∀ i, cls.Mem (v i)) ∧ IsCapped v Mbar ∧ IsCorrelatedEq prio v μ rec ∧
        x = (OPT v, ∫ ω, SW prio v (rec ω) ∂μ)
    | .bayesNash => ∃ (T : Fin (n + 1) → Type) (_ : ∀ i, MeasurableSpace (T i))
        (F : ∀ i, Measure (T i)) (_ : ∀ i, IsProbabilityMeasure (F i))
        (V : ∀ i, T i → Finset (Fin m) → ℝ)
        (Ω : Fin (n + 1) → Type) (_ : ∀ i, MeasurableSpace (Ω i)) (μ : ∀ i, Measure (Ω i))
        (_ : ∀ i, IsProbabilityMeasure (μ i)) (b : ∀ i, T i → Ω i → Strategy (n + 1) m δ Mbar),
        (∀ i t, cls.Mem (V i t)) ∧ (∀ i t j, V i t {j} ≤ Mbar) ∧
        (∀ i S, Measurable fun t => V i t S) ∧
        IsBayesNash prio F μ V b ∧
        x = (∫ y, OPT (fun j => V j (y j).1) ∂(typeDeviceLaw F μ),
             ∫ y, SW prio (fun j => V j (y j).1) (profileAt b y) ∂(typeDeviceLaw F μ))}

/-- The price of anarchy: the supremum of `E[OPT]/E[SW]` over `outcomes c cls m δ`, in `ℝ≥0∞`
(p.5). -/
noncomputable def poa (c : Concept) (cls : ValClass) (m : ℕ) (δ : ℝ) : ENNReal :=
  ⨆ x ∈ outcomes c cls m δ, ENNReal.ofReal x.1 / ENNReal.ofReal x.2

end DraftPoA


