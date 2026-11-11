-- Prove2me | Definitions.Def_SingleSampleCombPI_XOS_Online
-- name    : SingleSampleCombPI_XOS_Online
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T09:08:35.425346+00:00
-- url     : https://prove2.me/theorems/5908efed-4ec0-4f94-b6ca-9da9d97e4eba
-- title:
--   §3 — Game of Googol, online algorithms, buyer-locality, smooth competitiveness, Algorithms 1–3
-- statement:
--   This file defines the online model and the reduction of §3.
--
--   1. **Game of Googol.** With one sample, the adversary fixes a pair of buyer types per buyer and an independent fair coin assigns them to (sample, real). With $k$ samples, $k+1$ values per buyer are permuted uniformly into $k$ sample slots and one real slot. Real buyers arrive in a fixed order $\rho$; an online algorithm sees, when buyer $i$ arrives, only the samples, the earlier real arrivals and $i$'s own real type.
--   2. **Single-item $k$-sample algorithms** ($k$-SPI, SSPI for $k=1$). A randomized online rule allocating to each arriving single-item buyer. It is valid if its output is always feasible on valid inputs, and $\beta$-competitive under order $\rho$ if $\beta\in[0,1]$ and for every adversarial family $\mathbb E[\sum_iq(r_i)y_i]\ge\beta\,\mathbb E[\mathrm{Opt}(r)]$.
--   3. **Online free-disposal algorithms** (FDAlg). A state machine with randomized initial state; each step takes the next buyer and returns a provisional allocation in $A^m$ and the next state. Run in a processing order $\pi$, its state before buyer $i$ is saved. It is $\alpha$-competitive (random order) if $\mathbb E_\pi\mathbb E[\mathrm{FD}]\ge\alpha\,\mathrm{Opt}(v)$. **Smooth competitive ratio $\Gamma$** (Definition 10): $\Gamma:[0,1]\to[0,1]$ is increasing and, for every profile $v$ and $q\in[0,1]$, keeping each buyer independently with probability $q$ and replacing it by the zero buyer otherwise, then running FDAlg in uniformly random order on this profile $v'$, gives $\mathbb E[\mathrm{FD}]\ge\Gamma(q)\,\mathrm{Opt}(v)$, with FD evaluated on $v'$.
--   4. **Buyer-local provisional allocation** (Definitions 8–9). Given the coordination sample $s^c$ and shared randomness, buyer $i$'s provisional allocation $\mathrm{PAlloc}_i(s^c,r_i)\in A^m$ depends only on $r_i$. It is $\alpha$-competitive under free disposal if, for every family of pairs ordered by fair coins into $(s^c_i,r_i)$, $\mathbb E[\mathrm{FD}(\mathrm{PAlloc}(s^c,r))]\ge\alpha\,\mathbb E[\mathrm{Opt}(r)]$.
--   5. **Algorithm 1.** Each sample profile is transformed by PAlloc with the same randomness; item $j$'s $k$-SPI instance (independent randomness) receives the per-item pairs $(q_{i,j}(x_i),x_{i,j})$ of the transformed samples and, online, of the transformed real buyers, and returns $x'_{i,j}\le\hat x_{i,j}$.
--   6. **Algorithm 2 (replay).** Draw a uniform order $\pi$ and FDAlg's randomness, run FDAlg on the coordination sample in order $\pi$ saving its state before each buyer; $\mathrm{PAlloc}_i(s^c,r_i)$ is FDAlg's allocation for $r_i$ from buyer $i$'s saved state.
--   7. **Algorithm 3.** Independent coins $H_i\sim\mathrm{Bernoulli}(q)$; coordinating buyers ($H_i=1$) give $(s^c_i,s^1_i,r_i)=(s'_i,0,0)$, competing buyers $(0,s'_i,r'_i)$; run Algorithm 1 with $k=1$ and the replay PAlloc, and allocate $0$ to coordinating buyers. The analysis quantities are $x_i=\mathrm{PAlloc}_i(s^c,r_i)$ and $z_i=\mathrm{PAlloc}_i(s^c,s^c_i)$.
--
--   Costs: one execution of Algorithm 3 is charged its role coins and zeroing, the order draw, seeds, the FDAlg sample run, one FDAlg call and one supporting-price query per transformed sample buyer and per real buyer, the per-item extraction and aggregation, and every single-item decision.
--
--   **Formalization Note** Internal seeds have arbitrary probability laws, including atomless laws. Expectations are nonnegative lower integrals in $[0,\infty]$, with finite external choices averaged inside seed integrals and independent item seeds integrated successively. For measurable source payoffs this is ordinary expectation. Online-ness is structural: a decision receives only the arrivals before it.
-- source:
--   Shuchi Chawla, Trung Dang, STOC 2027 submission #30 (October 2026), SHA-256 d6ed330221fdb64a0d8f70c7d0abbd3346ee1cb8f9e101a745f7e1e57d35230e, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/30.pdf, §§2.1, 2.4, 3.1–3.4, PDF pp. 8–19 (printed pp. 6–17), Definitions 8–10, Algorithms 1–3

import Mathlib
import Definitions.Def_SingleSampleCombPI_XOS_Model

open scoped ENNReal

namespace SingleSampleCombPI.XOS

/-! # Online algorithms, Game of Googol, and the reductions (Algorithms 1–3, Definitions 8–10)

Chawla–Dang, STOC 2027 submission #30, §§2.1, 2.4, 3.1–3.3.  All randomness is explicit:
fair swap coins of the Game of Googol, uniform permutations, Bernoulli role coins and each
algorithm's own internal randomness (an arbitrary probability space `seed`). -/

/-! ## Game of Googol assignments -/

/-- Single-sample Game of Googol: the fair coin `c` assigns the adversary's pair `V` to
`(sample, real)`. -/
def gogPair {α : Type*} (V : Fin 2 → α) (c : Bool) : α × α :=
  if c then (V 1, V 0) else (V 0, V 1)

/-- `k`-sample Game of Googol with `k+1` fixed values per buyer and uniformly random
permutations `σ i`: sample `t` of buyer `i`. -/
def gogSamples {α : Type*} {n k : ℕ} (V : Fin n → Fin (k + 1) → α)
    (σ : Fin n → Equiv.Perm (Fin (k + 1))) : Fin k → Fin n → α :=
  fun t i => V i (σ i t.castSucc)

/-- `k`-sample Game of Googol: the real value of buyer `i`. -/
def gogReal {α : Type*} {n k : ℕ} (V : Fin n → Fin (k + 1) → α)
    (σ : Fin n → Equiv.Perm (Fin (k + 1))) : Fin n → α :=
  fun i => V i (σ i (Fin.last k))

/-- Arrivals before buyer `i` under the arrival order `ρ` (`ρ t` arrives at time `t`):
the revealed `(buyer, real type)` pairs, in arrival order. -/
def prefixOf {α : Type*} {n : ℕ} (ρ : Equiv.Perm (Fin n)) (r : Fin n → α) (i : Fin n) :
    List (Fin n × α) :=
  ((List.finRange n).filter (fun t => t < ρ.symm i)).map (fun t => (ρ t, r (ρ t)))

/-! ## Single-item `k`-sample algorithms (`k`-SPI, SSPI for `k = 1`) -/

/-- A randomized online single-item algorithm with `k` samples: its allocation to the
arriving buyer `i` depends on its random seed, the `k` sample profiles, the previously
revealed real arrivals, and `i`'s own real item — never on future arrivals.  The cost fields
report the primitive operations of drawing the seed and of each decision. -/
structure KSPI (A : Regime) (n k : ℕ) where
  /-- internal randomness -/
  Ω : Type
  /-- its distribution -/
  seed : RandomSource Ω
  /-- the online decision rule -/
  act : Ω → (Fin k → Fin n → Item) → List (Fin n × Item) → Fin n → Item → ℝ
  /-- primitive operations to draw the seed -/
  seedCost : ℕ
  /-- primitive operations of one decision -/
  actCost : Ω → (Fin k → Fin n → Item) → List (Fin n × Item) → Fin n → Item → ℕ

/-- The allocation of a `k`-SPI run on real items `r` arriving in order `ρ`. -/
def spiRun {A : Regime} {n k : ℕ} (S : KSPI A n k) (ω : S.Ω) (s : Fin k → Fin n → Item)
    (ρ : Equiv.Perm (Fin n)) (r : Fin n → Item) : Fin n → ℝ :=
  fun i => S.act ω s (prefixOf ρ r i) i (r i)

/-- Total primitive operations of a `k`-SPI run. -/
def spiCost {A : Regime} {n k : ℕ} (S : KSPI A n k) (ω : S.Ω) (s : Fin k → Fin n → Item)
    (ρ : Equiv.Perm (Fin n)) (r : Fin n → Item) : ℕ :=
  S.seedCost + ∑ i, S.actCost ω s (prefixOf ρ r i) i (r i)

/-- The algorithm always outputs a feasible allocation on valid inputs. -/
def KSPI.Valid {A : Regime} {n k : ℕ} (S : KSPI A n k) : Prop :=
  ∀ ω s ρ r, (∀ t i, ItemValid A (s t i)) → (∀ i, ItemValid A (r i)) →
    ItemFeasible A r (spiRun S ω s ρ r)

/-- `β`-competitiveness in the single-item `k`-sample Game of Googol (§2.4) when the real
buyers arrive in the fixed order `ρ`, for every adversarial family of `k+1` items per buyer. -/
def KSPI.Competitive {A : Regime} {n k : ℕ} (S : KSPI A n k) (β : ℝ)
    (ρ : Equiv.Perm (Fin n)) : Prop :=
  β ∈ Set.Icc (0 : ℝ) 1 ∧
  ∀ V : Fin n → Fin (k + 1) → Item, (∀ i t, ItemValid A (V i t)) →
    ENNReal.ofReal β * avg (fun σ : Fin n → Equiv.Perm (Fin (k + 1)) =>
        ENNReal.ofReal (itemOpt A (gogReal V σ))) ≤
      pexp S.seed (fun ω => avg (fun σ : Fin n → Equiv.Perm (Fin (k + 1)) =>
        ENNReal.ofReal (∑ i, (gogReal V σ i).1 * spiRun S ω (gogSamples V σ) ρ (gogReal V σ) i)))

/-! ## Online free-disposal algorithms (FDAlg) -/

/-- An online free-disposal algorithm as a state machine: an initial state drawn with its
internal randomness, and a step that, given the current state and the next buyer, returns a
buyer-feasible provisional allocation `x ∈ A^m` and the next state.  Supporting prices of a
provisional allocation are always the buyer's own oracle `q_v(x)`. -/
structure FDAlg (A : Regime) (n m : ℕ) where
  /-- algorithm state -/
  State : Type
  /-- internal randomness -/
  Ω : Type
  /-- its distribution -/
  seed : RandomSource Ω
  /-- initial state (including all internal coin flips) -/
  init : Ω → State
  /-- process one buyer -/
  step : State → Fin n → Buyer m → AVec A m × State
  /-- primitive operations to draw the seed -/
  seedCost : ℕ
  /-- cost of one step -/
  stepCost : State → Fin n → Buyer m → Cost

/-- State after processing the buyers `π 0, …, π (t-1)` of the profile `v`. -/
def fdState {A : Regime} {n m : ℕ} (F : FDAlg A n m) (ω : F.Ω) (π : Equiv.Perm (Fin n))
    (v : Fin n → Buyer m) : ℕ → F.State
  | 0 => F.init ω
  | t + 1 => if h : t < n then (F.step (fdState F ω π v t) (π ⟨t, h⟩) (v (π ⟨t, h⟩))).2
             else fdState F ω π v t

/-- The state immediately before buyer `i` is processed, in processing order `π`. -/
def savedState {A : Regime} {n m : ℕ} (F : FDAlg A n m) (ω : F.Ω) (π : Equiv.Perm (Fin n))
    (v : Fin n → Buyer m) (i : Fin n) : F.State :=
  fdState F ω π v (π.symm i)

/-- The provisional allocations of `F` run on `v` in processing order `π`. -/
def fdRun {A : Regime} {n m : ℕ} (F : FDAlg A n m) (ω : F.Ω) (π : Equiv.Perm (Fin n))
    (v : Fin n → Buyer m) : Fin n → Vec m :=
  fun i => (F.step (savedState F ω π v i) i (v i)).1.1

/-- Cost of one run of `F` on `n` buyers in order `π` (drawing the order and the seed, plus
every step). -/
def fdRunCost {A : Regime} {n m : ℕ} (F : FDAlg A n m) (ω : F.Ω) (π : Equiv.Perm (Fin n))
    (v : Fin n → Buyer m) : Cost :=
  (n + F.seedCost, 0, 0) + ∑ i, F.stepCost (savedState F ω π v i) i (v i)

/-- Zero out every buyer whose coin is `false`. -/
def keepIf {n m : ℕ} (H : Fin n → Bool) (v : Fin n → Buyer m) : Fin n → Buyer m :=
  fun i => if H i then v i else Buyer.zero m

/-- `α`-competitiveness of a random-order free-disposal algorithm (§2.3) on the buyer class
`C`: buyers processed in a uniformly random order. -/
def FDAlg.FDCompetitive {A : Regime} {n m : ℕ} (F : FDAlg A n m) (C : Buyer m → Prop)
    (α : ℝ) : Prop :=
  α ∈ Set.Icc (0 : ℝ) 1 ∧
  ∀ v : Fin n → Buyer m, (∀ i, C (v i)) →
    ENNReal.ofReal α * ENNReal.ofReal (Opt A v) ≤
      pexp F.seed (fun ω => avg (fun π : Equiv.Perm (Fin n) =>
        ENNReal.ofReal (FD A v (fdRun F ω π v))))

/-- Definition 10 (smooth competitive ratio) for a random-order free-disposal algorithm on
the class `C`: `Γ : [0,1] → [0,1]` is (weakly) increasing, and for every profile `v` and
`q ∈ [0,1]`, independently keeping each buyer with probability `q` (zeroing it otherwise) and
running `F` on the modified profile `v'` in a uniformly random order gives expected free-disposal
value (evaluated on `v'`) at least `Γ(q) · Opt(v)`. -/
def FDAlg.Smooth {A : Regime} {n m : ℕ} (F : FDAlg A n m) (C : Buyer m → Prop)
    (Γ : ℝ → ℝ) : Prop :=
  MonotoneOn Γ (Set.Icc 0 1) ∧ (∀ q ∈ Set.Icc (0 : ℝ) 1, Γ q ∈ Set.Icc (0 : ℝ) 1) ∧
  ∀ v : Fin n → Buyer m, (∀ i, C (v i)) → ∀ q ∈ Set.Icc (0 : ℝ) 1,
    ENNReal.ofReal (Γ q) * ENNReal.ofReal (Opt A v) ≤
      pexp F.seed (fun ω => bernExp q (fun H => avg (fun π : Equiv.Perm (Fin n) =>
        ENNReal.ofReal (FD A (keepIf H v) (fdRun F ω π (keepIf H v))))))

/-! ## Buyer-local provisional allocation (Definitions 8–9) -/

/-- Definition 8: a buyer-local provisional-allocation algorithm, given by its local
implementation: after fixing the coordination sample `sᶜ` and the (shared) randomness `ω`,
buyer `i`'s provisional allocation `PAlloc_i(sᶜ, r_i) ∈ A^m` depends only on `r_i`.  Its
supporting prices are `r_i`'s own oracle `q_{r_i}(x_i)`. -/
structure PAlloc (A : Regime) (n m : ℕ) where
  /-- shared randomness -/
  Ω : Type
  /-- its distribution -/
  seed : RandomSource Ω
  /-- the local maps `PAlloc_i` -/
  loc : Ω → (Fin n → Buyer m) → Fin n → Buyer m → AVec A m

/-- Definition 9: `α`-competitiveness under the free-disposal value, for every family of
valuation pairs from the class `C`, each pair independently and uniformly ordered into
`(sᶜ_i, r_i)`. -/
def PAlloc.FDCompetitive {A : Regime} {n m : ℕ} (P : PAlloc A n m) (C : Buyer m → Prop)
    (α : ℝ) : Prop :=
  α ∈ Set.Icc (0 : ℝ) 1 ∧
  ∀ V : Fin n → Fin 2 → Buyer m, (∀ i t, C (V i t)) →
    ENNReal.ofReal α * avg (fun c : Fin n → Bool =>
        ENNReal.ofReal (Opt A (fun i => (gogPair (V i) (c i)).2))) ≤
      pexp P.seed (fun ω => avg (fun c : Fin n → Bool =>
        ENNReal.ofReal (FD A (fun i => (gogPair (V i) (c i)).2)
          (fun i => (P.loc ω (fun i' => (gogPair (V i') (c i')).1) i
            (gogPair (V i) (c i)).2).1))))

/-! ## Algorithm 1 (combinatorial to single-item reduction) -/

/-- The single-item type `(q_{b,j}(x), x_j)` that a provisional allocation `x` of a buyer `b`
induces on item `j`. -/
def itemOf {m : ℕ} (b : Buyer m) (x : Vec m) (j : Fin m) : Item := (b.q x j, x j)

/-- Algorithm 1 (PDF p. 14): every sample profile `s t` is transformed by `PAlloc` with the
same randomness `ω`; for each item `j` an independent `k`-SPI instance (seed `ωs j`) receives
these per-item samples and, online in the real arrival order `ρ`, the per-item real types of
the transformed real buyers, and returns `x'_{i,j}`. -/
def alg1 {A : Regime} {n m k : ℕ} (P : PAlloc A n m) (S : KSPI A n k) (ω : P.Ω)
    (ωs : Fin m → S.Ω) (ρ : Equiv.Perm (Fin n)) (sc : Fin n → Buyer m)
    (s : Fin k → Fin n → Buyer m) (r : Fin n → Buyer m) : Fin n → Vec m :=
  fun i j =>
    spiRun S (ωs j) (fun t i' => itemOf (s t i') (P.loc ω sc i' (s t i')).1 j) ρ
      (fun i' => itemOf (r i') (P.loc ω sc i' (r i')).1 j) i

/-- Slot of the coordination sample in the `(k+2)`-slot Game of Googol. -/
def slotC (k : ℕ) : Fin (k + 2) := 0

/-- Slot of sample `t`. -/
def slotS {k : ℕ} (t : Fin k) : Fin (k + 2) := t.succ.castSucc

/-- Slot of the real valuation. -/
def slotR (k : ℕ) : Fin (k + 2) := Fin.last (k + 1)

/-- Expected welfare of Algorithm 1 in the `(k+1)`-sample Game of Googol: per buyer, the
`k+2` adversarial valuations are uniformly permuted into the coordination sample, the `k`
samples and the real valuation; the expectation also covers `PAlloc`'s randomness and the
`m` independent `k`-SPI instances. -/
noncomputable def alg1Exp {A : Regime} {n m k : ℕ} (P : PAlloc A n m) (S : KSPI A n k)
    (ρ : Equiv.Perm (Fin n)) (V : Fin n → Fin (k + 2) → Buyer m) : ℝ≥0∞ :=
  pexp P.seed (fun ω => pexpPi S.seed (fun ωs =>
    avg (fun σ : Fin n → Equiv.Perm (Fin (k + 2)) => ENNReal.ofReal (∑ i, (V i (σ i (slotR k))).v
      (alg1 P S ω ωs ρ (fun i' => V i' (σ i' (slotC k)))
        (fun t i' => V i' (σ i' (slotS t))) (fun i' => V i' (σ i' (slotR k))) i)))))

/-- Expected hindsight optimum of the real profile in the `(k+1)`-sample Game of Googol. -/
noncomputable def optExpK {A : Regime} {n m k : ℕ} (V : Fin n → Fin (k + 2) → Buyer m) :
    ℝ≥0∞ :=
  avg (fun σ : Fin n → Equiv.Perm (Fin (k + 2)) =>
    ENNReal.ofReal (Opt A (fun i => V i (σ i (slotR k)))))

/-! ## Algorithm 2 (replay) -/

/-- Algorithm 2 (PDF p. 13): draw a uniform processing order `π` and `FDAlg`'s seed; run
`FDAlg` on the coordination sample in order `π`, saving the state just before each buyer;
`PAlloc_i(sᶜ, r_i)` is the provisional allocation of one call of `FDAlg` on `r_i` from the
saved state of buyer `i` (which does not update the saved run). -/
noncomputable def replay {A : Regime} {n m : ℕ} (F : FDAlg A n m) : PAlloc A n m where
  Ω := Equiv.Perm (Fin n) × F.Ω
  seed := (RandomSource.ofPMF (PMF.uniformOfFintype (Equiv.Perm (Fin n)))).prod F.seed
  loc := fun πω sc i b => (F.step (savedState F πω.2 πω.1 sc i) i b).1

/-! ## Algorithm 3 (single-sample split) -/

/-- Algorithm 3's role split: coordinating buyers (`H i = true`) give
`(sᶜ_i, s¹_i, r_i) = (s'_i, 0, 0)`, competing buyers give `(0, s'_i, r'_i)`. -/
def roleSc {n m : ℕ} (H : Fin n → Bool) (s' : Fin n → Buyer m) : Fin n → Buyer m :=
  fun i => if H i then s' i else Buyer.zero m

/-- The single competition sample `s¹`. -/
def roleS1 {n m : ℕ} (H : Fin n → Bool) (s' : Fin n → Buyer m) : Fin n → Buyer m :=
  fun i => if H i then Buyer.zero m else s' i

/-- The real profile passed to Algorithm 1. -/
def roleR {n m : ℕ} (H : Fin n → Bool) (r' : Fin n → Buyer m) : Fin n → Buyer m :=
  fun i => if H i then Buyer.zero m else r' i

/-- Algorithm 3 (PDF p. 16): Algorithm 1 with `k = 1`, the replay `PAlloc` of Algorithm 2 on
the coordination sample, and allocation `0` to coordinating buyers. -/
noncomputable def alg3 {A : Regime} {n m : ℕ} (F : FDAlg A n m) (S : KSPI A n 1) (H : Fin n → Bool)
    (π : Equiv.Perm (Fin n)) (ω : F.Ω) (ωs : Fin m → S.Ω) (ρ : Equiv.Perm (Fin n))
    (s' r' : Fin n → Buyer m) : Fin n → Vec m :=
  fun i => if H i then 0 else
    alg1 (replay F) S (π, ω) ωs ρ (roleSc H s') (fun _ => roleS1 H s') (roleR H r') i

/-- Algorithm 3, line 11: the provisional allocation `x_i = PAlloc_i(sᶜ, r_i)`. -/
def replayX {A : Regime} {n m : ℕ} (F : FDAlg A n m) (H : Fin n → Bool)
    (π : Equiv.Perm (Fin n)) (ω : F.Ω) (s' r' : Fin n → Buyer m) : Fin n → Vec m :=
  fun i => (F.step (savedState F ω π (roleSc H s') i) i (roleR H r' i)).1.1

/-- Algorithm 3, line 11: the sample-run allocation `z_i = PAlloc_i(sᶜ, sᶜ_i)`. -/
def replayZ {A : Regime} {n m : ℕ} (F : FDAlg A n m) (H : Fin n → Bool)
    (π : Equiv.Perm (Fin n)) (ω : F.Ω) (s' : Fin n → Buyer m) : Fin n → Vec m :=
  fdRun F ω π (roleSc H s')

/-- Expected welfare `E[∑_i r'_i(x'_i)]` of Algorithm 3 with role probability `q`, in the
single-sample Game of Googol on the adversarial pairs `V` and real arrival order `ρ`. -/
noncomputable def alg3Exp {A : Regime} {n m : ℕ} (F : FDAlg A n m) (S : KSPI A n 1) (q : ℝ)
    (ρ : Equiv.Perm (Fin n)) (V : Fin n → Fin 2 → Buyer m) : ℝ≥0∞ :=
  pexp F.seed (fun ω => pexpPi S.seed (fun ωs =>
    avg (fun c : Fin n → Bool => bernExp q (fun H => avg (fun π : Equiv.Perm (Fin n) =>
      ENNReal.ofReal (∑ i, (gogPair (V i) (c i)).2.v
        (alg3 F S H π ω ωs ρ (fun i' => (gogPair (V i') (c i')).1)
          (fun i' => (gogPair (V i') (c i')).2) i)))))))

/-- Expected hindsight optimum `E[Opt(r')]` of the real profile in the single-sample Game of
Googol. -/
noncomputable def optExp1 {A : Regime} {n m : ℕ} (V : Fin n → Fin 2 → Buyer m) : ℝ≥0∞ :=
  avg (fun c : Fin n → Bool => ENNReal.ofReal (Opt A (fun i => (gogPair (V i) (c i)).2)))

/-- Operation and query counts of one execution of Algorithm 3 (with Algorithms 1 and 2
inside): drawing and applying the role coins and the final zeroing (`3n`), drawing `π` (`n`),
the seeds, the sample run of `FDAlg` on `sᶜ`, the transformation of `s¹` (one `FDAlg` call, one
supporting-price query and `m` extractions per buyer), and per real buyer one `FDAlg` call,
one supporting-price query, `2m` extraction/aggregation steps and the `m` single-item
decisions. -/
noncomputable def alg3Cost {A : Regime} {n m : ℕ} (F : FDAlg A n m) (S : KSPI A n 1) (H : Fin n → Bool)
    (π : Equiv.Perm (Fin n)) (ω : F.Ω) (ωs : Fin m → S.Ω) (ρ : Equiv.Perm (Fin n))
    (s' r' : Fin n → Buyer m) : Cost :=
  let P := replay F
  let sc := roleSc H s'
  let s1 := roleS1 H s'
  let r := roleR H r'
  let samp : Fin m → Fin 1 → Fin n → Item :=
    fun j _ i' => itemOf (s1 i') (P.loc (π, ω) sc i' (s1 i')).1 j
  let real : Fin m → Fin n → Item :=
    fun j i' => itemOf (r i') (P.loc (π, ω) sc i' (r i')).1 j
  (4 * n + F.seedCost + m * S.seedCost, 0, 0)
    + ∑ i, F.stepCost (savedState F ω π sc i) i (sc i)
    + ∑ i, (F.stepCost (savedState F ω π sc i) i (s1 i) + (m, 0, 1))
    + ∑ i, (F.stepCost (savedState F ω π sc i) i (r i) + (2 * m, 0, 1)
        + (∑ j, S.actCost (ωs j) (samp j) (prefixOf ρ (real j) i) i (real j i), 0, 0))

end SingleSampleCombPI.XOS


