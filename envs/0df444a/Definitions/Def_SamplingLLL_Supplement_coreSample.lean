-- Prove2me | Definitions.Def_SamplingLLL_Supplement_coreSample
-- name    : SamplingLLL_Supplement_coreSample
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:54:01.432035+00:00
-- url     : https://prove2.me/theorems/6035c5ec-e98b-4034-97c9-32731657d812
-- title:
--   The sampler and FPRAS of the proof of Theorem F.6: block heat bath on the core and packet insertion
-- statement:
--   The explicit procedures of the proof of Theorem F.6, for a formula with a decomposition $(F,U)$, literal signs, and accuracy $\varepsilon$, run at $\varepsilon_0=\min\{\varepsilon,1/2\}$.
--
--   1. **Residual formula.** For a core assignment $\sigma$ (an assignment of $U$ satisfying all internal clauses, i.e. $\sigma\in\prod_B\Omega_B$), the residual formula keeps each clause of $C_{\mathrm{res}}$ and each cross clause whose core literal is false, restricted to its remaining variables.
--   2. **Residual calls (p.55).** For a requested error $\xi$: compute the cutoff $L=\max\{2,\lceil\log_2(64m'p/\min\{\xi,1/2\})\rceil\}$ of Theorem 5.4 for the residual formula with $m'$ clauses, $p=2^{-k+3}$; enumerate the connected clause families through $L$ and test $|\mathrm{vbl}(T)|\ge(k-3)|T|$ (56). If the test passes, run the deterministic counter, respectively the restarted sampler, of Theorem 5.4; otherwise enumerate all assignments.
--   3. **Core chain (p.56).** Starting from a core state, perform $T_{\mathrm{core}}=C_{\mathrm{core}}\,s_B\,N_0^{\beta}\,(n+\lceil\log_2\lceil1/\varepsilon_0\rceil\rceil)$ updates of the lazy block heat-bath chain: with probability $1/2$ hold; otherwise choose a block uniformly, enumerate $\Omega_B$, compute the residual count of each of its values with relative error $\eta=\varepsilon_0/(64T_{\mathrm{core}})$, and resample the block from the normalized counts.
--   4. **Sampler.** After the chain, run the residual sampler at total variation error $\varepsilon_0/4$ and output the core assignment on $U$ and the residual sample on $W$.
--   5. **Counting (pp.56–57).** The base count $2^{|W|}Z(C_{\mathrm{res}})\prod_B|\Omega_B|$ uses the residual counter at relative error $\varepsilon_0/8$ and exact block enumeration. Then the cross-clause packets $P_B$ are inserted one block at a time: with $s_0=\max\{1,s_B\}$, $\gamma=\varepsilon_0/(16s_0)$ and $\tilde q=2^{-\lceil4pa_{\mathrm{blk}}\rceil\lceil\log_2N_0\rceil}\le q_{\min}=N_0^{-4pa_{\mathrm{blk}}}$, each nonempty packet's survival probability is estimated by the fraction of survivors among $M=\lceil8(\gamma\tilde q)^{-2}\rceil\lceil\log_2(32s_0)\rceil$ samples of its prefix, each drawn by the sampler at accuracy $\tau=\gamma\tilde q/4$. The product of the base count and the packet estimates is the output, under a work cap $K\lceil(N_0+\ell(\varepsilon))/\varepsilon\rceil^{e}$.
--
--   The constant $C_{\mathrm{core}}$ of (67) and the cap polynomial $(K,e)$ are parameters; Theorem F.6 quantifies them.
--
--   **Formalization Note** Charges: the expansion test $m'(4d')^{2L}(n+m'+2)^2$ with $d'-1$ the maximum dependency degree of the residual formula; exhaustive enumeration $2^n(N+1)^2$; block enumeration $2^{|B|}N_0^2$; reading $\varepsilon$ and computing the derived integers $(\ell(\varepsilon)+N_0)^2$; all rational arithmetic by actual bit lengths. The initial core state takes the first element of each $\Omega_B$ in a fixed order (the paper allows any core state). The rational $\tilde q$ replaces the generally irrational $q_{\min}$; it is smaller, so the sample count is at least the printed one and the sampling accuracy at least as fine. The module's main declarations are `Core.coreSample` and `Core.coreCount`.
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), proof of Theorem F.6, pp.55–57; (67), p.56; proof of Theorem 2.19, p.48 (the cutoff)

import Mathlib
import Definitions.Def_SamplingLLL_Supplement_Core

set_option autoImplicit false

open scoped ENNReal

namespace SamplingLLL.Supplement

open Proc

/-! # The algorithms of the proof of Theorem F.6

Source: Achlioptas, *Counting and Sampling by Local Repair*, STOC 2027 submission (manuscript sha256
7a943167…), proof of Theorem F.6, pp.55–57.

Every procedure is built from the base charged primitives and from the procedures `frCount`, `frRestart` of
Theorem 5.4 (Appendix D). -/

section Residual

variable {n m' : ℕ} (J : AtomicCSP n m')

/-- The expansion test (56) through the cutoff `L` on a residual formula (p.55): every nonempty connected
family `T` of at most `L` clauses has `|vbl(T)| ≥ (k − 3)|T|`. -/
def expTest (k L : ℕ) : Prop :=
  ∀ T : Finset (Fin m'), T.card ≤ L → (J.H.induce (T : Set (Fin m'))).Connected →
    (k - 3) * T.card ≤ (T.biUnion J.vbl).card

/-- The charge of the expansion test, `m (4d)^{2L} (n + m + 2)²` with `d − 1` the maximum dependency degree
of the formula (p.55: "The test itself costs `m(4d)^{O(L)}`"). -/
def testCost (L : ℕ) : ℕ :=
  m' * (4 * ((Finset.univ.sup fun a => (J.H.neighborFinset a).card) + 1)) ^ (2 * L) * (n + m' + 2) ^ 2

/-- A residual counting call with requested relative error `ξ` (the rule of p.55): compute the cutoff `L`
requested by Theorem 5.4 (the cutoff of p.48 for the formula at hand), enumerate the connected clause
families through `L` and test (56); if the test passes run the deterministic counter of Theorem 5.4 at
`p = 2^{−k+3}`, otherwise enumerate all assignments. The output estimates the acceptance probability `Z` of
the formula under the uniform assignment. It draws no random bits. -/
noncomputable def resCount (k : ℕ) (ξ : ℚ) : Proc ℚ := by
  classical
  exact do
    let L ← cutoffP m' k ξ
    tick (testCost J L)
    if expTest J k L then frCount J (p0k k) L
    else do
      tick (enumCost J)
      pure (J.toCSP.Z Finset.univ)

/-- A residual sampling call with requested total variation error `ξ` (the rule of p.55): the same cutoff
and test; if the test passes run the restarted sampler of Theorem 5.4, otherwise enumerate all assignments
and draw a satisfying one uniformly. -/
noncomputable def resSample (k : ℕ) (ξ : ℚ) : Proc J.toCSP.Config := by
  classical
  exact do
    let L ← cutoffP m' k ξ
    tick (testCost J L)
    if expTest J k L then frRestart J (p0k k) L
    else do
      tick (enumCost J)
      let sols := (Finset.univ.filter fun x => J.toCSP.sat Finset.univ x = true).toList
      drawList (sols.map fun x => (x, (1 / sols.length : ℚ))) (fun _ => 0) 1

end Residual

namespace Core

variable {n m : ℕ} (F : Core n m) (sgn : Fin m → Fin n → Bool)

/-- The clause `c` is violated by the Boolean assignment `x`: every variable of its scope takes the
falsifying value `sgn c v` (the convention of `kcnf`). -/
def viol (c : Fin m) (x : Fin n → Bool) : Prop := ∀ v ∈ F.scope c, x v = sgn c v

instance (c : Fin m) (x : Fin n → Bool) : Decidable (F.viol sgn c x) := by unfold viol; infer_instance

/-- The residual clauses that survive the core assignment `σ` among the present clauses `S` (F.3, p.50), in
index order: the clauses of `S` not internal to `U` whose variables in `U` all take their falsifying value.
A clause of `C_res` has no variable in `U` and always survives; a cross clause survives exactly when its
core literal is false. -/
def surv (S : Finset (Fin m)) (σ : Fin n → Bool) : List (Fin m) :=
  (List.finRange m).filter fun c =>
    decide (c ∈ S ∧ ¬ F.scope c ⊆ F.U ∧ ∀ u ∈ F.scope c ∩ F.U, σ u = sgn c u)

/-- The residual formula `Ψ` for the core assignment `σ` and the present clauses `S`: each surviving clause
restricted to its remaining variables, with its signs. The variables of `U` are unconstrained in it. -/
noncomputable def resCSP (S : Finset (Fin m)) (σ : Fin n → Bool) :
    AtomicCSP n (F.surv sgn S σ).length :=
  kcnf (fun j => F.res ((F.surv sgn S σ).get j)) (fun j => sgn ((F.surv sgn S σ).get j))

/-- `Ω_B` (p.49): the assignments of the block `B` satisfying all clauses internal to `B`, each given by
its set of true variables, listed in a fixed order. -/
noncomputable def omega (B : Finset (Fin n)) : List (Finset (Fin n)) := by
  classical
  exact (B.powerset.filter fun Tr =>
    ∀ c, F.scope c ⊆ B → ¬ F.viol sgn c (fun v => decide (v ∈ Tr))).toList

/-- Overwrite the block `B` of the core assignment `σ` by the assignment with true set `Tr`. -/
def setB (_F : Core n m) (σ : Fin n → Bool) (B Tr : Finset (Fin n)) : Fin n → Bool :=
  fun v => if v ∈ B then decide (v ∈ Tr) else σ v

/-- The blocks in a fixed order. -/
noncomputable def blockList : List (Finset (Fin n)) := F.blocks.toList

/-- The residual counts of the values of `Ω_B`, each by the residual counter at relative error `η`
(p.56: "enumerate `Ω_B` and compute the residual count for each of its values using the residual FPTAS").
Writing down the residual formula of a value (one scan of the clauses) is charged `N₀²`. -/
noncomputable def weights (k : ℕ) (S : Finset (Fin m)) (η : ℚ) (σ : Fin n → Bool)
    (B : Finset (Fin n)) : List (Finset (Fin n)) → Proc (List (Finset (Fin n) × ℚ))
  | [] => pure []
  | Tr :: l => do
    tick (F.N0 ^ 2)
    let w ← resCount (F.resCSP sgn S (F.setB σ B Tr)) k η
    let r ← weights k S η σ B l
    pure ((Tr, w) :: r)

/-- One update of the lazy block heat-bath chain on the core (p.56): with probability `1/2` hold; otherwise
choose a block uniformly at random, enumerate `Ω_B` (charged `2^{|B|} N₀²`), compute the residual count of
each of its values at relative error `η`, and resample the block from the normalized counts. -/
noncomputable def hbUpdate (k : ℕ) (S : Finset (Fin m)) (η : ℚ) (σ : Fin n → Bool) :
    Proc (Fin n → Bool) := do
  let hold ← flip
  if hold then pure σ else
    match F.blockList with
    | [] => pure σ
    | B0 :: bl => do
      let j ← uniformFin bl.length
      let B := (B0 :: bl).get j
      tick (2 ^ B.card * F.N0 ^ 2)
      let ws ← F.weights sgn k S η σ B (F.omega sgn B)
      let tot ← ws.foldlM (fun acc x => qadd acc x.2) 0
      let ps ← ws.mapM fun x => do
        let q ← qdiv x.2 tot
        pure (x.1, q)
      let Tr ← drawList ps (B.filter fun v => σ v = true) 1
      pure (F.setB σ B Tr)

/-- `t` successive updates. -/
noncomputable def hbRun (k : ℕ) (S : Finset (Fin m)) (η : ℚ) : ℕ → (Fin n → Bool) → Proc (Fin n → Bool)
  | 0, σ => pure σ
  | t + 1, σ => do
    let σ' ← F.hbUpdate sgn k S η σ
    hbRun k S η t σ'

/-- The number of updates `T_core = C_core s_B N₀^β (n + ⌈log₂⌈1/ε⌉⌉)` of (67), p.56; the constant of the
`O(·)` in (67) is the parameter `C_core`. -/
noncomputable def Tcore (Ccore β : ℕ) (ε : ℚ) : ℕ :=
  Ccore * F.blocks.card * F.N0 ^ β * (n + Nat.clog 2 ⌈(1 / ε : ℚ)⌉₊)

/-- The initial core state: on each block the first assignment of `Ω_B` (any core state may be used,
p.56). -/
noncomputable def sigma0 : Fin n → Bool := by
  classical
  exact fun v => decide (v ∈ F.U ∧ v ∈ (F.omega sgn (F.blockOf v)).headD ∅)

/-- The sampler of the proof of Theorem F.6 (pp.55–56) for the formula restricted to the present clauses
`S` (`S = Finset.univ` for the formula itself; a prefix in the counting algorithm), at accuracy `ε`, run at
`ε₀ = min{ε, 1/2}`: `T_core` updates of the lazy block heat-bath chain on the core with residual counts at
relative error `η = ε₀/(64 T_core)`, then the residual sampler at total variation error `ε₀/4` on the
remaining variables. Reading `ε` and computing `T_core` and `η` is charged `(bits ε + N₀)²`; the initial
state (the first element of each `Ω_B`, by enumeration) is charged `2^{|B|} N₀²` per block; writing down the
final residual formula is charged `N₀²`. -/
noncomputable def coreSample (k β Ccore : ℕ) (S : Finset (Fin m)) (ε : ℚ) :
    Proc (kcnf F.scope sgn).toCSP.Config := do
  tick ((bits ε + F.N0) ^ 2)
  let ε₀ : ℚ := min ε (1 / 2)
  let Tc := F.Tcore Ccore β ε₀
  tick (∑ B ∈ F.blocks, 2 ^ B.card * F.N0 ^ 2)
  let σ ← F.hbRun sgn k S (ε₀ / (64 * Tc)) Tc (F.sigma0 sgn)
  tick (F.N0 ^ 2)
  let x ← resSample (F.resCSP sgn S σ) k (ε₀ / 4)
  pure fun v => if v ∈ F.U then (if σ v then 1 else 0) else if (x v : ℕ) = 1 then 1 else 0

/-- The rational `q̃ = 2^{−⌈4 p a_blk⌉ ⌈log₂ N₀⌉} ≤ N₀^{−4 p a_blk} = q_min` (p.56), `p = 2^{−k+3}`. -/
noncomputable def qtil (k : ℕ) (ablk : ℝ) : ℚ :=
  (1 / 2 : ℚ) ^ (⌈4 * (8 / 2 ^ k : ℝ) * ablk⌉₊ * Nat.clog 2 F.N0)

/-- The number of survivors of the packet `P_B` among `t` independent samples of the prefix `S` at total
variation error `τ`, added to `acc`; evaluating the packet on a sample is charged `N₀²`. -/
noncomputable def survivors (k β Ccore : ℕ) (S : Finset (Fin m)) (B : Finset (Fin n)) (τ : ℚ) :
    ℕ → ℕ → Proc ℕ
  | 0, acc => pure acc
  | t + 1, acc => do
    let x ← F.coreSample sgn k β Ccore S τ
    tick (F.N0 ^ 2)
    survivors k β Ccore S B τ t
      (if ∀ c ∈ F.crossOf B, ¬ F.viol sgn c (fun v => decide ((x v : ℕ) = 1)) then acc + 1 else acc)

/-- Insert the cross-clause packets one block at a time (p.56): for each nonempty packet, estimate its
survival probability by the fraction of survivors among `M` samples of its prefix, each within `τ` of the
uniform solution law of the prefix, and multiply the estimate into `acc`. -/
noncomputable def packets (k β Ccore : ℕ) (τ : ℚ) (M : ℕ) :
    List (Finset (Fin n)) → Finset (Fin m) → ℚ → Proc ℚ
  | [], _, acc => pure acc
  | B :: l, S, acc =>
    if F.crossOf B = ∅ then packets k β Ccore τ M l S acc else do
      let c ← F.survivors sgn k β Ccore S B τ M 0
      let q ← qdiv (c : ℚ) (M : ℚ)
      let acc' ← qmul acc q
      packets k β Ccore τ M l (S ∪ F.crossOf B) acc'

/-- The counting algorithm of the proof of Theorem F.6 (pp.56–57), before the cap, at accuracy
`ε₀ = min{ε, 1/2}`. The base count `2^{|W|} Z(C_res) ∏_B |Ω_B|` of the internal clauses and `C_res` uses the
residual counter at relative error `ε₀/8` (writing down `C_res` is charged `N₀²`) and exact block
enumeration (charged `2^{|B|} N₀²` per block). Then
the packets are inserted with `s₀ = max{1, s_B}`, `γ = ε₀/(16 s₀)`, `τ = γ q̃/4` and
`M = ⌈8 (γ q̃)^{-2}⌉ ⌈log₂(32 s₀)⌉` samples. The output estimates the number of satisfying assignments. -/
noncomputable def countCore (k : ℕ) (ablk : ℝ) (β Ccore : ℕ) (ε : ℚ) : Proc ℚ := by
  classical
  exact do
    tick ((bits ε + F.N0) ^ 2)
    let ε₀ : ℚ := min ε (1 / 2)
    let s₀ : ℕ := max 1 F.blocks.card
    let γ : ℚ := ε₀ / (16 * s₀)
    tick (F.N0 ^ 2)
    let zres ← resCount
      (F.resCSP sgn (Finset.univ.filter fun c => Disjoint (F.scope c) F.U) fun _ => false) k (ε₀ / 8)
    tick (∑ B ∈ F.blocks, 2 ^ B.card * F.N0 ^ 2)
    let base ← qmul zres ((2 : ℚ) ^ (n - F.U.card) * ∏ B ∈ F.blocks, ((F.omega sgn B).length : ℚ))
    F.packets sgn k β Ccore (γ * F.qtil k ablk / 4)
      (⌈(8 / (γ * F.qtil k ablk) ^ 2 : ℚ)⌉₊ * Nat.clog 2 (32 * s₀))
      F.blockList (Finset.univ.filter fun c => ¬ F.cross c) base

/-- The FPRAS of Theorem F.6: the counting algorithm under the work cap
`K ⌈(N₀ + bits ε)/ε⌉^e` (p.57: "Cap the aggregate running time at sixteen times the proved polynomial upper
bound on its expectation"); `K` and `e` are the parameters of that polynomial. -/
noncomputable def coreCount (k : ℕ) (ablk : ℝ) (β Ccore K e : ℕ) (ε : ℚ) : Proc ℚ :=
  capped (K * ⌈(((F.N0 : ℚ) + bits ε) / ε : ℚ)⌉₊ ^ e) 0 (F.countCore sgn k ablk β Ccore ε)

end Core

end SamplingLLL.Supplement


