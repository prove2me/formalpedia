-- Prove2me | Definitions.Def_ExactParallelSampling_QuasiUniform_IndepSystems
-- name    : ExactParallelSampling_QuasiUniform_IndepSystems
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T20:50:58.066875+00:00
-- url     : https://prove2.me/theorems/c170a928-1234-4f3a-9f29-aceec6d5daae
-- title:
--   Random orders, shortest dependent prefixes, φ, essential probability, α-values, GreedyOpt and Certify
-- statement:
--   The objects of §6 (pp. 28–35) for a family $I$ of subsets of a finite ground set $E$; $n=|E|$ and logarithms are base 2. `uprob Ω P` is the probability of $P$ under the uniform distribution on a finite set (\#favourable / \#all).
--
--   - **Orders and prefixes.** An order of $M$ is a bijection from positions $0,\dots,|M|-1$ to $M$. `prefixOf σ t` is its first $t$ elements; `sdp I σ` $=P_\sigma$ is the shortest dependent prefix; `lip I σ` $=Q_\sigma$ is the longest independent prefix.
--   - **Probabilities.** `phi I M S` $=\varphi^M_S=\Pr_\pi[P_\pi\cap S\notin I]$; `essProb I S x` $=p_x(S)=\Pr_\sigma[x\in P_\sigma,\ P_\sigma-x\in I]$; `fS I S ℓ` $=f_S(\ell)$, the probability that a uniform $\ell$-subset of $S$ is independent; `alphaVal I S` $=\alpha(S)=\min\{\ell:f_S(\ell)\le1/2\}$.
--   - **Parameters.** $c_\gamma=48/\gamma$, $\delta=n^{-1-\gamma}$, $\varepsilon=\delta/(2n)$, $N=\lceil1280n^{4+\gamma}\rceil$, $\theta_s=1-\delta/2+s\varepsilon$.
--   - **Algorithm 2, GreedyOpt$(M)$ (p. 32).** Given $N$ orders $\pi_i$ of $M$: $D_i$ is the family of all circuits contained in $P_{\pi_i}$, as $\mathrm{Rec}$ returns it. Then $\hat\varphi_S=\frac1N|\{i:\exists D\in D_i,\ D\subseteq S\}|$. Starting from $S=M$, the first $x\in S$ (in the order of $E$) with $\hat\varphi_{S-x}\ge\theta_{|S|-1}$ is removed, until none remains. Its first round asks all $N|M|$ prefixes (`greedyOptQueries`).
--   - **Algorithm 4, Certify$(S)$ (p. 35).** $m_S=\lceil(1-1/\log n)|S|\rceil$, $N_c=\lceil4n^{3+\gamma}\ln(2^{24}n)\rceil$ (natural log), $R_c=\lceil2^{24}n\rceil$. The random choices `CertRand` are a uniform $m_S$-subset $S'\subseteq S$ and $N_c$ uniform orders of $S'$. `certifyR` returns $R=\{x\in S\setminus S': Q_\sigma+x\notin I\text{ for some }\sigma\}$, and `certifyCert` gives $T_x=Q_\sigma$ for the first such $\sigma$.
--
--   `greedyProtocol` is the transcript implementation of Algorithm 2 after the uniform orders are drawn. It asks all nonempty prefixes in its first batch, constructs the recovery batch only from their answers, and computes the removal loop with `greedyFromFamilies` from the returned circuit families. It has no direct access to I. Duplicate queries are shared.
-- source:
--   Shen, Li, Shi and Li (2026), Exact Parallel Sampling without Maximal Independent Sets, supplied PDF, §6.1, Algorithms 2 and 4, §6.3, §6.5, p. 28–35; SHA256 34a681c96bb71642376464cc79acf05535f33206b14e5949999f5f31c28082d4

import Mathlib
import Definitions.Def_ExactParallelSampling_QuasiUniform_Distributions
import Definitions.Def_ExactParallelSampling_QuasiUniform_Protocol

noncomputable section
open Classical

namespace ExactParallelSampling.QuasiUniform

/-! # Random orders, shortest dependent prefixes, α-values, GreedyOpt and Certify (§6, pp. 28–35)

`I : Finset E → Prop` is a family of subsets of a finite ground set `E` (an independence system
where so assumed). All probabilities are over uniformly random finite objects and are computed
exactly as `#favourable / #all` (`uprob`). Logarithms are base 2 except `ln` in `N_c`. -/

/-- The probability of `P` under the uniform distribution on a finite type. -/
def uprob (Ω : Type*) [Fintype Ω] (P : Ω → Prop) : ℝ :=
  ((Finset.univ.filter P).card : ℝ) / (Fintype.card Ω : ℝ)

variable {E : Type*} [Fintype E]

/-- A linear order of `M`, listed as a bijection from positions `0, …, |M| − 1`. -/
abbrev Order (M : Finset E) := Fin M.card ≃ ↥M

/-- The prefix `σ[1..t]` (its first `t` elements). -/
def prefixOf {M : Finset E} (σ : Order M) (t : ℕ) : Finset E :=
  (Finset.univ.filter (fun i : Fin M.card => (i : ℕ) < t)).image (fun i => (σ i : E))

/-- Length of the shortest dependent prefix (`|M|` if no prefix is dependent; for dependent `M`
the whole order is a dependent prefix). -/
def sdpLen (I : Finset E → Prop) {M : Finset E} (σ : Order M) : ℕ :=
  if h : ∃ t, ¬ I (prefixOf σ t) then Nat.find h else M.card

/-- The shortest dependent prefix `P_σ`. -/
def sdp (I : Finset E → Prop) {M : Finset E} (σ : Order M) : Finset E :=
  prefixOf σ (sdpLen I σ)

/-- The longest independent prefix `Q_σ` (Algorithm 4). -/
def lip (I : Finset E → Prop) {M : Finset E} (σ : Order M) : Finset E :=
  prefixOf σ (Nat.findGreatest (fun t => I (prefixOf σ t)) M.card)

/-- Circuit-containment probability `φ^M_S = Pr_π[P_π ∩ S ∉ I]`, `π` uniform order of `M`. -/
def phi (I : Finset E → Prop) (M S : Finset E) : ℝ :=
  uprob (Order M) (fun π => ¬ I (sdp I π ∩ S))

/-- Essential probability `p_x(S) = Pr_σ[x ∈ P_σ and P_σ − x ∈ I]`, `σ` uniform order of `S`. -/
def essProb (I : Finset E → Prop) (S : Finset E) (x : E) : ℝ :=
  uprob (Order S) (fun σ => x ∈ sdp I σ ∧ I ((sdp I σ).erase x))

/-- `f_S(ℓ)`: the probability that a uniformly random `ℓ`-subset of `S` is independent. -/
def fS (I : Finset E → Prop) (S : Finset E) (ℓ : ℕ) : ℝ :=
  uprob {T // T ∈ S.powersetCard ℓ} (fun T => I T.1)

/-- The α-value `α(S) = min{ℓ : f_S(ℓ) ≤ 1/2}` (used for dependent `S`, where `f_S(|S|) = 0`). -/
def alphaVal (I : Finset E → Prop) (S : Finset E) : ℕ :=
  if h : ∃ ℓ, fS I S ℓ ≤ 1 / 2 then Nat.find h else 0

/-! ## The parameters of §6 (p. 28, p. 32, p. 35) -/

/-- `c_γ = 48/γ`. -/
def cgam (γ : ℝ) : ℝ := 48 / γ

/-- `δ = n^{−1−γ}`. -/
def deltaP (n : ℕ) (γ : ℝ) : ℝ := (n : ℝ) ^ (-1 - γ)

/-- `ε = δ/(2n)`. -/
def epsP (n : ℕ) (γ : ℝ) : ℝ := deltaP n γ / (2 * n)

/-- `N = ⌈1280 n³/δ⌉ = ⌈1280 n^{4+γ}⌉`. -/
def Nord (n : ℕ) (γ : ℝ) : ℕ := ⌈1280 * (n : ℝ) ^ (4 + γ)⌉₊

/-- `θ_s = 1 − δ/2 + s ε`. -/
def theta (n : ℕ) (γ : ℝ) (t : ℕ) : ℝ := 1 - deltaP n γ / 2 + t * epsP n γ

/-! ## Algorithm 2: GreedyOpt(M) (p. 32)

Lines 1–3: `N` independent uniform orders `π_i` of `M`; one round queries every prefix (this finds
`P_i`), then `Rec` is run on `(P_i − x_i, x_i)` for all `i` in parallel and returns `D_i`, the family
of all circuits contained in `P_i`. Lines 4–8 are offline. "The first such `x`" is the first in the
linear order of `E`. -/

variable [LinearOrder E]

/-- `φ̂_S = (1/N) |{i : some D ∈ D_i satisfies D ⊆ S}|`. -/
def phiHat (I : Finset E → Prop) {M : Finset E} {N : ℕ} (π : Fin N → Order M) (S : Finset E) :
    ℝ :=
  ((Finset.univ.filter (fun i => ∃ D ∈ circuitsIn I (sdp I (π i)), D ⊆ S)).card : ℝ) / N

/-- One pass of the while loop: remove the first `x ∈ S` with `φ̂_{S−x} ≥ θ_{|S|−1}`, if any. -/
def greedyStep (I : Finset E → Prop) (n : ℕ) (γ : ℝ) {M : Finset E} {N : ℕ}
    (π : Fin N → Order M) (S : Finset E) : Finset E :=
  let cand := S.filter (fun x => theta n γ (S.card - 1) ≤ phiHat I π (S.erase x))
  if h : cand.Nonempty then S.erase (cand.min' h) else S

/-- `GreedyOpt(M)` on the orders `π` (with `N = Nord n γ` of them): start from `S = M` and run the
loop until no element can be removed (at most `|M|` removals). -/
def greedyOpt (I : Finset E → Prop) (n : ℕ) (γ : ℝ) {M : Finset E}
    (π : Fin (Nord n γ) → Order M) : Finset E :=
  (greedyStep I n γ π)^[M.card + 1] M

/-- The number of independence queries of the first round of GreedyOpt: every prefix
`π_i[1..t]`, `i ≤ N`, `t ≤ |M|`. -/
def greedyOptQueries (n : ℕ) (γ : ℝ) (M : Finset E) : ℕ := Nord n γ * M.card

/-! ### The oracle execution of Algorithm 2

The supplied orders are the random choices in line 1. The following protocol has no access to
`I`: its second batch uses only the first batch's answers, and its output uses the returned
circuit families. Repeated identical queries are shared. -/

/-- Lines 4–8, computed offline from the recovered families. -/
def greedyFromFamilies (n : ℕ) (γ : ℝ) (M : Finset E) {N : ℕ}
    (D : Fin N → Finset (Finset E)) : Finset E :=
  let ph : Finset E → ℝ := fun S =>
    ((Finset.univ.filter (fun i => ∃ C ∈ D i, C ⊆ S)).card : ℝ) / N
  let step : Finset E → Finset E := fun S =>
    let cand := S.filter (fun x => theta n γ (S.card - 1) ≤ ph (S.erase x))
    if h : cand.Nonempty then S.erase (cand.min' h) else S
  step^[M.card + 1] M

/-- The first batch: every nonempty prefix of every sampled order. -/
def greedyPrefixBatch {E : Type} [Fintype E] [LinearOrder E] {M : Finset E} {N : ℕ} (π : Fin N → Order M) : Finset (IQuery E) :=
  (Finset.univ : Finset (Fin N × Fin M.card)).image
    (fun it => IQuery.indep (prefixOf (π it.1) (it.2.val + 1)))

/-- Recover the shortest dependent prefix using only its queried independence answers;
the harmless `indep ∅` fallback is used only for malformed answers or independent `M`. -/
def greedyRecoveryQuery {E : Type} [Fintype E] [LinearOrder E] (known : Finset E → Prop) {M : Finset E} (σ : Order M) : IQuery E :=
  let dep := (Finset.Icc 1 M.card).filter (fun t => ¬ known (prefixOf σ t))
  if hd : dep.Nonempty then
    let t := dep.min' hd
    if ht : t - 1 < M.card then
      let x : E := σ ⟨t - 1, ht⟩
      .recover ((prefixOf σ t).erase x) x
    else .indep ∅
  else .indep ∅

/-- Independence information from the first batch. -/
def greedyKnown {E : Type} [Fintype E] [LinearOrder E] (h : Transcript (IQuery E) (IAnswer E)) (T : Finset E) : Prop :=
  transcriptAnswer h 0 (.indep T) = some (.bool true)

/-- The second batch: one recovery instance for each sampled order, duplicates shared. -/
def greedyRecoveryBatch {E : Type} [Fintype E] [LinearOrder E] {M : Finset E} {N : ℕ} (π : Fin N → Order M)
    (h : Transcript (IQuery E) (IAnswer E)) : Finset (IQuery E) :=
  Finset.univ.image (fun i => greedyRecoveryQuery (greedyKnown h) (π i))

/-- Read the family returned for an order from the second batch. -/
def greedyReturnedFamily {E : Type} [Fintype E] [LinearOrder E] {M : Finset E} (σ : Order M)
    (h : Transcript (IQuery E) (IAnswer E)) : Finset (Finset E) :=
  match transcriptAnswer h 1 (greedyRecoveryQuery (greedyKnown h) σ) with
  | some (.family D) => D
  | _ => ∅

/-- Algorithm 2 after its random orders have been drawn: one independence batch, one parallel
recovery phase costing `ρ` rounds, then offline computation and halt. -/
def greedyProtocol {E : Type} [Fintype E] [LinearOrder E] (n : ℕ) (γ : ℝ) {M : Finset E} (π : Fin (Nord n γ) → Order M) :
    Protocol (IQuery E) (IAnswer E) (Finset E) where
  next h _ :=
    if h.length = 0 then .ask (greedyPrefixBatch π)
    else if h.length = 1 then .ask (greedyRecoveryBatch π h)
    else .halt (greedyFromFamilies n γ M (fun i => greedyReturnedFamily (π i) h))
  measurable_next h a := by
    let act : Action (IQuery E) (Finset E) :=
      if h.length = 0 then .ask (greedyPrefixBatch π)
      else if h.length = 1 then .ask (greedyRecoveryBatch π h)
      else .halt (greedyFromFamilies n γ M (fun i => greedyReturnedFamily (π i) h))
    change MeasurableSet {ω : Tape | act = a}
    by_cases ha : act = a <;> simp [ha]

/-! ## Algorithm 4: Certify(S) (p. 35) -/

/-- `m_S = ⌈(1 − 1/log n)|S|⌉`. -/
def mS (n : ℕ) (S : Finset E) : ℕ := ⌈(1 - 1 / Real.logb 2 n) * S.card⌉₊

/-- `N_c = ⌈4 n^{3+γ} ln(2^{24} n)⌉` (natural logarithm). -/
def Ncert (n : ℕ) (γ : ℝ) : ℕ := ⌈4 * (n : ℝ) ^ (3 + γ) * Real.log (2 ^ 24 * n)⌉₊

/-- `R_c = ⌈2^{24} n⌉`. -/
def Rcert (n : ℕ) : ℕ := ⌈(2 : ℝ) ^ 24 * n⌉₊

/-- The random choices of one run of Certify(S): a uniformly random `m_S`-subset `S'` of `S` and
`N_c` independent uniformly random orders of `S'`. The uniform distribution on this type is
exactly that law, because every `S'` has the same number of order tuples. -/
abbrev CertRand (n : ℕ) (γ : ℝ) (S : Finset E) :=
  Σ S' : {T // T ∈ S.powersetCard (mS n S)}, (Fin (Ncert n γ) → Order S'.1)

/-- The set returned by Certify(S): `R = {x ∈ S ∖ S' : Q_σ + x ∉ I for some σ}`. -/
def certifyR (I : Finset E → Prop) {n : ℕ} {γ : ℝ} {S : Finset E} (c : CertRand n γ S) :
    Finset E :=
  (S \ c.1.1).filter (fun x => ∃ i, ¬ I (insert x (lip I (c.2 i))))

/-- The certificate `T_x = Q_σ` of a returned `x`, for the first such order `σ`. -/
def certifyCert (I : Finset E → Prop) {n : ℕ} {γ : ℝ} {S : Finset E} (c : CertRand n γ S)
    (x : E) : Finset E :=
  let wit := Finset.univ.filter (fun i : Fin (Ncert n γ) => ¬ I (insert x (lip I (c.2 i))))
  if h : wit.Nonempty then lip I (c.2 (wit.min' h)) else ∅

end ExactParallelSampling.QuasiUniform


