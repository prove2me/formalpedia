-- Prove2me | Definitions.Def_DeepQOperator_Sampling
-- name    : DeepQOperator_Sampling
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:05:56.14286+00:00
-- url     : https://prove2.me/theorems/7c1ad5de-4653-4329-86fc-db86c43f5595
-- title:
--   The parameters (8), the sampling estimators (44), and the two raw protocols of (9)
-- statement:
--   1. **Parameters (8).** $\delta=\min\{1/2,16\varepsilon/\gamma\}$, $R=2\lceil\log_2(m/\delta)\rceil+1$, $v=\max\{1,\lceil\log_2(8\gamma/\varepsilon)\rceil\}$, and $s=1024$.
--   2. **Estimators.** With sampled addresses $V_{t,k}$ ($t\le R$, $k\le s$): $U_{t,i}=(2s)^{-1}\sum_kc_i(V_{t,k})a_{V_{t,k}}$, $\widetilde U_{t,i}=(2s)^{-1}\sum_kc_i(V_{t,k})Q_5(a_{V_{t,k}})$ (44), and $\widetilde b_i=\mathrm{median}_t\,\widetilde U_{t,i}$, the $\frac{R+1}2$-th order statistic.
--   3. **The sampling protocol (E.2–E.3).** Stage one reads the raw row-C site $a_{V_{t,k}}$ for all $sR$ draws with five bits each. From these symbols it forms $J=\{i:\widetilde b_i\ge1/8\}$. If $|J|>64$ it stops and returns action $-$. Otherwise it reads $b_i$ and $z_i$ for each $i\in J$ (in increasing order) with $v$ bits each, computes $\widetilde A=\max\{1/4,\max_{i\in J}(\widetilde\beta_i+\widetilde z_i/16)\}$, $\widetilde B=\max\{1/4,\max_{i\in J}\widetilde\beta_i\}$ from the reconstructions $\widetilde\beta_i=Q_v(b_i)$, $\widetilde z_i=Q_v(z_i)$, and chooses $+$ iff $\gamma(\widetilde A-\widetilde B-1/32)\ge0$. Its seed is the list of draws, uniformly distributed.
--   4. **The direct protocol (E.4).** A fixed raw protocol that reads all $m$ baseline scores $b_i$ and all $m$ payloads $z_i$ with $v$ bits each and applies the same rule with $J=\{0,\dots,m-1\}$.
--
--   These are the two protocols whose better budget gives (9).
--
--   **Formalization Note** $R$ and $v$ are natural numbers computed with the natural-number ceiling of `Real.logb 2`; the `max` with $1$ makes $v$ agree with the paper when the logarithm is negative. Stage-one field $j$ reads draw $(\lfloor j/1024\rfloor, j\bmod1024)$; stage-two fields $sR+2p$ and $sR+2p+1$ read $b_i$ and $z_i$ for the $p$-th element $i$ of $J$. The direct protocol's seed space is a one-point space.
-- source:
--   Qi, Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions, STOC 2027 submission (manuscript sha256 9f8f3285…), Theorem 2 eq. (8) p.4, Appendix E.2–E.4 pp.23–25 (PDF pp.7, 26–28)

import Mathlib
import Definitions.Def_DeepQOperator_Family
import Definitions.Def_DeepQOperator_Quantizer
import Definitions.Def_DeepQOperator_ReplyProtocol

open MeasureTheory

namespace DeepQOperator

/-!
# The parameters (8), the sampling estimators (44)–(45), and the two raw protocols of (9)

Q. Qi, *Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions*,
STOC 2027 submission (manuscript sha256 9f8f3285…), Theorem 2 eq. (8) p.4 (PDF p.7),
Appendix E.2–E.4 pp.23–25 (PDF pp.26–28).

* (8): `δ = min{1/2, 16ε/γ}`, `R = 2⌈log₂(m/δ)⌉ + 1`, `v = max{1, ⌈log₂(8γ/ε)⌉}`.
* E.2: `s = 1024`; for each repetition `t ≤ R` and sample `k ≤ s` a uniform address `V_{t,k}`. The
  unquantized average `U_{t,i} = (2s)^{-1} Σ_k c_i(V_{t,k}) a_{V_{t,k}}`, the quantized average
  `Ũ_{t,i} = (2s)^{-1} Σ_k c_i(V_{t,k}) Q_5(a_{V_{t,k}})` (44), and `b̃_i = median_t Ũ_{t,i}`.
* E.3: `J = {i : b̃_i ≥ 1/8}`; if `|J| > 64` stop and return a fixed action; otherwise request the raw
  row-B scalar `b_i` and the raw row-C scalar `z_i` for each `i ∈ J` with `j_v`, and choose `+` iff
  `g̃ = γ(Ã - B̃ - 1/32) ≥ 0`, where `Ã = max{1/4, max_{i∈J}(β̃_i + z̃_i/16)}`,
  `B̃ = max{1/4, max_{i∈J} β̃_i}`.
* E.4: the direct fixed raw protocol reads all `m` baseline scores `b_i` and payloads `z_i` with `j_v`
  and uses `J = {0, …, m-1}`.

**Formalization Note.**
* `R` and `v` are natural numbers: `⌈·⌉₊` of `Real.logb 2`. `max 1 ⌈log₂(8γ/ε)⌉₊` equals the
  paper's `max{1, ⌈log₂(8γ/ε)⌉}` also when the logarithm is negative.
* `oddMedian x` is the entry of index `⌊R/2⌋` of the sorted list of `x₀, …, x_{R-1}`: for odd `R` the
  `((R+1)/2)`-th order statistic.
* The sampling protocol's seed is `ω : Fin R → Fin 1024 → Addr m` (the draws `V_{t,k}`) with the
  uniform measure. Its stage-one field at position `j < 1024 R` reads the row-C site `a_{V_{t,k}}`,
  `t = ⌊j/1024⌋`, `k = j mod 1024`, with five bits. Stage two reads, for the `p`-th element `i` of `J`
  in increasing order, `b_i` at position `1024R + 2p` and `z_i` at position `1024R + 2p + 1`, with `v`
  bits. The overflow fallback action is `-` (`false`).
* The direct protocol's seed space is `Unit` (with the Dirac measure); its field `2i` reads `b_i` and
  its field `2i+1` reads `z_i`.
-/

/-- `δ = min{1/2, 16ε/γ}` of (8). -/
noncomputable def deltaParam (γ ε : ℝ) : ℝ := min (1 / 2) (16 * ε / γ)

/-- `R = 2⌈log₂(m/δ)⌉ + 1` of (8). -/
noncomputable def RParam (m : ℕ) (γ ε : ℝ) : ℕ :=
  2 * ⌈Real.logb 2 ((m : ℝ) / deltaParam γ ε)⌉₊ + 1

/-- `v = max{1, ⌈log₂(8γ/ε)⌉}` of (8). -/
noncomputable def vParam (γ ε : ℝ) : ℕ := max 1 ⌈Real.logb 2 (8 * γ / ε)⌉₊

/-- The sample size `s = 1024` of E.2. -/
abbrev sampleSize : ℕ := 1024

/-- The median of an odd number of reals: the entry of index `⌊R/2⌋` of the sorted list. -/
noncomputable def oddMedian {R : ℕ} (x : Fin R → ℝ) : ℝ :=
  ((List.ofFn x).mergeSort (fun a b => decide (a ≤ b))).getD (R / 2) 0

/-- The signed sample mean `(2s)^{-1} Σ_k c_i(V_k) y(V_k)` of the values `y` at the sampled
addresses `V`. With `y = a` it is `U_{t,i}`; with `y = Q_5 ∘ a` it is `Ũ_{t,i}` (44). -/
noncomputable def sampleMean {m s : ℕ} (i : Fin m) (V : Fin s → Addr m) (y : Addr m → ℝ) : ℝ :=
  (1 / (2 * (s : ℝ))) * ∑ k, walsh (rr m) i (V k) * y (V k)

/-- The address read by the stage-one field at position `j`. -/
def sampleAt {m R : ℕ} (ω : Fin R → Fin sampleSize → Addr m) (j : ℕ) : Addr m :=
  if h : j / sampleSize < R then ω ⟨j / sampleSize, h⟩ ⟨j % sampleSize, Nat.mod_lt _ (by norm_num)⟩
  else ⟨0, Nat.two_pow_pos _⟩

/-- `Ũ_{t,i}` computed from the received five-bit symbols in the history `h`. -/
noncomputable def stageOneMean {m R : ℕ} (ω : Fin R → Fin sampleSize → Addr m) (h : List ℕ)
    (t : Fin R) (i : Fin m) : ℝ :=
  (1 / (2 * (sampleSize : ℝ))) *
    ∑ k : Fin sampleSize, walsh (rr m) i (ω t k) * recon 5 (h.getD ((t : ℕ) * sampleSize + (k : ℕ)) 0)

/-- `b̃_i = median_t Ũ_{t,i}` from the received symbols. -/
noncomputable def stageOneEstimate {m R : ℕ} (ω : Fin R → Fin sampleSize → Addr m) (h : List ℕ)
    (i : Fin m) : ℝ :=
  oddMedian (fun t : Fin R => stageOneMean ω h t i)

/-- The candidate set `J = {i : b̃_i ≥ 1/8}`. -/
noncomputable def candidates {m R : ℕ} (ω : Fin R → Fin sampleSize → Addr m) (h : List ℕ) :
    Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun i => (1 / 8 : ℝ) ≤ stageOneEstimate ω h i)

/-- The candidates in increasing order. -/
noncomputable def candList {m R : ℕ} (ω : Fin R → Fin sampleSize → Addr m) (h : List ℕ) :
    List (Fin m) :=
  (candidates ω h).sort (· ≤ ·)

/-- The affine scalar requested by the sampling protocol at history `h`. -/
noncomputable def samplingQuery (m R : ℕ) (ω : Fin R → Fin sampleSize → Addr m) (h : List ℕ) :
    AffQuery (Coord m) :=
  if h.length < sampleSize * R then siteC m (Sum.inl (sampleAt ω h.length))
  else
    match (candList ω h)[(h.length - sampleSize * R) / 2]? with
    | some i => if (h.length - sampleSize * R) % 2 = 0 then siteB m i else siteC m (Sum.inr i)
    | none => constSite m

/-- The decision of the sampling protocol from the seed and the complete history. -/
noncomputable def samplingDecide (m : ℕ) (γ : ℝ) (R v : ℕ) (ω : Fin R → Fin sampleSize → Addr m)
    (h : List ℕ) : Bool :=
  if 64 < (candidates ω h).card then false
  else
    let pos : Fin m → ℕ := fun i => (candList ω h).idxOf i
    let βt : Fin m → ℝ := fun i => recon v (h.getD (sampleSize * R + 2 * pos i) 0)
    let zt : Fin m → ℝ := fun i => recon v (h.getD (sampleSize * R + 2 * pos i + 1) 0)
    let At := (candidates ω h).fold max (1 / 4 : ℝ) (fun i => βt i + zt i / 16)
    let Bt := (candidates ω h).fold max (1 / 4 : ℝ) βt
    decide (0 ≤ γ * (At - Bt - 1 / 32))

/-- The length of the field at history `h` in the sampling protocol. -/
def samplingLen (R v : ℕ) (h : List ℕ) : ℕ := if h.length < sampleSize * R then 5 else v

/-- The at-most-two-stage sampling protocol of E.2–E.3 with repetitions `R` and candidate
precision `v`. -/
noncomputable def samplingProtocolRV (m : ℕ) (γ : ℝ) (R v : ℕ) (hv : 1 ≤ v) :
    ReplyProtocol (Coord m) (Fin R → Fin sampleSize → Addr m) where
  ask ω h := decide (h.length < sampleSize * R ∨
    ((candidates ω h).card ≤ 64 ∧ h.length < sampleSize * R + 2 * (candidates ω h).card))
  coef ω h := (samplingQuery m R ω h).1
  const ω h := (samplingQuery m R ω h).2
  len _ h := samplingLen R v h
  quant _ h x := jEnc (samplingLen R v h) x
  decide ω h := samplingDecide m γ R v ω h
  len_pos _ h _ := by unfold samplingLen; split_ifs <;> omega
  quant_lt _ h x _ := jEnc_lt _ x

lemma one_le_vParam (γ ε : ℝ) : 1 ≤ vParam γ ε := le_max_left _ _

/-- The sampling protocol with the parameters (8). -/
noncomputable def samplingProtocol (m : ℕ) (γ ε : ℝ) :
    ReplyProtocol (Coord m) (Fin (RParam m γ ε) → Fin sampleSize → Addr m) :=
  samplingProtocolRV m γ (RParam m γ ε) (vParam γ ε) (one_le_vParam γ ε)

/-- The uniform seed law of the sampling protocol. -/
noncomputable def samplingSeedLaw (m R : ℕ) : Measure (Fin R → Fin sampleSize → Addr m) :=
  ProbabilityTheory.uniformOn Set.univ

/-- The affine scalar requested by the direct protocol at history `h`. -/
noncomputable def directQuery (m : ℕ) (h : List ℕ) : AffQuery (Coord m) :=
  if hj : h.length / 2 < m then
    (if h.length % 2 = 0 then siteB m ⟨h.length / 2, hj⟩ else siteC m (Sum.inr ⟨h.length / 2, hj⟩))
  else constSite m

/-- The decision of the direct protocol. -/
noncomputable def directDecide (m : ℕ) (γ : ℝ) (v : ℕ) (h : List ℕ) : Bool :=
  let βt : Fin m → ℝ := fun i => recon v (h.getD (2 * (i : ℕ)) 0)
  let zt : Fin m → ℝ := fun i => recon v (h.getD (2 * (i : ℕ) + 1) 0)
  let At := Finset.univ.fold max (1 / 4 : ℝ) (fun i => βt i + zt i / 16)
  let Bt := Finset.univ.fold max (1 / 4 : ℝ) βt
  decide (0 ≤ γ * (At - Bt - 1 / 32))

/-- The direct fixed raw protocol of E.4 with precision `v`. -/
noncomputable def directProtocolV (m : ℕ) (γ : ℝ) (v : ℕ) (hv : 1 ≤ v) :
    ReplyProtocol (Coord m) Unit where
  ask _ h := decide (h.length < 2 * m)
  coef _ h := (directQuery m h).1
  const _ h := (directQuery m h).2
  len _ _ := v
  quant _ _ x := jEnc v x
  decide _ h := directDecide m γ v h
  len_pos _ _ _ := hv
  quant_lt _ _ x _ := jEnc_lt v x

/-- The direct protocol with `v` of (8). -/
noncomputable def directProtocol (m : ℕ) (γ ε : ℝ) : ReplyProtocol (Coord m) Unit :=
  directProtocolV m γ (vParam γ ε) (one_le_vParam γ ε)

end DeepQOperator


