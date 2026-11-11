-- Prove2me | Definitions.Def_MulticalibrationERM_Oracle_OEMC
-- name    : MulticalibrationERM_Oracle_OEMC
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:51:58.139609+00:00
-- url     : https://prove2.me/theorems/c172691f-0602-4783-a76c-b98d6fba73b3
-- title:
--   §6.2–6.4, Algorithm 4, Appendix H — cell rounding, confidence intervals, the partition, V_P, and OEMC in both modes
-- statement:
--   **Cell rounding** (§6.2). For a map `cell : X → ι` (the cells of a partition), maps $G_x:\Xi\to\Lambda$ and seeds $(\xi_R)_R$, one per cell, $p(x)=G_x(\xi_{R(x)})$ (`cellRound`). `gridQuantile q ξ` is the $\xi$-quantile of a distribution $q$ on the grid (a draw from $q$ when $\xi$ is uniform). The **variance budget** of a partition with singletons $\{x\}$, $x\in O$, and remaining cells $P_{\mathrm{rest}}$ is $V_P=\sum_{x\in O}\omega_x^2r_x^2+\sum_{R\in P_{\mathrm{rest}}}D_X(R)^2$ (`varBudget`).
--
--   **Confidence intervals** (§6.3) from the confidence sample (stream positions $0,\dots,n_{\mathrm{conf}}-1$): $O$ the inputs that occur, $n_x$ their counts, $\hat y_x$ their mean outcomes, $\iota=\max\{1,\log(8n_{\mathrm{conf}}/\delta_0)\}$, $r_x=\min\{1,\sqrt{\iota/n_x}\}$, $I_x=[\hat y_x-r_x,\hat y_x+r_x]\cap[0,1]$. **Partition** (for a total order on $X$ with measurable order intervals, `OrderIntervalsMeasurable`, Remark 2.7): sort the distinct partition-sample inputs $z_1<\dots<z_k$; the cells are the singletons of $O$, the sets $\{z_i\}\setminus O$, the open gaps $(z_i,z_{i+1})\setminus O$ and the two end rays minus $O$ (`cellKey`); `constructionBudget` is $V_P$ of this construction.
--
--   **Algorithm 4 (OEMC)** with the absolute constants `OEMCConsts` $(C,C_0,C_b,C')$ of Appendix H. Randomized mode: $K=\lceil C/\varepsilon\rceil$, $m=K+1$, $S=S_{\mathrm{Had}}$, $\alpha=\varepsilon/(C\sqrt m)$, $T$ the smallest positive integer for which `batchBound` (constants $C_0,C_b$, $N=|S_{\mathrm{Had}}|$, $\kappa=\sqrt m$) is at most $\varepsilon$, $L=\lceil2\alpha^{-2}\log(16mT/\delta)\rceil$, $\eta=\min\{1,\sqrt{\log N/T}\}$; run SignedTests on $T$ examples and return $\bar Q$. It uses $T$ samples (`oemcRandomizedSamples`) and $T(N+L)$ calls. Deterministic mode: the same parameters at accuracy $\varepsilon/2$ and confidence $\delta/4$; $D_{\mathrm{par}}=d+m+\log(8/\delta)$ and $n_{\mathrm{conf}}=n_{\mathrm{part}}=\lceil C'D_{\mathrm{par}}\varepsilon^{-2}\log(eD_{\mathrm{par}}/(\varepsilon\delta))\rceil$ (`oemcAuxSize`); build $O$ and the intervals from $n_{\mathrm{conf}}$ examples with $\delta_0=\delta/8$; train SignedTests with interval hints on the next $T$ fresh examples; build the partition from the next $n_{\mathrm{part}}$ inputs; for each cell draw $t_R$ uniform on the rounds and $\xi_R$ uniform on $[0,1]$ (uniforms unused by training); output $p(x)=$ the $\xi_{R(x)}$-quantile of $Q_{t_{R(x)}}(x)$. It uses $n_{\mathrm{conf}}+T+n_{\mathrm{part}}$ samples (`oemcDeterministicSamples`) and $T(N+L)$ calls.
--
--   **Formalization Note.** Computability of the order and of equality tests (Remark 2.7) is not modelled: the algorithm uses the order and equality directly.
-- source:
--   Okoroafor, The Sample Complexity of Multicalibration with an ERM Oracle, supplied 61-page preprint (PDF SHA256 654c7a8127547d76c5a4b6db236ce672c2c09a70d21d56a3981583e1805d0f8d; exact arXiv revision unresolved, not arXiv:2610.14363v1), pp. 33–37, 56–57, §6.2–6.4, Algorithm 4, Appendix H

import Mathlib
import Definitions.Def_MulticalibrationERM_Oracle_Setting
import Definitions.Def_MulticalibrationERM_Oracle_ERM
import Definitions.Def_MulticalibrationERM_Oracle_Forecast
import Definitions.Def_MulticalibrationERM_Oracle_SignedTests

namespace MulticalibrationERM.Oracle

open MeasureTheory

/-! # Confidence intervals, the partition, cell rounding, and Algorithm 4 (OEMC)

Okoroafor, *The Sample Complexity of Multicalibration with an ERM Oracle* (supplied preprint,
SHA256 654c7a81…), Section 6.2 (cell rounding, p. 33), Section 6.3 (confidence intervals and the
partition, pp. 34–35), Algorithm 4 (p. 36), and Appendix H (parameter choices, pp. 56–57).

Samples are read from a stream `s : ℕ → X × ℝ` (the first component of a `Seeds`): the
confidence sample is `s 0, …, s (n_conf − 1)`; a partition sample of `n_part` inputs starting at
index `poff` is `(s poff).1, …, (s (poff + n_part − 1)).1`. -/

variable {X : Type*} [MeasurableSpace X]

/-- The `D_X`-mass of a set of inputs. -/
noncomputable def LabeledDist.massX (D : LabeledDist X) (A : Set X) : ℝ :=
  (D.μ (Prod.fst ⁻¹' A)).toReal

/-- The variance budget `V_P = ∑_{x ∈ O} ω_x² r_x² + ∑_{R ∈ P_rest} D_X(R)²` (p. 33) of a
partition given by a cell map `cell : X → ι`, whose cells other than the singletons of `O` are
the sets `cell⁻¹{i} \ O` for the labels `i ∈ labels` (a set equal to an `O`-singleton minus `O`
is empty and contributes `0`). -/
noncomputable def varBudget {ι : Type*} (D : LabeledDist X) (O : Finset X) (r : X → ℝ)
    (cell : X → ι) (labels : Finset ι) : ℝ :=
  ∑ x ∈ O, D.atom x ^ 2 * r x ^ 2 + ∑ i ∈ labels, D.massX ({y | cell y = i} \ ↑O) ^ 2

/-- Cell rounding (p. 33): `p(x) = G_x(ξ_{R(x)})`, with one seed `ξ_R` per cell `R` and `R(x)`
the cell of `x`. -/
def cellRound {ι Ξ : Type*} {K : ℕ} (cell : X → ι) (Gq : X → Ξ → Fin (K + 1))
    (seeds : ι → Ξ) : X → Fin (K + 1) :=
  fun x => Gq x (seeds (cell x))

/-- The `ξ`-quantile of a distribution `q` on the grid: the first grid index whose cumulative
probability exceeds `ξ` (the last index if none). For `ξ` uniform on `[0, 1]` it is a draw
from `q`. -/
noncomputable def gridQuantile {K : ℕ} (q : Fin (K + 1) → ℝ) (ξ : ℝ) : Fin (K + 1) :=
  open Classical in
  ⟨min ((List.range (K + 1)).findIdx
      (fun i => decide (ξ < ∑ j ∈ Finset.univ.filter (fun j : Fin (K + 1) => (j : ℕ) ≤ i), q j))) K,
    Nat.lt_succ_of_le (min_le_right _ _)⟩

/-! ### Confidence intervals (p. 34) -/

section Confidence
variable [DecidableEq X]

/-- `O`: the set of inputs occurring in the confidence sample `s 0, …, s (n − 1)`. -/
def confSet (s : ℕ → X × ℝ) (n : ℕ) : Finset X := (Finset.range n).image (fun i => (s i).1)

/-- `n_x`: the number of occurrences of `x` in the confidence sample. -/
def confCount (s : ℕ → X × ℝ) (n : ℕ) (x : X) : ℕ :=
  ((Finset.range n).filter (fun i => (s i).1 = x)).card

/-- `ŷ_x`: the average outcome at `x` in the confidence sample. -/
noncomputable def confMean (s : ℕ → X × ℝ) (n : ℕ) (x : X) : ℝ :=
  (∑ i ∈ (Finset.range n).filter (fun i => (s i).1 = x), (s i).2) / confCount s n x

/-- `ι = max{1, log(8 n_conf / δ₀)}`. -/
noncomputable def confIota (n : ℕ) (δ₀ : ℝ) : ℝ := max 1 (Real.log (8 * n / δ₀))

/-- `r_x = min{1, √(ι / n_x)}`. -/
noncomputable def confRad (s : ℕ → X × ℝ) (n : ℕ) (δ₀ : ℝ) (x : X) : ℝ :=
  min 1 (Real.sqrt (confIota n δ₀ / confCount s n x))

/-- Lower end of `I_x = [ŷ_x − r_x, ŷ_x + r_x] ∩ [0, 1]`. -/
noncomputable def confLo (s : ℕ → X × ℝ) (n : ℕ) (δ₀ : ℝ) (x : X) : ℝ :=
  max 0 (confMean s n x - confRad s n δ₀ x)

/-- Upper end of `I_x = [ŷ_x − r_x, ŷ_x + r_x] ∩ [0, 1]`. -/
noncomputable def confHi (s : ℕ → X × ℝ) (n : ℕ) (δ₀ : ℝ) (x : X) : ℝ :=
  min 1 (confMean s n x + confRad s n δ₀ x)

end Confidence

/-! ### The partition (p. 34), for a total order on `X` -/

section Partition
variable [LinearOrder X]

/-- Remark 2.7: the order intervals of the total order on `X` are measurable (open intervals,
closed intervals, in particular singletons, and the two kinds of open rays). Computability of the
order and of equality tests is not modelled: the algorithms below use the order relation and
equality directly. -/
def OrderIntervalsMeasurable (X : Type*) [MeasurableSpace X] [LinearOrder X] : Prop :=
  ∀ a b : X, MeasurableSet (Set.Ioo a b) ∧ MeasurableSet (Set.Icc a b) ∧
    MeasurableSet (Set.Iio a) ∧ MeasurableSet (Set.Ioi a)

/-- The distinct values `z_1 < ⋯ < z_k` of the partition sample `(s poff).1, …,
(s (poff + n − 1)).1`, sorted. -/
noncomputable def partSorted (s : ℕ → X × ℝ) (poff n : ℕ) : List X :=
  ((Finset.range n).image (fun i => (s (poff + i)).1)).sort (· ≤ ·)

/-- The label of the cell of `x` in the partition `P`: the singleton `{x}` for `x ∈ O`
(label `3·(position of x in O)`), the cell `{z_i} \ O` (label `3i + 1`), or the open gap
`(z_i, z_{i+1}) \ O` (label `3i + 2`, where `i` is the number of `z`'s below `x`; `i = 0` and
`i = k` are the two unbounded intervals). -/
noncomputable def cellKey (O : Finset X) (zs : List X) (x : X) : ℕ :=
  if x ∈ O then 3 * (O.sort (· ≤ ·)).idxOf x
  else if x ∈ zs then 3 * zs.idxOf x + 1
  else 3 * (zs.filter (· < x)).length + 2

/-- The labels of the cells of `P_rest` (possibly empty cells included; they contribute
nothing). -/
def restLabels (zs : List X) : Finset ℕ :=
  (Finset.range zs.length).image (fun i => 3 * i + 1) ∪
    (Finset.range (zs.length + 1)).image (fun i => 3 * i + 2)

/-- The variance budget `V_P` of the construction of Section 6.3: confidence sample
`s 0, …, s (n_conf − 1)` with failure parameter `δ₀`, partition sample of `n_part` inputs from
index `poff`. -/
noncomputable def constructionBudget (D : LabeledDist X) (s : ℕ → X × ℝ) (nconf npart poff : ℕ)
    (δ₀ : ℝ) : ℝ :=
  varBudget D (confSet s nconf) (confRad s nconf δ₀)
    (cellKey (confSet s nconf) (partSorted s poff npart))
    (restLabels (partSorted s poff npart))

end Partition

/-! ### Algorithm 4 and the parameters of Appendix H -/

/-- The absolute constants on which the parameter choices of Appendix H depend: `C` (in `K` and
`α`), the constant `C₀` of `Reg` (Theorem 2.5), the constant `Cb` of the bound of Theorem 3.8,
and `C'` (`Cn`) in `n_conf = n_part`. -/
structure OEMCConsts where
  C : ℝ
  C₀ : ℝ
  Cb : ℝ
  Cn : ℝ

/-- The randomized-mode parameters of Appendix H for accuracy `ε`, confidence `δ` and VC bound
`d`: `K = ⌈C/ε⌉`, `m = K + 1`, `S = S_Had`, `α = ε/(C√m)`, `T` the smallest positive integer
for which the bound of Theorem 3.8 with `N = |S_Had|`, `κ = √m` is at most `ε`,
`L = ⌈2α⁻² log(16mT/δ)⌉`, `η = min{1, √(log N / T)}`. -/
noncomputable def oemcParams (c : OEMCConsts) (ε δ : ℝ) (d : ℕ) :
    Σ K : ℕ, A1Params K :=
  let K := ⌈c.C / ε⌉₊
  let S := hadamardTests (K + 1)
  let N := S.length
  let α := ε / (c.C * Real.sqrt (K + 1))
  let T := sInf {T : ℕ | 1 ≤ T ∧ batchBound c.C₀ c.Cb K N (Real.sqrt (K + 1)) d T δ α ≤ ε}
  ⟨K, { S := S, T := T, η := a1Eta N T, L := ⌈a1Lmin K T α δ⌉₊ }⟩

variable {Ω : Type*} [MeasurableSpace Ω] {H : Set (X → Bool)}

/-- Algorithm 4, randomized mode: run `SignedTests(S_Had, K, T, η, L)` on `T` examples and
return `Q̄ = T⁻¹ ∑_t Q_t`. -/
noncomputable def oemcRandomized (c : OEMCConsts) (ε δ : ℝ) (d : ℕ) (O : ERMOracle X H 0 Ω)
    (ω : Seeds X Ω) : X → Fin ((oemcParams c ε δ d).1 + 1) → ℝ :=
  signedTestsQbar O (oemcParams c ε δ d).1 (oemcParams c ε δ d).2 ω

/-- The number of labeled examples used by the randomized mode: `T`. -/
noncomputable def oemcRandomizedSamples (c : OEMCConsts) (ε δ : ℝ) (d : ℕ) : ℕ :=
  (oemcParams c ε δ d).2.T

/-- `n_conf = n_part = ⌈C' D_par ε⁻² log(e D_par/(εδ))⌉` with `D_par = d + m + log(8/δ)`
(Appendix H, deterministic mode; `m = K + 1` for the parameters at accuracy `ε/2`). -/
noncomputable def oemcAuxSize (c : OEMCConsts) (ε δ : ℝ) (d : ℕ) : ℕ :=
  let m : ℝ := (oemcParams c (ε / 2) (δ / 4) d).1 + 1
  let Dpar : ℝ := d + m + Real.log (8 / δ)
  ⌈c.Cn * Dpar * ε⁻¹ ^ 2 * Real.log (Real.exp 1 * Dpar / (ε * δ))⌉₊

/-- Algorithm 4, deterministic mode (lines 5–10), for an input set with a total order:
parameters for accuracy `ε/2` and confidence `δ/4`; confidence sample `s 0, …, s (n_conf − 1)`
with `δ₀ = δ/8`; training by SignedTests with interval hints on the `T` fresh examples
`s n_conf, …`; partition sample of `n_part` fresh inputs from index `n_conf + T`; for each cell
`R` the seed `(t_R, ξ_R)`, `t_R` uniform on the rounds and `ξ_R` uniform on `[0, 1]`, read from
the uniforms with indices `T(N + L) + 2·label`, `T(N + L) + 2·label + 1` (unused by training);
the output is `p(x) = ` the `ξ_{R(x)}`-quantile of `Q_{t_{R(x)}}(x)`. -/
noncomputable def oemcDeterministic [LinearOrder X] (c : OEMCConsts) (ε δ : ℝ) (d : ℕ)
    (O : ERMOracle X H 0 Ω) (ω : Seeds X Ω) : X → Fin ((oemcParams c (ε / 2) (δ / 4) d).1 + 1) :=
  let K := (oemcParams c (ε / 2) (δ / 4) d).1
  let P := (oemcParams c (ε / 2) (δ / 4) d).2
  let n := oemcAuxSize c ε δ d
  let s := ω.1
  let Oset := confSet s n
  let lo := hintLo K Oset (confLo s n (δ / 8))
  let hi := hintHi K Oset (confHi s n (δ / 8))
  let Qs := (a1State O K P lo hi n ω P.T).Qs
  let zs := partSorted s (n + P.T) n
  let base := a1Calls P
  fun x =>
    let key := cellKey Oset zs x
    let tR : ℕ := min ⌊((ω.2.2.1 (base + 2 * key) : ℝ)) * P.T⌋₊ (P.T - 1)
    let ξR : ℝ := ω.2.2.1 (base + 2 * key + 1)
    gridQuantile ((Qs.getD tR (fun _ _ => 0)) x) ξR

/-- The number of labeled examples used by the deterministic mode: `n_conf + T + n_part`. -/
noncomputable def oemcDeterministicSamples (c : OEMCConsts) (ε δ : ℝ) (d : ℕ) : ℕ :=
  oemcAuxSize c ε δ d + (oemcParams c (ε / 2) (δ / 4) d).2.T + oemcAuxSize c ε δ d

end MulticalibrationERM.Oracle


