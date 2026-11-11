-- Prove2me | Definitions.Def_MulticalibrationERM_Oracle_SignedTests
-- name    : MulticalibrationERM_Oracle_SignedTests
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:51:07.038261+00:00
-- url     : https://prove2.me/theorems/b0c08aaa-0617-4287-af0d-4fa271c6c553
-- title:
--   Algorithm 1 (SignedTests), with and without interval hints — the averaged predictor Q̄ and its call count
-- statement:
--   **Randomness.** A run of Algorithm 1 is a deterministic function of a seed drawn from `seedMeasure D ν`: an i.i.d. stream of labeled examples from $D$, i.i.d. standard Gaussians, i.i.d. uniforms on $[0,1]$, and i.i.d. oracle seeds of law $\nu$, all independent. Oracle call number $c$ uses its own Gaussians and oracle seed, and the test draw of auxiliary call $c$ uses its own uniform.
--
--   **Algorithm 1** $\mathrm{SignedTests}(S,K,T,\eta,L)$, for a list $S$ of $N$ tests, one Gaussian follow-the-perturbed-leader learner $A_\sigma$ over $H$ with horizon $T$ per test, $w_1$ uniform on $S$. Round $t$ (here $t=0,\dots,T-1$; example $t$ of the stream, shifted by `off`):
--   1. for $i\le L$: draw a test $\sigma^{(i)}\sim w_t$ (inverse c.d.f. of a uniform) and $h^{(i)}\sim\pi_{t,\sigma^{(i)}}$ (one ERM call); $\hat A_t(x)=L^{-1}\sum_i h^{(i)}(x)\,\sigma^{(i)}$; $Q_t(x)=\mathrm{Minimax}_{\Lambda_x}(\hat A_t(x))$; $\mu_t(x)=\sum_vQ_t(x)(v)\,v$. These draws precede the example and are retained;
--   2. receive $(X_t,Y_t)$;
--   3. for each test $\sigma$: $Z_{t,\sigma}=(\mu_t(X_t)-Y_t)\sum_v\sigma_vQ_t(X_t)(v)$; draw $h_{t,\sigma}\sim\pi_{t,\sigma}$ with fresh randomness (one ERM call), $\hat s_{t,\sigma}=h_{t,\sigma}(X_t)Z_{t,\sigma}$; give $(X_t,Z_{t,\sigma})$ to $A_\sigma$;
--   4. $w_{t+1}(\sigma)\propto w_t(\sigma)\exp(\eta\,\hat s_{t,\sigma})$.
--
--   Without hints $\Lambda_x=\Lambda$ (`signedTestsQbar`). **With interval hints** (`a1Qbar … lo hi`), for a finite set $O$ with intervals $[ylo_x,yhi_x]$, $\Lambda_x=\Lambda\cap[\lfloor K\,ylo_x\rfloor/K,\lceil K\,yhi_x\rceil/K]$ for $x\in O$ and $\Lambda$ otherwise (`hintLo`, `hintHi`). The output is the **averaged predictor** $\bar Q_x(v)=T^{-1}\sum_tQ_t(x)(v)$. A run makes $N+L$ ERM calls per round, `a1Calls` $=T(N+L)$ in total. `a1Eta N T` $=\min\{1,\sqrt{\log N/T}\}$, `a1Lmin K T α δ` $=2\alpha^{-2}\log(16mT/\delta)$, and
--   $$\texttt{batchBound}=\frac1{2K}+\kappa\Big[\frac1T\mathrm{Reg}\big(T,d,\tfrac{\delta}{8N}\big)+C\sqrt{\frac{d\log(eT)+\log(8N/\delta)}{T}}+\alpha\Big]$$
--   is the bound of Theorem 3.8 with its constants $C_0$ (in Reg) and $C$ as parameters.
-- source:
--   Okoroafor, The Sample Complexity of Multicalibration with an ERM Oracle, supplied 61-page preprint (PDF SHA256 654c7a8127547d76c5a4b6db236ce672c2c09a70d21d56a3981583e1805d0f8d; exact arXiv revision unresolved, not arXiv:2610.14363v1), pp. 18–20, 35, Algorithm 1, §3.3, §6.3

import Mathlib
import Definitions.Def_MulticalibrationERM_Oracle_Setting
import Definitions.Def_MulticalibrationERM_Oracle_ERM
import Definitions.Def_MulticalibrationERM_Oracle_Forecast

namespace MulticalibrationERM.Oracle

open MeasureTheory ProbabilityTheory

/-! # Algorithm 1 (SignedTests), with and without interval hints

Okoroafor, *The Sample Complexity of Multicalibration with an ERM Oracle* (supplied preprint,
SHA256 654c7a81…), Algorithm 1 (p. 19), the averaged predictor `Q̄` (p. 20), and SignedTests with
interval hints (p. 35).

**Randomness.** A run is a deterministic function of a seed
`(samples, gauss, unif, oseed) : Seeds X Ω`, drawn from `seedMeasure D ν`: i.i.d. labeled examples
from `D`, i.i.d. standard Gaussians `gauss c s`, i.i.d. uniform numbers in `[0, 1]`, and i.i.d.
oracle seeds of law `ν`. Oracle call number `c` (counted from `0`) uses the Gaussians `gauss c ·`
for its perturbation and the oracle seed `oseed c`; the test draw of auxiliary call `c` uses
`unif c`. Every call therefore has fresh, independent randomness.

**Rounds** are numbered `t = 0, …, T − 1` (the paper's `1, …, T`); round `t` reads the example
`samples (off + t)`. Round `t` makes the `L` auxiliary calls `c = t(N + L) + i`, `i < L`, then the
`N` learner calls `c = t(N + L) + L + j`, one per test `j < N`, where `N = |S|`.

Tests are indexed by `j < N` (`S.getD j 0` is test `j`); feedback and weights are stored as
functions of the test index. -/

variable {X : Type*} {Ω : Type*} [MeasurableSpace Ω]

/-- The seed of a run: labeled examples, Gaussians, uniforms and oracle seeds. -/
abbrev Seeds (X Ω : Type*) := (ℕ → X × ℝ) × (ℕ → ℕ → ℝ) × (ℕ → unitInterval) × (ℕ → Ω)

/-- The law of the seed: all coordinates independent; examples i.i.d. `D`, Gaussians i.i.d.
`N(0, 1)`, uniforms i.i.d. on `[0, 1]`, oracle seeds i.i.d. `ν`. -/
noncomputable def seedMeasure [MeasurableSpace X] (D : LabeledDist X) (ν : Measure Ω) :
    Measure (Seeds X Ω) :=
  (Measure.infinitePi fun _ : ℕ => D.μ).prod
    ((Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod
      ((Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval)).prod
        (Measure.infinitePi fun _ : ℕ => ν)))

/-- A draw from a distribution `w` on test indices `0, …, N − 1` by inversion of a uniform
number `u`: the first `j` with `u · ∑_k w_k < ∑_{k ≤ j} w_k` (the last index if none). -/
noncomputable def catSample (N : ℕ) (w : ℕ → ℝ) (u : ℝ) : ℕ :=
  open Classical in
  min ((List.range N).findIdx
      (fun j => decide (u * ∑ k ∈ Finset.range N, w k < ∑ k ∈ Finset.range (j + 1), w k)))
    (N - 1)

/-- The parameters of Algorithm 1: the list `S` of tests, the grid size `K`, the number of rounds
`T`, the learning rate `η`, the number `L` of auxiliary draws. -/
structure A1Params (K : ℕ) where
  S : List (Fin (K + 1) → ℝ)
  T : ℕ
  η : ℝ
  L : ℕ

/-- The state of Algorithm 1 before a round: the history of past inputs with the feedback of every
test (oldest first), the exponential weights `w_t` on tests, and the forecasts `Q_1, …, Q_t`
announced so far (each a map from inputs to distributions on the grid). -/
structure A1State (X : Type*) (K : ℕ) where
  hist : List (X × (ℕ → ℝ))
  w : ℕ → ℝ
  Qs : List (X → Fin (K + 1) → ℝ)

variable {H : Set (X → Bool)}

/-- One round `t` of Algorithm 1 with interval hints `[lo x, hi x]` (grid indices); without hints
`lo x = 0`, `hi x = K`.

* (lines 3–5) For `i < L`: draw a test `σ⁽ⁱ⁾ ∼ w_t` and a hypothesis `h⁽ⁱ⁾ ∼ π_{t,σ⁽ⁱ⁾}` (one
  ERM call); `Â_t(x) = L⁻¹ ∑_i h⁽ⁱ⁾(x) σ⁽ⁱ⁾`, `Q_t(x) = Minimax_{Λ_x}(Â_t(x))`,
  `µ_t(x) = ∑_v Q_t(x)(v) v`. These draws precede the example and are retained.
* (line 6) Receive `(X_t, Y_t)`.
* (lines 7–10) For every test `σ`: `Z_{t,σ} = (µ_t(X_t) − Y_t) ∑_v σ_v Q_t(X_t)(v)`; draw
  `h_{t,σ} ∼ π_{t,σ}` with fresh randomness (one ERM call), `ŝ_{t,σ} = h_{t,σ}(X_t) Z_{t,σ}`;
  give `(X_t, Z_{t,σ})` to the learner of `σ` (appended to the history).
* (line 11) `w_{t+1}(σ) ∝ w_t(σ) exp(η ŝ_{t,σ})`.

The learner of test `j` is Gaussian follow-the-perturbed-leader over `H` with horizon `T`
(`γ = ftplScale T`), run on the history of inputs and the feedback of test `j`. -/
noncomputable def a1Step (O : ERMOracle X H 0 Ω) (K : ℕ) (P : A1Params K) (lo hi : X → ℕ)
    (off : ℕ) (ω : Seeds X Ω) (t : ℕ) (st : A1State X K) : A1State X K :=
  let N := P.S.length
  let base := t * (N + P.L)
  let γ := ftplScale P.T
  let n := st.hist.length
  let draw : ℕ → ℕ → X → Bool := fun j c =>
    ftplDraw O γ n (fun s => (st.hist.get s).1) (fun s => (st.hist.get s).2 j)
      (fun s => ω.2.1 c s) (ω.2.2.2 c)
  let σi : ℕ → ℕ := fun i => catSample N st.w (ω.2.2.1 (base + i))
  let Ahat : X → Fin (K + 1) → ℝ := fun x v =>
    (1 / (P.L : ℝ)) * ∑ i ∈ Finset.range P.L,
      pm (draw (σi i) (base + i) x) * (P.S.getD (σi i) 0) v
  let Q : X → Fin (K + 1) → ℝ := fun x => minimax K (lo x) (hi x) (Ahat x)
  let μt : X → ℝ := fun x => gridMean (Q x)
  let Xt := (ω.1 (off + t)).1
  let Yt := (ω.1 (off + t)).2
  let Z : ℕ → ℝ := fun j => (μt Xt - Yt) * ∑ v, (P.S.getD j 0) v * Q Xt v
  let shat : ℕ → ℝ := fun j => pm (draw j (base + P.L + j) Xt) * Z j
  let wnum : ℕ → ℝ := fun j => st.w j * Real.exp (P.η * shat j)
  { hist := st.hist ++ [(Xt, Z)]
    w := fun j => wnum j / ∑ k ∈ Finset.range N, wnum k
    Qs := st.Qs ++ [Q] }

/-- The state after `t` rounds of Algorithm 1 (`w_1` uniform on the `N` tests). -/
noncomputable def a1State (O : ERMOracle X H 0 Ω) (K : ℕ) (P : A1Params K) (lo hi : X → ℕ)
    (off : ℕ) (ω : Seeds X Ω) : ℕ → A1State X K
  | 0 => { hist := [], w := fun _ => 1 / (P.S.length : ℝ), Qs := [] }
  | t + 1 => a1Step O K P lo hi off ω t (a1State O K P lo hi off ω t)

/-- The averaged randomized predictor `Q̄_x(v) = T⁻¹ ∑_{t ≤ T} Q_t(x)(v)` returned by
Algorithm 1 with interval hints `lo, hi`, reading its examples from `samples (off + t)`. -/
noncomputable def a1Qbar (O : ERMOracle X H 0 Ω) (K : ℕ) (P : A1Params K) (lo hi : X → ℕ)
    (off : ℕ) (ω : Seeds X Ω) : X → Fin (K + 1) → ℝ :=
  fun x v => (1 / (P.T : ℝ)) * ((a1State O K P lo hi off ω P.T).Qs.map (fun Q => Q x v)).sum

/-- The averaged predictor of Algorithm 1 without hints (`Λ_x = Λ` for every `x`), examples
`samples 0, …, samples (T − 1)`. -/
noncomputable def signedTestsQbar (O : ERMOracle X H 0 Ω) (K : ℕ) (P : A1Params K)
    (ω : Seeds X Ω) : X → Fin (K + 1) → ℝ :=
  a1Qbar O K P (fun _ => 0) (fun _ => K) 0 ω

/-- The number of weighted ERM calls of a run of Algorithm 1: `N + L` per round,
`T (N + L)` in total. -/
def a1Calls {K : ℕ} (P : A1Params K) : ℕ := P.T * (P.S.length + P.L)

/-- The learning rate `η = min{1, √(log N / T)}` of Theorem 3.8. -/
noncomputable def a1Eta (N T : ℕ) : ℝ := min 1 (Real.sqrt (Real.log N / T))

/-- The number of auxiliary draws required by Theorem 3.8: `2 α⁻² log(16 m T / δ)`, `m = K + 1`. -/
noncomputable def a1Lmin (K T : ℕ) (α δ : ℝ) : ℝ :=
  2 * α⁻¹ ^ 2 * Real.log (16 * (K + 1) * T / δ)

/-- The bound of Theorem 3.8:
`1/(2K) + κ [T⁻¹ Reg(T, d, δ/(8N)) + Cb √((d log(eT) + log(8N/δ))/T) + α]`. -/
noncomputable def batchBound (C₀ Cb : ℝ) (K N : ℕ) (κ : ℝ) (d : ℕ) (T : ℕ) (δ α : ℝ) : ℝ :=
  1 / (2 * (K : ℝ)) + κ * ((1 / (T : ℝ)) * Reg C₀ T d (δ / (8 * N)) +
    Cb * Real.sqrt ((d * Real.log (Real.exp 1 * T) + Real.log (8 * N / δ)) / T) + α)

/-- Interval hints from a finite set `O` of inputs with intervals `[ylo x, yhi x]` (p. 35):
`Λ_x = Λ ∩ [⌊K ylo_x⌋/K, ⌈K yhi_x⌉/K]` for `x ∈ O` and `Λ_x = Λ` otherwise, as grid indices. -/
noncomputable def hintLo [DecidableEq X] (K : ℕ) (O : Finset X) (ylo : X → ℝ) (x : X) : ℕ :=
  if x ∈ O then min K ⌊(K : ℝ) * ylo x⌋₊ else 0

/-- Upper hint index, see `hintLo`. -/
noncomputable def hintHi [DecidableEq X] (K : ℕ) (O : Finset X) (yhi : X → ℝ) (x : X) : ℕ :=
  if x ∈ O then min K ⌈(K : ℝ) * yhi x⌉₊ else K

end MulticalibrationERM.Oracle


