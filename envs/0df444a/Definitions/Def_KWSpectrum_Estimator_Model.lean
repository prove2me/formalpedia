-- Prove2me | Definitions.Def_KWSpectrum_Estimator_Model
-- name    : KWSpectrum_Estimator_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:32:03.205171+00:00
-- url     : https://prove2.me/theorems/efda5d63-8ecb-40bb-83ec-f98ae2e5c861
-- title:
--   The spectrum set $\Sigma$ (corrected (5)–(6)), the estimator $E_N(\Delta)$ and outcome law $K_N(\Delta)$ of (7)–(9), the rate function (13), small boundary (pp. 2–3)
-- statement:
--   This file fixes the objects of Keyl and Werner's spectrum estimation theorem. Throughout, $d$ is the dimension of the one-particle space $\mathbb C^d$ and $N$ the number of copies.
--
--   1. **Possible spectra.** The set of possible spectra is the closed ordered simplex
--   $$\Sigma = \Big\{ s \in \mathbb R^d \;\Big|\; s_1 \ge s_2 \ge \dots \ge s_d \ge 0,\ \sum_{j=1}^d s_j = 1 \Big\}.$$
--   2. **Young frames.** A Young frame $Y$ with $N$ boxes and at most $d$ rows has row lengths $Y_1 \ge \dots \ge Y_d \ge 0$ with $\sum_\alpha Y_\alpha = N$. Its normalization is $s_N(Y) = Y/N = (Y_1/N, \dots, Y_d/N) \in \Sigma$.
--   3. **Frame probabilities.** For a $d\times d$ matrix $\rho$, the probability of the frame $Y$ is $\operatorname{tr}(\rho^{\otimes N} P_Y)$, where $P_Y$ is the projection of $(\mathbb C^d)^{\otimes N}$ onto the summand $\mathcal R_Y \otimes \mathcal S_Y$ of the Schur–Weyl decomposition, i.e. the isotypic projection of type $Y$ of the action of the permutations of the $N$ tensor factors.
--   4. **Estimator and outcome law.** For $\Delta \subseteq \mathbb R^d$,
--   $$E_N(\Delta) = \sum_{Y:\ Y/N \in \Delta} P_Y, \qquad K_N(\Delta) = \operatorname{tr}\big(E_N(\Delta)\,\rho^{\otimes N}\big) \in [0,\infty].$$
--   The normalized logarithm $\frac1N \ln K_N(\Delta)$ is taken in the extended reals, with $\ln 0 = -\infty$.
--   5. **Rate function.** For $r, s \in \mathbb R^d$,
--   $$I(s) = \sum_j s_j(\ln s_j - \ln r_j) \in (-\infty, +\infty],$$
--   with $0 \ln 0 = 0$ and $I(s) = +\infty$ as soon as $s_j > 0 = r_j$ for some $j$.
--   6. **Spectrum of $\rho$.** $r$ is the spectrum of $\rho$ when $r \in \Sigma$ and $\rho = U \operatorname{diag}(r) U^*$ for a unitary $U$; this says that $\rho$ is a density matrix whose eigenvalues, listed in decreasing order, are $r_1, \dots, r_d$.
--   7. **Small boundary.** For $\Delta \subseteq \Sigma$, the relative interior and relative closure are the interior and the closure of $\Delta$ in the topology of $\Sigma$ (as a subspace of $\mathbb R^d$). $\Delta$ has small boundary when its relative interior is dense in its relative closure.
--   8. **Content.** The content of a filling $T$ of $Y$ with entries in $\{1,\dots,d\}$ is the vector $\mu$ with $\mu_i$ the number of cells carrying the entry $i$.
--
--   These are the objects of the paper's Theorem (asymptotic exactness of the estimator $Y/N$ and its large-deviation rate) and of the steps of its proof.
--
--   **Formalization Note** Indices are zero-based: Lean's row and coordinate $0$ is the paper's $1$, and fillings take values in `Fin d`. $\rho^{\otimes N}$ is `QAlgorithms.piKron N ρ`, $P_Y$ is the published `QAlgorithms.Schur.isotypicProjector Y` (the central idempotent $\frac{\dim \mathcal S_Y}{N!}\sum_p \chi_Y(p^{-1}) S_p$), frames are `QAlgorithms.Schur.Partition d N`. Traces are real parts of complex traces; $K_N(\Delta)$ is `ENNReal.ofReal` of $\operatorname{Re}\operatorname{tr}(E_N(\Delta)\rho^{\otimes N})$, which is the exact value since this trace is nonnegative for a density matrix. $\ln$ of $K_N$ is `ENNReal.log`, valued in `EReal`. The rate function is `EReal`-valued; it is nonnegative on $\Sigma\times\Sigma$, which is stated as a theorem, not built in. The relative interior and closure live on the subtype of $\Sigma$. At $N = 0$ the vector $Y/N$ is $0$; only limits $N\to\infty$ are used.
-- source:
--   Keyl & Werner, Estimating the spectrum of a density operator, arXiv:quant-ph/0102027v1, pp. 1–3: §I p. 1 (Young frames), §II p. 2 eqs. (1)–(9), p. 3 (small boundary, eq. (13)), §III p. 3 (weights)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SchurWeylDecomposition
import Definitions.Def_QAlgorithms_Defs_SchurCharacters

namespace KWSpectrum.Estimator

open QAlgorithms QAlgorithms.Schur
open scoped ENNReal

/-- Keyl–Werner, arXiv:quant-ph/0102027v1, p. 2, eqs. (5)–(6), corrected: the set `Σ` of possible
spectra of a `d`-level density operator, the closed ordered simplex
`{s ∈ ℝ^d | s₁ ≥ s₂ ≥ ⋯ ≥ s_d ≥ 0, Σ_j s_j = 1}` (index `0` is the paper's index `1`). -/
def SpectrumSet (d : ℕ) : Set (Fin d → ℝ) :=
  {s | Antitone s ∧ (∀ j, 0 ≤ s j) ∧ ∑ j, s j = 1}

/-- p. 2, eq. (9): the normalized Young frame `s_N(Y) = Y/N`, the vector of row lengths
`(Y₁/N, …, Y_d/N)` (row `0` in Lean is the paper's row `1`). -/
noncomputable def youngFrac {d N : ℕ} (Y : Partition d N) : Fin d → ℝ :=
  fun i => (Y.val.rowLen i.val : ℝ) / N

/-- p. 2, eq. (10): the probability `tr(ρ^{⊗N} P_Y)` of the Young frame `Y`, where `P_Y` is the
isotypic projection of `(ℂ^d)^{⊗N}` of type `Y` (`QAlgorithms.Schur.isotypicProjector`) and
`ρ^{⊗N}` is the tensor power `QAlgorithms.piKron N ρ` (real part of the trace). -/
noncomputable def frameProb {d N : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) (Y : Partition d N) : ℝ :=
  effectProb (isotypicProjector Y) (piKron N ρ)

open Classical in
/-- p. 2, eq. (8) with (9): the estimator `E_N(Δ) = Σ_{Y : Y/N ∈ Δ} P_Y`, a sum over the Young
frames with `N` boxes and at most `d` rows. -/
noncomputable def estimatorEffect (d N : ℕ) (Δ : Set (Fin d → ℝ)) :
    Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ :=
  ∑ Y : Partition d N with youngFrac Y ∈ Δ, isotypicProjector Y

/-- p. 2, eq. (7): the outcome probability `K_N(Δ) = tr(E_N(Δ) ρ^{⊗N})`, as an element of
`[0, ∞]` (the real number `Re tr(E_N(Δ) ρ^{⊗N})`, cut off below at `0`). -/
noncomputable def outcomeProb {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) (N : ℕ)
    (Δ : Set (Fin d → ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal (effectProb (estimatorEffect d N Δ) (piKron N ρ))

/-- p. 3, eq. (12), left-hand side: `(1/N) ln K_N(Δ)` in the extended reals, with `ln 0 = −∞`. -/
noncomputable def logRate {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) (Δ : Set (Fin d → ℝ))
    (N : ℕ) : EReal :=
  (((N : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (outcomeProb ρ N Δ)

/-- p. 3, eq. (13): the rate function `I(s) = Σ_j s_j (ln s_j − ln r_j) ∈ [0, ∞]`, the relative
entropy of `s` with respect to `r`, with the conventions `0 · ln 0 = 0` and
`s_j ln(s_j / 0) = +∞` for `s_j > 0`. -/
noncomputable def rate {d : ℕ} (r s : Fin d → ℝ) : EReal :=
  if ∃ j, 0 < s j ∧ r j = 0 then ⊤ else ((∑ j, s j * Real.log (s j / r j) : ℝ) : EReal)

/-- p. 2: `r ∈ Σ` is the spectrum of `ρ`, listed in decreasing order: `ρ = U diag(r) U*` for a
unitary `U`. -/
def IsSpectrumOf {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) (r : Fin d → ℝ) : Prop :=
  r ∈ SpectrumSet d ∧
    ∃ U ∈ Matrix.unitaryGroup (Fin d) ℂ,
      ρ = U * Matrix.diagonal (fun j => (r j : ℂ)) * star U

/-- p. 3: the interior of `Δ ⊆ Σ` relative to `Σ` (subspace topology of `Σ ⊆ ℝ^d`). -/
def relInterior {d : ℕ} (Δ : Set (Fin d → ℝ)) : Set (Fin d → ℝ) :=
  Subtype.val '' interior (Subtype.val ⁻¹' Δ : Set (SpectrumSet d))

/-- p. 3: the closure of `Δ ⊆ Σ` relative to `Σ` (subspace topology of `Σ ⊆ ℝ^d`). -/
def relClosure {d : ℕ} (Δ : Set (Fin d → ℝ)) : Set (Fin d → ℝ) :=
  Subtype.val '' closure (Subtype.val ⁻¹' Δ : Set (SpectrumSet d))

/-- p. 3: `Δ ⊆ Σ` has "small boundary": its interior is dense in its closure, both taken in the
topology of `Σ`. -/
def HasSmallBoundary {d : ℕ} (Δ : Set (Fin d → ℝ)) : Prop :=
  closure (Subtype.val ⁻¹' Δ : Set (SpectrumSet d)) ⊆
    closure (interior (Subtype.val ⁻¹' Δ : Set (SpectrumSet d)))

/-- p. 3: the content (weight) `μ` of a filling `T` of the Young frame `Y` with entries in
`{0, …, d − 1}`: `μ_i` is the number of cells carrying the entry `i`. -/
def content {d N : ℕ} (Y : Partition d N) (T : Y.val.cells → Fin d) : Fin d → ℕ :=
  fun i => (Finset.univ.filter fun a => T a = i).card

/-- Sanity check: for `d = 1` the set `Σ` is the single point `1`. -/
example : (fun _ => (1 : ℝ)) ∈ SpectrumSet 1 := by
  refine ⟨fun _ _ _ => le_rfl, fun _ => zero_le_one, by simp⟩

/-- Sanity check: the rate function vanishes on the diagonal of a strictly positive vector. -/
example {d : ℕ} (r : Fin d → ℝ) (hr : ∀ j, 0 < r j) : rate r r = 0 := by
  have h : ¬ ∃ j, 0 < r j ∧ r j = 0 := fun ⟨j, _, h⟩ => (hr j).ne' h
  simp [rate, h, div_self (hr _).ne']

end KWSpectrum.Estimator


