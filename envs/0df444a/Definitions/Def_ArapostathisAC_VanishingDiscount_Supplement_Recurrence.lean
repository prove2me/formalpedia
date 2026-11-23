-- Prove2me | Definitions.Def_ArapostathisAC_VanishingDiscount_Supplement_Recurrence
-- name    : ArapostathisAC_VanishingDiscount_Supplement_Recurrence
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T18:02:35.376077+00:00
-- url     : https://prove2.me/theorems/4c009829-b779-4803-94f9-f9342052623d
-- title:
--   Recurrence conditions of §5.1–§5.2: $n$-step probabilities, hitting times $\tau_B$, invariant sets, Assumptions 5.1–5.13 and the ACOE for a signed cost
-- statement:
--   On the countable-state controlled Markov process of §5 ($S=\{0,1,2,\dots\}$, compact $U(i)$, continuity in the action), for $f\in\Pi_{SD}$:
--
--   1. $P^n(f)(i,j)=\mathcal P^f_i(X_n=j)$; $\tau_B=\min\{t\ge1:X_t\in B\}$ (5.11), with $E^f_i[\tau_B]\in[0,\infty]$;
--   2. an **invariant set** is a nonempty $C$ with $P(C\mid i,f(i))=1$ for $i\in C$; a state is **recurrent** if the chain returns to it a.s.; the chain is **aperiodic** if every recurrent state has period one.
--   3. **Assumption 5.1**: a finite $B$ and $K>0$ with $E^f_i\tau_B<K$ for all $i,f$, and no two disjoint invariant sets under any $f$. **5.2**: $K>0$ and, for each $f$, a state $j(f)$ with $E^f_i\tau_{\{j(f)\}}<K$ for all $i$. **5.3**: a finite $B$, $n\ge1$, $\alpha>0$ with $\sum_{j\in B}P^n(f)(i,j)\ge\alpha$ for all $i,f$, and no two disjoint invariant sets. **5.4**: $n\ge1$, $\alpha>0$ with $\sum_j\min\{P^n(f)(i_1,j),P^n(f)(i_2,j)\}\ge\alpha$. **5.5**: $n\ge1$, $\rho>0$ and probability vectors $\eta(f)$ with $\sum_j|P^m(f)(i,j)-\eta(f)(j)|\le2(1-\rho)^{\lfloor m/n\rfloor}$ for all $i$ and $m\ge1$.
--   4. The ACOE (5.1) for a signed cost $c$ and action sets $U$; **Assumption 5.6**: one $K>0$ such that for every bounded measurable $c$ and every collection of nonempty compact $U(i)$ of admissible actions on which $c(i,\cdot)$ is continuous, the ACOE has a bounded solution with $\|h\|\le K\|c\|$.
--   5. **Assumptions 5.7–5.12**: Cesàro limits $\eta_i(f)\in\mathcal P(S)$ of $P^n(f)(i,\cdot)$ exist (5.7); $f\mapsto\eta_i(f)$ is continuous (5.8); they exist and $\{\eta_i(f)\}_f$ is tight (5.9); every $f$ gives a recurrent chain (5.10); no two disjoint invariant sets (5.11); $\{P(f)(i,\cdot)\}_{i,f}$ is tight (5.12).
--   6. **Assumption 5.13**: the killed kernel $\tilde P(f)(i,j)=P(f)(i,j)$ for $j\ne0$, $0$ for $j=0$, and $w:S\to\mathbb R_+$ with (i) $c(i,f(i))+1+\sum_j\tilde P(f)(i,j)w(j)\le w(i)$, (ii) $f\mapsto\sum_jP(f)(i,j)w(j)$ continuous, (iii) $\sum_j\tilde P^n(f)(i,j)w(j)\to0$.
--
--   **Formalization Note** Assumption 5.3 is stated with $n$-step probabilities (the printed display omits the superscript; see Theorem 5.4). Continuity in $f$ refers to the product topology on $\Pi_{SD}$ and is stated for sequences, which suffices because a countable product of metric spaces is metrizable; weak convergence of probability vectors on $S$ is pointwise convergence. $\tilde P^n(f)(i,j)$ is the probability of $X_1,\dots,X_n\ne0$ and $X_n=j$. Sums involving $w$ are computed in $[0,\infty]$.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), pp. 302–306, (5.11), Assumptions 5.1–5.13

import Mathlib
import Definitions.Def_ArapostathisAC_VanishingDiscount_CMP
import Definitions.Def_ArapostathisAC_VanishingDiscount_StationaryChain

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace ArapostathisAC.VanishingDiscount.Supplement

open ArapostathisAC.VanishingDiscount

variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]

/-- The `n`-step transition probability `Pⁿ(f)(i, j) = 𝒫^f_i(X_n = j)` of the chain of
`f ∈ Π_SD` (p. 294, p. 303). -/
noncomputable def nstep (M : CMP A) (f : StationaryPolicy M) (n i j : ℕ) : ℝ :=
  (pathMeasure M f.toPolicy i {ω | (ω n).1 = j}).toReal

/-- The first entrance time after time zero (5.11) (p. 302), `τ_B = min {t ≥ 1 : X_t ∈ B}`, equal to
`⊤` if the trajectory never enters `B` at a time `t ≥ 1`. -/
noncomputable def hitTime (B : Set ℕ) (ω : ℕ → ℕ × A) : ℕ∞ :=
  ⨅ t : {t : ℕ // 1 ≤ t ∧ (ω t).1 ∈ B}, (t.1 : ℕ∞)

/-- `E^f_i[τ_B]`, in `[0, ∞]`. -/
noncomputable def meanHit (M : CMP A) (f : StationaryPolicy M) (B : Set ℕ) (i : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, ((hitTime B ω : ℕ∞) : ℝ≥0∞) ∂(pathMeasure M f.toPolicy i)

/-- `C` is an invariant (closed) set of the chain of `f ∈ Π_SD`: `C` is nonempty and
`P(C | i, f(i)) = 1` for every `i ∈ C`. -/
def IsInvariantSet (M : CMP A) (f : StationaryPolicy M) (C : Set ℕ) : Prop :=
  C.Nonempty ∧ ∀ i ∈ C, M.P (i, f.1 i) C = 1

/-- The chain of `f ∈ Π_SD` does not have two disjoint invariant sets. -/
def NoTwoDisjointInvariant (M : CMP A) (f : StationaryPolicy M) : Prop :=
  ∀ C D : Set ℕ, IsInvariantSet M f C → IsInvariantSet M f D → ¬ Disjoint C D

/-- Assumption 5.1 (p. 302): there are a finite `B ⊂ S` and `K > 0` with `E^f_i[τ_B] < K` for all
`i ∈ S` and `f ∈ Π_SD`; and for every `f ∈ Π_SD` the chain has no two disjoint invariant sets. -/
def Assumption51 (M : CMP A) : Prop :=
  (∃ B : Set ℕ, B.Finite ∧ ∃ K : ℝ, 0 < K ∧
    ∀ (f : StationaryPolicy M) (i : ℕ), meanHit M f B i < ENNReal.ofReal K) ∧
  ∀ f : StationaryPolicy M, NoTwoDisjointInvariant M f

/-- Assumption 5.2 (p. 302): there is `K > 0` such that every `f ∈ Π_SD` has a state `j(f)` with
`E^f_i[τ_{j(f)}] < K` for all `i ∈ S`. -/
def Assumption52 (M : CMP A) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ f : StationaryPolicy M, ∃ j : ℕ,
    ∀ i, meanHit M f {j} i < ENNReal.ofReal K

/-- Assumption 5.3 (simultaneous Doeblin, pp. 302–303), with the `n`-step transition probability:
there are a finite `B`, an integer `n ≥ 1` and `α > 0` with `∑_{j ∈ B} Pⁿ(f)(i, j) ≥ α` for all
`i ∈ S` and `f ∈ Π_SD`; and for every `f ∈ Π_SD` the chain has no two disjoint invariant sets. -/
def Assumption53 (M : CMP A) : Prop :=
  (∃ B : Finset ℕ, ∃ n : ℕ, 1 ≤ n ∧ ∃ α : ℝ, 0 < α ∧
    ∀ (f : StationaryPolicy M) (i : ℕ), α ≤ ∑ j ∈ B, nstep M f n i j) ∧
  ∀ f : StationaryPolicy M, NoTwoDisjointInvariant M f

/-- Assumption 5.4 (scrambling, p. 303): there are `n ≥ 1` and `α > 0` with
`∑_j min {Pⁿ(f)(i₁, j), Pⁿ(f)(i₂, j)} ≥ α` for all `f ∈ Π_SD` and `i₁, i₂ ∈ S`. -/
def Assumption54 (M : CMP A) : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ ∃ α : ℝ, 0 < α ∧ ∀ (f : StationaryPolicy M) (i₁ i₂ : ℕ),
    α ≤ ∑' j, min (nstep M f n i₁ j) (nstep M f n i₂ j)

/-- Assumption 5.5 (ergodicity, p. 303): there are `n ≥ 1` and `ρ > 0` such that every
`f ∈ Π_SD` has a probability vector `η(f)` with `∑_j |Pᵐ(f)(i, j) − η(f)(j)| ≤ 2(1 − ρ)^⌊m/n⌋`
for all `i ∈ S` and `m ≥ 1`. -/
def Assumption55 (M : CMP A) : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∀ f : StationaryPolicy M, ∃ η : ℕ → ℝ,
    (∀ j, 0 ≤ η j) ∧ HasSum η 1 ∧ ∀ i m, 1 ≤ m →
      ∑' j, |nstep M f m i j - η j| ≤ 2 * (1 - ρ) ^ (m / n)

/-- State `i` is recurrent for the chain of `f ∈ Π_SD`: started at `i`, the chain returns to `i`
with probability one. -/
def IsRecurrentState (M : CMP A) (f : StationaryPolicy M) (i : ℕ) : Prop :=
  pathMeasure M f.toPolicy i {ω | returnTime i ω = ⊤} = 0

/-- The chain of `f ∈ Π_SD` is aperiodic: every recurrent state has period one, i.e. `1` is the
only common divisor of the times `n ≥ 1` with `Pⁿ(f)(i, i) > 0`. -/
def IsAperiodic (M : CMP A) (f : StationaryPolicy M) : Prop :=
  ∀ i, IsRecurrentState M f i →
    ∀ d : ℕ, (∀ n, 1 ≤ n → 0 < nstep M f n i i → d ∣ n) → d = 1

/-- The average cost optimality equation (5.1) for a signed cost `c` and admissible action sets
`U` on the transition law of `M`: for every `i`, the series are summable for `a ∈ U(i)` and
`ρ + h(i) = min_{a ∈ U(i)} {c(i, a) + ∑_j P(j | i, a) h(j)}`, the minimum being attained. -/
def ACOEWith (M : CMP A) (c : ℕ → A → ℝ) (U : ℕ → Set A) (ρ : ℝ) (h : ℕ → ℝ) : Prop :=
  ∀ i, (∀ a ∈ U i, Summable (fun j => prob M i a j * h j)) ∧
    (∃ a ∈ U i, ρ + h i = c i a + ∑' j, prob M i a j * h j) ∧
    (∀ a ∈ U i, ρ + h i ≤ c i a + ∑' j, prob M i a j * h j)

/-- Assumption 5.6 (p. 303), for the transition law of `M`: there is one `K > 0` such that for
every bounded measurable cost `c : S × A → ℝ` (signed) and every collection of nonempty compact
`U(i) ⊆ U_M(i)` on which `c(i, ·)` is continuous, the ACOE (5.1) has a bounded solution `(ρ, h)`
with `‖h‖ ≤ K ‖c‖` (sup norms). -/
def Assumption56 (M : CMP A) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ c : ℕ → A → ℝ, Measurable (fun p : ℕ × A => c p.1 p.2) →
    BddAbove (Set.range fun p : ℕ × A => |c p.1 p.2|) →
    ∀ U : ℕ → Set A, (∀ i, (U i).Nonempty ∧ IsCompact (U i) ∧ U i ⊆ M.U i ∧
      ContinuousOn (c i) (U i)) →
    ∃ ρ : ℝ, ∃ h : ℕ → ℝ, ACOEWith M c U ρ h ∧ BddAbove (Set.range fun i => |h i|) ∧
      ∀ i, |h i| ≤ K * ⨆ p : ℕ × A, |c p.1 p.2|

/-- `η` is the Cesàro limit of the rows `Pⁿ(f)(i, ·)` and is a probability vector (Assumption 5.7):
`η(j) = lim_N N⁻¹ ∑_{n<N} Pⁿ(f)(i, j)` for every `j`. -/
def IsCesaroLimit (M : CMP A) (f : StationaryPolicy M) (i : ℕ) (η : ℕ → ℝ) : Prop :=
  (∀ j, 0 ≤ η j) ∧ HasSum η 1 ∧ ∀ j,
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, nstep M f n i j) atTop (𝓝 (η j))

/-- Assumption 5.7 (p. 305): for each `f ∈ Π_SD` and `i ∈ S` the Cesàro limit
`η_i(f) ∈ 𝒫(S)` of `Pⁿ(f)(i, ·)` exists. -/
def Assumption57 (M : CMP A) : Prop :=
  ∀ (f : StationaryPolicy M) (i : ℕ), ∃ η : ℕ → ℝ, IsCesaroLimit M f i η

/-- Convergence `f_n → f` in `Π_SD` with the product topology: `f_n(k) → f(k)` for every `k`. -/
def PolicyTendsto (M : CMP A) (fs : ℕ → StationaryPolicy M) (f : StationaryPolicy M) : Prop :=
  ∀ k, Tendsto (fun n => (fs n).1 k) atTop (𝓝 (f.1 k))

/-- Assumption 5.8 (p. 305): `f ↦ η_i(f)` is continuous for every `i`, `Π_SD` carrying the product
topology and `𝒫(S)` the weak topology (sequential form; on the discrete `S` weak convergence of
probability vectors is pointwise convergence). -/
def Assumption58 (M : CMP A) : Prop :=
  ∀ i, ∀ η : StationaryPolicy M → ℕ → ℝ, (∀ f, IsCesaroLimit M f i (η f)) →
    ∀ (fs : ℕ → StationaryPolicy M) (f : StationaryPolicy M), PolicyTendsto M fs f →
      ∀ j, Tendsto (fun n => η (fs n) j) atTop (𝓝 (η f j))

/-- Assumption 5.9 (p. 305): the measures `η_i(f)` of Assumption 5.7 exist and, for each `i`,
`{η_i(f) : f ∈ Π_SD}` is tight. -/
def Assumption59 (M : CMP A) : Prop :=
  Assumption57 M ∧ ∀ i, ∀ η : StationaryPolicy M → ℕ → ℝ, (∀ f, IsCesaroLimit M f i (η f)) →
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ f, 1 - ε ≤ ∑ j ∈ Finset.range N, η f j

/-- Assumption 5.10 (p. 305): for each `f ∈ Π_SD` the chain is recurrent (every state is
recurrent). -/
def Assumption510 (M : CMP A) : Prop :=
  ∀ (f : StationaryPolicy M) (i : ℕ), IsRecurrentState M f i

/-- Assumption 5.11 (p. 305): for each `f ∈ Π_SD` the chain has no two disjoint invariant sets. -/
def Assumption511 (M : CMP A) : Prop :=
  ∀ f : StationaryPolicy M, NoTwoDisjointInvariant M f

/-- Assumption 5.12 (p. 305): `{P(f)(i, ·) : i ∈ S, f ∈ Π_SD}` is tight. -/
def Assumption512 (M : CMP A) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ (f : StationaryPolicy M) (i : ℕ),
    ENNReal.ofReal (1 - ε) ≤ M.P (i, f.1 i) (Set.Iio N)

/-- The killed `n`-step kernel `P̃ⁿ(f)(i, j)` of Assumption 5.13 (p. 306), the `n`-th power of
`P̃(f)(i, j) = P(f)(i, j)` for `j ≠ 0` and `0` for `j = 0`: the probability under `f` from `i` that
`X_1, …, X_n ≠ 0` and `X_n = j` (for `n = 0`, the identity). -/
noncomputable def killedPow (M : CMP A) (f : StationaryPolicy M) (n i j : ℕ) : ℝ≥0∞ :=
  pathMeasure M f.toPolicy i {ω | (∀ t, 1 ≤ t → t ≤ n → (ω t).1 ≠ 0) ∧ (ω n).1 = j}

/-- Assumption 5.13 (Lyapunov condition, p. 306): there is `w : S → ℝ₊` such that, for all `i`,
(i) `c(i, f(i)) + 1 + ∑_j P̃(f)(i, j) w(j) ≤ w(i)` for every `f ∈ Π_SD`;
(ii) `f ↦ ∑_j P(f)(i, j) w(j)` is continuous (product topology on `Π_SD`, sequential form);
(iii) `lim_n ∑_j P̃ⁿ(f)(i, j) w(j) = 0` for every `f ∈ Π_SD`.
Sums are computed in `[0, ∞]`. -/
def Assumption513 (M : CMP A) : Prop :=
  ∃ w : ℕ → ℝ, (∀ i, 0 ≤ w i) ∧
    (∀ (f : StationaryPolicy M) (i : ℕ),
      ENNReal.ofReal (M.c i (f.1 i)) + 1 + ∑' j, killedPow M f 1 i j * ENNReal.ofReal (w j) ≤
        ENNReal.ofReal (w i)) ∧
    (∀ i, ∀ (fs : ℕ → StationaryPolicy M) (f : StationaryPolicy M), PolicyTendsto M fs f →
      Tendsto (fun n => ∑' j, M.P (i, (fs n).1 i) {j} * ENNReal.ofReal (w j)) atTop
        (𝓝 (∑' j, M.P (i, f.1 i) {j} * ENNReal.ofReal (w j)))) ∧
    ∀ (f : StationaryPolicy M) (i : ℕ),
      Tendsto (fun n => ∑' j, killedPow M f n i j * ENNReal.ofReal (w j)) atTop (𝓝 0)

end ArapostathisAC.VanishingDiscount.Supplement


