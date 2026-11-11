-- Prove2me | Definitions.Def_KXorTPCA_Reduction_Reductions
-- name    : KXorTPCA_Reduction_Reductions
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:22:37.526132+00:00
-- url     : https://prove2.me/theorems/c478782f-99ea-40c7-92b8-c339b360b362
-- title:
--   Average-case reductions for detection and recovery, at fixed dimension and between problem sequences (Definitions C.4, C.5, C.6)
-- statement:
--   Let $P$ (dimension $n$) and $Q$ (dimension $n'$) be planted problems, $R$ a program (the reduction), and $d_{TV}$ the total variation distance $\sup_A|\mu(A)-\nu(A)|$. A **signal map** $\sigma$ gives the output secret $x'=\sigma(x,\omega)\in\{\pm1\}^{n'}$ as a function of the input secret $x$ and of the reduction's own tapes $\omega$.
--
--   **Definition C.4** (detection, fixed dimension). $R$ is an average-case reduction for detection with TV-error $\rho$ from $P$ to $Q$ if there is a signal map $\sigma$ with
--
--   $$d_{TV}\big(R(Y),Q^{\mathrm{NULL}}\big)\le\rho\ \ (Y\sim P^{\mathrm{NULL}}),\qquad d_{TV}\big(R(Y),Q_{x'}\big)\le\rho\ \ (Y\sim P_x,\ x'=\sigma(x,\cdot))\ \text{ for all }x.$$
--
--   **Definition C.5** (recovery, fixed dimension), with losses $\ell,\ell'$ (taken up to sign), thresholds $\ell^\star,\ell'^\star$ and a loss map $f$: (1) for every $x$, the pair $(R(Y),\sigma(x,\omega))$ with $Y\sim P_x$ is within $\rho$ in total variation of $(Z,x')$ with $x'=\sigma(x,\cdot)$ and $Z\sim Q_{x'}$; (2) $f(t)\le\ell^\star$ for $t\in[0,\ell'^\star]$, and there is a program $\mathrm{Rec}$ (it receives $Y$, an estimate $\hat x'$ of $x'$, and the reduction's tapes together with fresh ones) such that for every program $B$, every $t\in[0,\ell'^\star]$ and every $x$:
--
--   $$\mathbb P\big[\ell(x,\mathrm{Rec}(Y,B(R(Y))))\le f(t)\big]\ \ge\ \inf_{x'}\mathbb P_{Z\sim Q_{x'}}\big[\ell'(x',B(Z))\le t\big]-\rho .$$
--
--   **Definition C.6** (sequences). For families $P,Q$ and parameter points $p,q$: polynomial-time programs $R$, $\mathrm{Rec}$ form an average-case reduction for detection and recovery from $P$ at $p$ to $Q$ at $q$ if there is $c>0$ such that for every parameter sequence $p_i\to p$ there are parameter sequences $q_i\to q$, dimensions $n_i\to\infty$ and $n'_i$ with $\log n'_i/\log n_i\to c$, an index $i_0$ and TV-errors $\varepsilon_i\to0$ such that for all $i>i_0$, through one signal map, $R$ is a detection reduction and $(R,\mathrm{Rec})$ a recovery reduction from $P_{p_i}(n_i)$ to $Q_{q_i}(n'_i)$ with TV-error $\varepsilon_i$, for both standard losses (exact and overlap) with $f(t)=t+\varepsilon_i$. Optional conditions restrict the dimensions (e.g. $n'_i=n_i$) and the signal map (e.g. $x'=x[1:n']$; with $n'=n$ this is "preserves the secret signal vector precisely"). **Computational equivalence** means reductions in both directions.
--
--   **Formalization Note** The output of a reduction is its whole final memory; laws are push-forwards of the tape law, and $d_{TV}$ is the published `MarkovChainCLT.tvDist`. Definition C.4 allows $x'$ to be random (drawn by the reduction): Lemma 6.4's reduction has $x'=x^{\otimes a}\odot y$ for a $y$ it draws; a deterministic $x'$ is the special case. Definition C.5(2) prints "if $\ell'(x',\hat x')\le\delta_{n'}\le\ell'^\star$ then $\sup_x\mathbb E\,\ell(x,A_{rec}(Y,\hat x'))\le f(\delta_{n'})\le\ell^\star$" without saying how $\hat x'$ arises; it is read as the transfer, for every program $B$ producing $\hat x'$, of the success probability at each threshold, which is how Lemma C.2 and §C.4 use it. "$n'_i=n_i^c$" is read as $\log n'_i/\log n_i\to c$ (Lemma 8.1 has $n'=n(1-o(1))$). Detection and recovery use the same sequences and the same signal map.
-- source:
--   G. Bresler, A. Harbuzova, Average-Case Reductions for k-XOR and Tensor PCA, arXiv:2601.19016 (copy sha256 6ec029a7…), pp. 96–98 (PDF 99–101), Definitions C.4, C.5, C.6, footnotes 45, 46; pp. 99–102 (PDF 102–105), §C.4

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_KXorTPCA_Reduction_Tasks

set_option autoImplicit false

open Filter Topology MeasureTheory

/-!
# Average-case reductions (Definitions C.4, C.5, C.6)

G. Bresler, A. Harbuzova, *Average-Case Reductions for k-XOR and Tensor PCA*, arXiv:2601.19016
(copy sha256 6ec029a7…), §C.3, pp. 96–98; §C.4, pp. 99–102.

A reduction is a program `R`; its output on input `Y` is its whole final memory (`outMem`).
The total variation distance is the published `MarkovChainCLT.tvDist`
(`sup_A |μ(A) − ν(A)|` over measurable `A`), applied to push-forwards of the tape law.

**Signal maps.** A reduction maps an instance with secret `x ∈ {±1}ⁿ` to one with secret
`x′ ∈ {±1}^{n′}`; `σ x ω` is that `x′`, allowed to depend on the reduction's own tapes `ω`
(Lemma 6.4: `x′ = x^{⊗a} ⊙ y` for a `y` drawn by the reduction). The planted clause of
Definition C.4 compares the output with the law of `Q_{x′}` for `x′ = σ x ω` drawn independently
(for a deterministic `σ` this is `Q_{x′}` itself). Definition C.5 compares the output paired
with `x′` (the signal written in the negative cells, `withSig`) with `(Q_{x′}, x′)`.

**Recovery map (reading of Definition C.5(2)).** `Rec` receives the input instance `Y` with an
estimate `x̂′` of `x′` in cells `−1, …, −n′`, and runs on the reduction's tapes interleaved with
fresh tapes (so the reduction's randomness, e.g. the `y` of Lemma 6.4, is known to it). For every
program `B` producing `x̂′` on `Q` and every threshold `t ∈ [0, ℓ′⋆]`: the probability that
`Rec(Y, B(R(Y)))` has loss `≤ f(t)` against `x` is at least the worst-case (over `x′`) probability
that `B` has loss `≤ t` on `Q_{x′}`, minus the TV-error; and `f(t) ≤ ℓ⋆`.
-/

namespace KXorTPCA.Reduction

/-- A signal map: the output secret `x′` as a function of the input secret and of the
reduction's tapes. -/
abbrev SigMap (n n' : ℕ) := Signal n → Tapes → Signal n'

/-- Definition C.4 at fixed dimensions, with signal map `σ`: `R` is an average-case reduction for
detection with TV-error `ρ` from `P` to `Q`:
`d_TV(R(Y), Q^NULL) ≤ ρ` for `Y ∼ P^NULL`, and for every `x`, `d_TV(R(Y), Q_{x′}) ≤ ρ` for
`Y ∼ P_x`, `x′ = σ x ·`. -/
def IsDetReductionWith {n n' : ℕ} (R : Program) (P : Task n) (Q : Task n') (ρ : ℝ)
    (σ : SigMap n n') : Prop :=
  MarkovChainCLT.tvDist (lawOf2 fun ωi ωr => outMem R (P.null ωi) ωr)
      (lawOf2 fun _ ω₂ => Q.null ω₂) ≤ ρ ∧
  ∀ x : Signal n,
    MarkovChainCLT.tvDist (lawOf2 fun ωi ωr => outMem R (P.planted x ωi) ωr)
      (lawOf2 fun ω₁ ω₂ => Q.planted (σ x ω₁) ω₂) ≤ ρ

/-- Definition C.4 at fixed dimensions: for all `x` there is some (possibly random) `x′`. -/
def IsDetReduction {n n' : ℕ} (R : Program) (P : Task n) (Q : Task n') (ρ : ℝ) : Prop :=
  ∃ σ : SigMap n n', IsDetReductionWith R P Q ρ σ

/-- The estimate `x̂ ∈ {±1}ⁿ` of the composite: `R` on `Y = P_x(w 0)` with tapes `w 1`, then `B`
on the output with tapes `w 2`, then `Rec` on `(Y, x̂′)` with tapes `w 1` interleaved with
`w 3`. -/
noncomputable def compositeEstimate {n n' : ℕ} (R Rec B : Program) (P : Task n) (x : Signal n)
    (w : Fin 4 → Tapes) : Signal n :=
  outVec Rec n (withSig (P.planted x (w 0)) (outVec B n' (outMem R (P.planted x (w 0)) (w 1)) (w 2)))
    (mixTapes (w 1) (w 3))

/-- Definition C.5 at fixed dimensions (with the reading of clause 2 in the module docstring):
`(R, Rec)` is an average-case reduction for recovery with TV-error `ρ` from `P` to `Q`, signal
map `σ`, losses `ℓ`, `ℓ′`, thresholds `ℓ⋆`, `ℓ′⋆` and loss map `f`; losses are taken up to
global sign. -/
def IsRecReduction {n n' : ℕ} (R Rec : Program) (P : Task n) (Q : Task n') (ρ : ℝ)
    (σ : SigMap n n') (ℓ : Signal n → Signal n → ℝ) (ℓ' : Signal n' → Signal n' → ℝ)
    (ℓstar ℓ'star : ℝ) (f : ℝ → ℝ) : Prop :=
  (∀ x : Signal n,
    MarkovChainCLT.tvDist (lawOf2 fun ωi ωr => withSig (outMem R (P.planted x ωi) ωr) (σ x ωr))
      (lawOf2 fun ω₁ ω₂ => withSig (Q.planted (σ x ω₁) ω₂) (σ x ω₁)) ≤ ρ) ∧
  (∀ t : ℝ, 0 ≤ t → t ≤ ℓ'star → f t ≤ ℓstar) ∧
  ∀ (B : Program) (t : ℝ), 0 ≤ t → t ≤ ℓ'star → ∀ x : Signal n,
    (⨅ x' : Signal n', prob2 (fun ω₁ ω₂ => upToSign ℓ' x' (outVec B n' (Q.planted x' ω₁) ω₂) ≤ t))
        - ρ ≤
      probOver 4 (fun w => upToSign ℓ x (compositeEstimate (n' := n') R Rec B P x w) ≤ f t)

/-- A condition on the dimension sequences `(n_i)`, `(n′_i)` of a reduction. -/
abbrev DimSpec := (ℕ → ℕ) → (ℕ → ℕ) → Prop

/-- A condition on the signal map of a reduction at dimensions `n → n′`. -/
abbrev SigSpec := (n n' : ℕ) → SigMap n n' → Prop

/-- No condition on the dimensions. -/
def anyDims : DimSpec := fun _ _ => True

/-- The dimension is kept: `n′_i = n_i`. -/
def sameDims : DimSpec := fun ns n's => ∀ i, n's i = ns i

/-- No condition on the signal map. -/
def anySig : SigSpec := fun _ _ _ => True

/-- `x′ = x[1:n′]`, the first `n′` coordinates of `x` (with `sameDims`: `x′ = x`, the secret
signal vector is preserved precisely). -/
def prefixSig : SigSpec := fun n n' σ =>
  ∀ (x : Signal n) (ω : Tapes) (i : Fin n'), ∃ h : (i : ℕ) < n, σ x ω i = x ⟨i, h⟩

/-- Definition C.6 (reductions between problem sequences), for both detection and recovery, with
one program `R` and one recovery map `Rec`, both polynomial-time: there is a constant `c > 0` such
that for every parameter sequence `p_i → p` there are parameter sequences `q_i → q`, dimensions
`n_i → ∞` and `n′_i` with `log n′_i / log n_i → c` (`n′ = n^c`), an index `i₀` and TV-errors
`ε_i → 0` such that for every `i > i₀`, `R` is a detection reduction (Definition C.4) and
`(R, Rec)` a recovery reduction (Definition C.5) from `P_{p_i}(n_i)` to `Q_{q_i}(n′_i)` with
TV-error `ε_i`, for both standard losses (exact: `1_{x ≠ x̂}`; weak/strong: `1 − ⟨x, x̂⟩/n`) with
the loss map `t ↦ t + ε_i` (§C.4), through one signal map satisfying `sigs`; the dimension
sequences satisfy `dims`. -/
def IsAvgReduction (R Rec : Program) (P : Family) (p : ℝ × ℝ) (Q : Family) (q : ℝ × ℝ)
    (dims : DimSpec) (sigs : SigSpec) : Prop :=
  PolyTime R ∧ PolyTime Rec ∧ ∃ c : ℝ, 0 < c ∧
  ∀ ps : ℕ → ℝ × ℝ, Tendsto ps atTop (𝓝 p) →
    ∃ (qs : ℕ → ℝ × ℝ) (ns n's : ℕ → ℕ) (i₀ : ℕ) (ε : ℕ → ℝ),
      Tendsto qs atTop (𝓝 q) ∧ Tendsto ns atTop atTop ∧ Tendsto ε atTop (𝓝 0) ∧
      Tendsto (fun i => Real.log (n's i) / Real.log (ns i)) atTop (𝓝 c) ∧ dims ns n's ∧
      ∀ i, i₀ < i → ∃ σ : SigMap (ns i) (n's i), sigs (ns i) (n's i) σ ∧
        IsDetReductionWith R (P (ps i).1 (ps i).2 (ns i)) (Q (qs i).1 (qs i).2 (n's i)) (ε i) σ ∧
        IsRecReduction R Rec (P (ps i).1 (ps i).2 (ns i)) (Q (qs i).1 (qs i).2 (n's i)) (ε i) σ
          lossExact lossExact (1 + ε i) 1 (fun t => t + ε i) ∧
        IsRecReduction R Rec (P (ps i).1 (ps i).2 (ns i)) (Q (qs i).1 (qs i).2 (n's i)) (ε i) σ
          lossOverlap lossOverlap (1 + ε i) 1 (fun t => t + ε i)

/-- There is a polynomial-time average-case reduction for both detection and recovery
(Definition C.6) from `P` at `p` to `Q` at `q`. -/
def AvgReduces (P : Family) (p : ℝ × ℝ) (Q : Family) (q : ℝ × ℝ) (dims : DimSpec)
    (sigs : SigSpec) : Prop :=
  ∃ R Rec : Program, IsAvgReduction R Rec P p Q q dims sigs

/-- Computational equivalence: polynomial-time average-case reductions for both detection and
recovery in both directions. -/
def CompEquiv (P : Family) (p : ℝ × ℝ) (Q : Family) (q : ℝ × ℝ) (dims : DimSpec)
    (sigs : SigSpec) : Prop :=
  AvgReduces P p Q q dims sigs ∧ AvgReduces Q q P p dims sigs

end KXorTPCA.Reduction


