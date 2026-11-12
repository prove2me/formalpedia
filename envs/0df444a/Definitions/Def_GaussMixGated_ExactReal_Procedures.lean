-- Prove2me | Definitions.Def_GaussMixGated_ExactReal_Procedures
-- name    : GaussMixGated_ExactReal_Procedures
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T15:25:16.732455+00:00
-- url     : https://prove2.me/theorems/123261cc-028c-431e-a153-53a830973dc2
-- title:
--   Input/output conventions of the dictionary (Theorem 2.1) and fitting (Theorem 2.2) procedures
-- statement:
--   The dictionary construction of Theorem 2.1 starts with $d,k,m,\sigma,r,\theta,\delta'$ and the $md$ center coordinates in memory, and has one channel returning draws from $P_\sigma$. At its halt it outputs a description (cells $0,\dots,\ell-1$, $\ell$ in pointer register $0$), a feature dimension $N$ (pointer register $1$) and a norm bound $L_z$ (real register $0$). A fixed **feature evaluator** program receives the description and a point $x\in\mathbb R^d$ and leaves $z_0(x),\dots,z_{N-1}(x)$ in memory cells $0,\dots,N-1$.
--
--   The fitting procedure of Theorem 2.2 starts with $N,L_z,a,\delta'$ in memory and has two channels: $z(X)$ for fresh $X\sim Q$ and $z(X)$ for fresh $X\sim P'$. At its halt the cells $iN+j$ hold the fitted matrix $C$, and the numerator is
--
--   $$f(x)=\kappa+z(x)^{\top}Cz(x).$$
--
--   These conventions make the two theorems statements about one machine model.
-- source:
--   Zheng, Xie, He, Learning Finite Gaussian Location Mixtures via Gated Moments and Posterior Covers, STOC 2027 submission #36 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/36.pdf, PDF p. 6, Theorems 2.1 and 2.2

import Mathlib
import Definitions.Def_GaussMixGated_ExactReal_Machine

open MeasureTheory ProbabilityTheory

noncomputable section

namespace GaussMixGated.ExactReal

/-!
# Input and output conventions of the dictionary and fitting procedures
(Zheng–Xie–He, STOC 2027 #36, Theorems 2.1 and 2.2, PDF p. 6)
-/

/-- The quadratic form `zᵀ S z` of an `N × N` matrix and a vector given as a sequence. -/
def matQuad {N : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) (z : ℕ → ℝ) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N, S i j * z i * z j

/-- The coordinates of the centers `c_1, …, c_m ∈ ℝ^d`, center by center. -/
def centersList {d m : ℕ} (c : Fin m → EuclideanSpace ℝ (Fin d)) : List ℝ :=
  (List.finRange m).flatMap (fun j => (List.finRange d).map (fun i => c j i))

/-- The dictionary construction's initial configuration (Theorem 2.1): cells `0–6` hold
`d, k, m, σ, r, θ, δ′`, followed by the `m d` center coordinates; pointer registers `0, 1, 2` hold
`d, k, m`. -/
def dictionaryStart {d m : ℕ} (k : ℕ) (c : Fin m → EuclideanSpace ℝ (Fin d)) (σ r θ δ' : ℝ) :
    State :=
  initState (listMem ([(d : ℝ), (k : ℝ), (m : ℝ), σ, r, θ, δ'] ++ centersList c))
    (listPtrs [(d : ℤ), (k : ℤ), (m : ℤ)])

/-- The dictionary construction's environment: Gaussian tape `g` and channel `0` returning the
draws `xs t` (from `P_σ`). -/
def dictionaryEnv {d : ℕ} (xs : ℕ → EuclideanSpace ℝ (Fin d)) (g : ℕ → ℝ) : Env :=
  ⟨g, [obsChannel xs]⟩

/-- The feature dimension `N` output by a construction: pointer register `1` at the halt. -/
def featureDim (s : State) : ℕ := (s.ptrs 1).toNat

/-- The feature norm bound `L_z` output by a construction: real register `0` at the halt. -/
def featureBound (s : State) : ℝ := s.regs 0

/-- The feature evaluator's initial configuration: description `D` in cells `0, …`, the point
`x` in cells `−1, …, −d`, pointer register `0` holding `d`. -/
def featureStart (D : List ℝ) {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) : State :=
  initState (withPoint (listMem D) (fun i => x i)) (listPtrs [(d : ℤ)])

/-- The feature vector `z(x)` computed by the evaluator `Ev` on description `D`: memory cell `i`
at the halt is `z_i(x)` (`i < N`). The evaluator draws no Gaussian, so the tape is irrelevant. -/
def featureValue (Ev : Program) (D : List ℝ) {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) : ℕ → ℝ :=
  fun i => (final Ev (samplerEnv (fun _ => 0)) (featureStart D x)).mem i

/-- The feature-oracle channel of Theorem 2.2: the `t`-th call writes `z(X_t)` (`N` cells) for
the `t`-th entry `X_t` of its tape. -/
def featureChannel {d N : ℕ} (z : EuclideanSpace ℝ (Fin d) → Fin N → ℝ)
    (xs : ℕ → EuclideanSpace ℝ (Fin d)) : Channel :=
  ⟨0, N, 0, fun t _ i => if h : i < N then z (xs t) ⟨i, h⟩ else 0⟩

/-- The fitting procedure's initial configuration (Theorem 2.2): cells `0–3` hold `N, L_z, a, δ′`;
pointer register `0` holds `N`. -/
def fitStart (N : ℕ) (Lz a δ' : ℝ) : State :=
  initState (listMem [(N : ℝ), Lz, a, δ']) (listPtrs [(N : ℤ)])

/-- The fitting procedure's environment: Gaussian tape `g`, channel `0` = `z(X)` for fresh
`X ∼ Q` (tape `xq`), channel `1` = `z(X)` for fresh `X ∼ P′` (tape `xp`). -/
def fitEnv {d N : ℕ} (z : EuclideanSpace ℝ (Fin d) → Fin N → ℝ)
    (xq xp : ℕ → EuclideanSpace ℝ (Fin d)) (g : ℕ → ℝ) : Env :=
  ⟨g, [featureChannel z xq, featureChannel z xp]⟩

/-- The fitted matrix `C` read from memory at the halt: `C_{ij}` in cell `i N + j`. -/
def fitMatrix (N : ℕ) (s : State) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => s.mem ((i : ℕ) * N + j)

/-- The fitted numerator `f(x) = κ + z(x)ᵀ C z(x)`. -/
def fitNumerator {d N : ℕ} (κ : ℝ) (C : Matrix (Fin N) (Fin N) ℝ)
    (z : EuclideanSpace ℝ (Fin d) → Fin N → ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  κ + ∑ i, ∑ j, C i j * z x i * z x j

end GaussMixGated.ExactReal


