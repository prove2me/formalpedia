-- Prove2me | Definitions.Def_FourierDimTesting102_Quantum_Supplement_Model
-- name    : FourierDimTesting102_Quantum_Supplement_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T03:25:53.62769+00:00
-- url     : https://prove2.me/theorems/8f629e1b-10c3-4baa-b4eb-5694ec825eb6
-- title:
--   Uniform probabilities, nonadaptive classical testers, and the notation of Definition 6.1
-- statement:
--   This file adds the probabilistic language of §§4–6 to the base model of the mission (the space $V_n=\mathbb F_2^n$, boolean functions $f$, Fourier coefficients $\widehat f(s)$, the class $D_k$ and the distance $\operatorname{dist}$).
--
--   1. For a finite set $A$, $\Pr_a[E(a)]$ and $\mathbb E_a[Z(a)]$ denote the probability and the mean for $a$ uniform on $A$.
--   2. A **nonadaptive randomized classical query algorithm** draws a uniform seed $r$ from a finite set, queries $f$ at points $x_q(r)$ for every index $q$ of a finite index set $Q$, and outputs a bit computed from $r$ and the answers $f(x_q(r))$. Its number of queries is $|Q|$, on every run.
--   3. A **probability distribution** on $\mathbb F_2^n$ is a function $\mu\ge0$ with $\sum_s\mu(s)=1$; the Fourier distribution is $\mu_f(s)=\widehat f(s)^2$.
--   4. For a linear map $X:\mathbb F_2^n\to\mathbb F_2^r$ (an $r\times n$ matrix over $\mathbb F_2$), the pushforward is $\mu_X(t)=\sum_{s:Xs=t}\mu(s)$.
--   5. For a subspace $W$, $\mu(\overline W)=\sum_{s\notin W}\mu(s)$, and
--
--   $$
--   \rho_k(\mu)=\min_{\dim W\le k}\mu(\overline W),\qquad \rho_{k,X}(\mu)=\rho_k(\mu_X).
--   $$
--
--   6. For a list of samples $s_1,\dots,s_M$, the estimate is $\tilde\rho_k=\frac1M\min_{\dim W\le k}|\{i:s_i\notin W\}|$, and $\tilde\rho_{k,X}$ is the same estimate computed from $Xs_1,\dots,Xs_M$.
--   7. $\Pr[E(s_1,\dots,s_M)]$ for independent samples from $\mu$ (with replacement) is $\sum_{s}\prod_i\mu(s_i)\,\mathbf 1[E(s)]$.
--
--   These are the objects in which Lemmas 6.1–6.2 and Theorem 6.1 are stated, and the classical query model of Theorems 4.1 and 6.2.
--
--   **Formalization Note** Every probability is an exact finite sum; nothing is defined by the inequality it should satisfy. The minima are infima of finitely many values over a nonempty set (the zero subspace has dimension $0$), and the file proves they are attained. A linear map is a matrix, so the uniform law on matrices is the uniform random linear map, singular maps included.
-- source:
--   Kenny Chen, Exponential Quantum Advantage in Testing Fourier Dimensionality, September 2026 STOC 2027 submission #102 preprint, source.pdf SHA-256 afe3d00f3d3887de87812ce319a69c1fca5c95912047974553110aa755de4298, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/102.pdf, p.12 §2.2 (classical query access), p.19 Algorithm 2, p.27 Definition 6.1, p.28 Lemmas 6.1–6.2

import Definitions.Def_FourierDimTesting102_Quantum_Algorithm

/-!
# Supplement: uniform probabilities, nonadaptive classical testers and the notation of §6

Kenny Chen, *Exponential Quantum Advantage in Testing Fourier Dimensionality*, September 2026
STOC 2027 submission #102 preprint, §2.2 (p.12), Algorithm 2 (p.19), Definition 6.1 (p.27),
Lemmas 6.1–6.2 (p.28).

Every probability below is an exact finite average over a uniform seed, or an exact finite sum
weighted by an arbitrary distribution `μ`; nothing is defined by the inequality it is meant to
satisfy. The base model (`V`, `BoolFn`, `coeff`, `Dk`, `distToSet`, …) is reused unchanged.
-/

namespace FourierDimTesting102.Quantum.Supplement

open QAlgorithms FourierDimTesting102.Quantum

/-! ### Uniform probabilities -/

open Classical in
/-- `Pr_a[E(a)]` for `a` uniform on the finite type `α`. -/
noncomputable def unifProb {α : Type*} [Fintype α] (E : α → Prop) : ℝ :=
  ((Finset.univ.filter E).card : ℝ) / Fintype.card α

/-- `E_a[Z(a)]` for `a` uniform on the finite type `α`. -/
noncomputable def unifMean {α : Type*} [Fintype α] (Z : α → ℝ) : ℝ :=
  (Fintype.card α : ℝ)⁻¹ * ∑ a, Z a

/-! ### Nonadaptive randomized classical query algorithms -/

/-- §2.2, p.12 ("classical testers may query a point `x`, and in return obtain the value
`f(x)`"): a nonadaptive randomized classical query algorithm on `n`-bit inputs. It draws a seed
`r` uniformly from the finite type `R`, queries `f` at the points `pts r q` for every query index
`q : Q`, and outputs `dec r a` from the seed and the vector `a` of answers. The function `f`
reaches the output only through the answers. -/
structure NonadaptiveRandAlg (n : ℕ) (R Q : Type) where
  /-- The query points chosen from the seed. -/
  pts : R → Q → V n
  /-- The output, computed from the seed and the answers `a q = f (pts r q)`. -/
  dec : R → (Q → Bool) → Bool

namespace NonadaptiveRandAlg

variable {n : ℕ} {R Q : Type}

/-- The probability, over the uniform seed, that the algorithm outputs `b` on input `f`. -/
noncomputable def outProb [Fintype R] (A : NonadaptiveRandAlg n R Q) (f : BoolFn n) (b : Bool) :
    ℝ :=
  unifProb fun r : R => A.dec r (fun q => f (A.pts r q)) = b

/-- The number of oracle queries, the same on every run: one per query index. -/
def queries [Fintype Q] (_A : NonadaptiveRandAlg n R Q) : ℕ := Fintype.card Q

end NonadaptiveRandAlg

/-! ### Definition 6.1: distributions on `F₂ⁿ`, pushforward and minimum outside mass -/

/-- Definition 6.1 (1), p.27: `μ` is a probability distribution on `F₂ⁿ` (point masses and zero
weights allowed). -/
def IsProbDist {n : ℕ} (μ : V n → ℝ) : Prop :=
  (∀ s, 0 ≤ μ s) ∧ ∑ s, μ s = 1

/-- Definition 6.1 (1), p.27: the Fourier distribution `μ_f(s) = f̂(s)²`. -/
noncomputable def fourierDist {n : ℕ} (f : BoolFn n) : V n → ℝ := fun s => coeff f s ^ 2

/-- A linear map `X : F₂ⁿ → F₂ʳ`, as an `r × n` matrix over `F₂`; the uniform law on this type is
the uniform random linear map of §6 (independent uniform entries; singular maps included). -/
abbrev LinMap (n r : ℕ) := Matrix (Fin r) (Fin n) (ZMod 2)

open Classical in
/-- Definition 6.1 (2), p.27: the pushforward `μ_X(t) = ∑_{s : Xs = t} μ(s)`. -/
noncomputable def pushforward {n r : ℕ} (μ : V n → ℝ) (X : LinMap n r) : V r → ℝ :=
  fun t => ∑ s ∈ Finset.univ.filter (fun s => X.mulVec s = t), μ s

open Classical in
/-- The mass `μ(W̄) = ∑_{s ∉ W} μ(s)` outside a linear subspace `W`. -/
noncomputable def massOut {n : ℕ} (μ : V n → ℝ) (W : Submodule (ZMod 2) (V n)) : ℝ :=
  ∑ s ∈ Finset.univ.filter (fun s => s ∉ W), μ s

/-- The linear subspaces of `F₂ⁿ` of dimension at most `k`. -/
def subDimLe (n k : ℕ) : Set (Submodule (ZMod 2) (V n)) :=
  {W | Module.finrank (ZMod 2) W ≤ k}

/-- Definition 6.1 (3), p.27: `ρ_k(μ) = min_{dim W ≤ k} μ(W̄)`, the smallest of finitely many
values over a nonempty set (`⊥` belongs to it), so a genuine minimum (`exists_massOut_eq_rhoK`). -/
noncomputable def rhoK {n : ℕ} (k : ℕ) (μ : V n → ℝ) : ℝ :=
  sInf (massOut μ '' subDimLe n k)

/-- Definition 6.1 (3), p.27: `ρ_{k,X}(μ) = ρ_k(μ_X)`, the minimum over subspaces of `F₂ʳ`. -/
noncomputable def rhoKX {n r : ℕ} (k : ℕ) (μ : V n → ℝ) (X : LinMap n r) : ℝ :=
  rhoK k (pushforward μ X)

open Classical in
/-- `|{i : s_i ∉ W}|`, the number of sample indices outside `W`, counted with multiplicity. -/
noncomputable def outCount {n M : ℕ} (W : Submodule (ZMod 2) (V n)) (s : Fin M → V n) : ℕ :=
  (Finset.univ.filter fun i => s i ∉ W).card

/-- Lemma 6.1, p.28: the estimate `ρ̃_k = (1/M) min_{dim W ≤ k} |{i : s_i ∉ W}|` from the sample
list `s₁, …, s_M` (a genuine minimum, `exists_outCount_eq_rhoTilde`). -/
noncomputable def rhoTilde {n M : ℕ} (k : ℕ) (s : Fin M → V n) : ℝ :=
  sInf ((fun W => (outCount W s : ℝ)) '' subDimLe n k) / M

/-- Lemma 6.2, p.28: the compressed samples `X s₁, …, X s_M`; `ρ̃_{k,X} = rhoTilde k (compress X s)`. -/
def compress {n r M : ℕ} (X : LinMap n r) (s : Fin M → V n) : Fin M → V r :=
  fun i => X.mulVec (s i)

open Classical in
/-- `Pr[E(s₁, …, s_M)]` for `M` independent samples from `μ` (with replacement). -/
noncomputable def sampleProb {n : ℕ} (μ : V n → ℝ) (M : ℕ) (E : (Fin M → V n) → Prop) : ℝ :=
  ∑ s : Fin M → V n, (∏ i, μ (s i)) * if E s then 1 else 0

/-! ### Structural facts: the minima are attained -/

theorem bot_mem_subDimLe (n k : ℕ) : (⊥ : Submodule (ZMod 2) (V n)) ∈ subDimLe n k := by
  simp [subDimLe]

theorem exists_massOut_eq_rhoK {n : ℕ} (k : ℕ) (μ : V n → ℝ) :
    ∃ W ∈ subDimLe n k, massOut μ W = rhoK k μ := by
  have hne : (subDimLe n k).Nonempty := ⟨⊥, bot_mem_subDimLe n k⟩
  exact (hne.image (massOut μ)).csInf_mem ((Set.toFinite _).image _)

theorem exists_outCount_eq_rhoTilde {n M : ℕ} (k : ℕ) (s : Fin M → V n) :
    ∃ W ∈ subDimLe n k,
      (outCount W s : ℝ) = sInf ((fun W => (outCount W s : ℝ)) '' subDimLe n k) := by
  have hne : (subDimLe n k).Nonempty := ⟨⊥, bot_mem_subDimLe n k⟩
  exact (hne.image _).csInf_mem ((Set.toFinite _).image _)

end FourierDimTesting102.Quantum.Supplement


