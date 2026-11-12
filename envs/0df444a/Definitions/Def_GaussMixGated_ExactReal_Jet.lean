-- Prove2me | Definitions.Def_GaussMixGated_ExactReal_Jet
-- name    : GaussMixGated_ExactReal_Jet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T15:24:15.823414+00:00
-- url     : https://prove2.me/theorems/d207bd74-c3d9-4e25-92b5-c7096ad3007a
-- title:
--   Polynomial maps, jets $J_F$, the moment $M(u)$, the sketch (16) and the eight-sketch gate
-- statement:
--   Points of $\mathbb R^n$ are real $n$-vectors. A **polynomial map** $F:\mathbb R^n\to\mathbb R^r$ of degree at most $q$ is given by $r$ real polynomials in $n$ variables of total degree at most $q$. For $v>0$ define
--
--   $$J_F(x)=\sum_{h=0}^{q}\frac{v^h}{h!}\,\|D^hF(x)\|_F^2,\qquad M(u)=\mathbb E\,\|F(u+\sqrt v\,G)\|^2,\quad G\sim N(0,I_n),$$
--
--   where $\|D^hF(x)\|_F^2$ is the sum of the squared entries $\partial^hF_j/\partial x_{i_1}\cdots\partial x_{i_h}(x)$ over all output coordinates $j$ and all $h$-tuples $(i_1,\dots,i_h)$: the Frobenius (Hilbert–Schmidt) norm, not the operator norm.
--
--   For independent $g_1,\dots,g_q\sim N(0,I_n)$ and $\gamma_1,\dots,\gamma_q\sim N(0,1)$ the **sketch** (16) is
--
--   $$W(x)=\sum_{h=0}^{q}\frac{v^{h/2}}{\sqrt{h!}}\,D^hF(x)[g_1,\dots,g_h]\prod_{\ell=h+1}^{q}\gamma_\ell .$$
--
--   The **gate** with threshold $T$ takes eight independent sketches and accepts $x$ when every $\|W_r(x)\|^2\le T$; $\alpha(u)$ is its acceptance probability for a gate input $A\sim N(u,vI_n)$ independent of the sketches. $K_q=3^{8q}e^{12q}$.
--
--   For §3.1, a latent atom index $I$ with $\mathbb P(I=i)=w_i$, gate-side noise $G_A$, query-side noise $G_B$, prior-history randomness $R_0$ and the sketches are independent; the gate input is $A=u_I+\sqrt vG_A$ and the query is $B=u_I+\sqrt vG_B$. For a prior history $H_0(A,R_0)$, $a_1(u)$ is the probability that $H_0$ and the appended gate both accept when $A\sim N(u,vI_n)$.
--
--   These objects are used by Lemma 3.1, Lemma 3.2 and Corollary 3.3.
-- source:
--   Zheng, Xie, He, Learning Finite Gaussian Location Mixtures via Gated Moments and Posterior Covers, STOC 2027 submission #36 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/36.pdf, PDF p. 8–9, §3.1 and §3.2 (definitions of J_F, M); PDF p. 9, (16); PDF p. 10, Lemma 3.2

import Mathlib

open MeasureTheory ProbabilityTheory

noncomputable section

namespace GaussMixGated.ExactReal

/-!
# Full-jet gates (Zheng–Xie–He, STOC 2027 #36, §3, PDF pp. 8–11)

Points of `ℝ^n` are functions `Fin n → ℝ`; `sqNorm` is the squared Euclidean norm.
A polynomial map `F : ℝ^n → ℝ^r` of degree at most `q` is a list of `r` real polynomials in `n`
variables of total degree at most `q`. `‖D^h F(x)‖_F` is the Frobenius (Hilbert–Schmidt) norm of
the `h`-th derivative: the root of the sum, over the output coordinate and over all `h`-tuples of
input coordinates, of the squared entries `∂^h F_j / ∂x_{i_1} ⋯ ∂x_{i_h}`. It is not the operator
norm.
-/

/-- The squared Euclidean norm of a finite real vector. -/
def sqNorm {n : ℕ} (y : Fin n → ℝ) : ℝ := ∑ j, y j ^ 2

/-- A polynomial map `ℝ^n → ℝ^r`: its `r` coordinate polynomials. -/
abbrev PolyMap (n r : ℕ) := Fin r → MvPolynomial (Fin n) ℝ

/-- Every coordinate polynomial has total degree at most `q`. -/
def PolyMap.DegLE {n r : ℕ} (F : PolyMap n r) (q : ℕ) : Prop := ∀ j, (F j).totalDegree ≤ q

/-- Evaluation `F(x)`. -/
def PolyMap.eval {n r : ℕ} (F : PolyMap n r) (x : Fin n → ℝ) : Fin r → ℝ :=
  fun j => MvPolynomial.eval x (F j)

/-- `D^h F_j(x)[y_1, …, y_h]`. -/
def derivApply {n r : ℕ} (F : PolyMap n r) (h : ℕ) (x : Fin n → ℝ) (j : Fin r)
    (y : Fin h → Fin n → ℝ) : ℝ :=
  iteratedFDeriv ℝ h (fun z => MvPolynomial.eval z (F j)) x y

/-- `‖D^h F(x)‖_F²`: the sum of the squared entries `D^h F_j(x)[e_{i_1}, …, e_{i_h}]`. -/
def frobSq {n r : ℕ} (F : PolyMap n r) (h : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∑ j, ∑ i : Fin h → Fin n, derivApply F h x j (fun l => Pi.single (i l) 1) ^ 2

/-- The jet `J_F(x) = ∑_{h=0}^{q} (v^h / h!) ‖D^h F(x)‖_F²` (§3.2). -/
def jet {n r : ℕ} (F : PolyMap n r) (q : ℕ) (v : ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ h ∈ Finset.range (q + 1), v ^ h / (h.factorial : ℝ) * frobSq F h x

/-- The standard Gaussian `N(0, I_n)` on `ℝ^n`. -/
def gaussVec (n : ℕ) : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => gaussianReal 0 1)

/-- `M(u) = E ‖F(u + √v G)‖²`, `G ∼ N(0, I_n)` (§3.2). -/
def momentM {n r : ℕ} (F : PolyMap n r) (v : ℝ) (u : Fin n → ℝ) : ℝ :=
  ∫ g, sqNorm (F.eval (u + Real.sqrt v • g)) ∂gaussVec n

/-- The sketch (16): with `g_1, …, g_q ∈ ℝ^n` and `γ_1, …, γ_q ∈ ℝ`,
`W(x) = ∑_{h=0}^{q} (v^{h/2}/√h!) D^h F(x)[g_1, …, g_h] ∏_{ℓ=h+1}^{q} γ_ℓ`
(indices are `0`-based here: `g_ℓ` is `g ⟨ℓ − 1, _⟩`). -/
def sketch {n r : ℕ} (F : PolyMap n r) (q : ℕ) (v : ℝ) (g : Fin q → Fin n → ℝ) (γ : Fin q → ℝ)
    (x : Fin n → ℝ) : Fin r → ℝ :=
  fun j => ∑ h : Fin (q + 1),
    Real.sqrt v ^ (h : ℕ) / Real.sqrt ((h : ℕ).factorial : ℝ) *
      derivApply F h x j (fun l => g (Fin.castLE (Nat.lt_succ_iff.mp h.isLt) l)) *
      ∏ l ∈ Finset.univ.filter (fun l : Fin q => (h : ℕ) ≤ (l : ℕ)), γ l

/-- The randomness of one sketch: independent `g_ℓ ∼ N(0, I_n)` and `γ_ℓ ∼ N(0, 1)`. -/
abbrev SketchNoise (n q : ℕ) := (Fin q → Fin n → ℝ) × (Fin q → ℝ)

/-- The law of one sketch's randomness. -/
def sketchNoise (n q : ℕ) : Measure (SketchNoise n q) :=
  (Measure.pi (fun _ : Fin q => gaussVec n)).prod (Measure.pi (fun _ : Fin q => gaussianReal 0 1))

/-- The law of the randomness of eight independent sketches. -/
def gateNoise (n q : ℕ) : Measure (Fin 8 → SketchNoise n q) :=
  Measure.pi (fun _ : Fin 8 => sketchNoise n q)

/-- The gate of Lemma 3.2 accepts the gate input `x`: every one of the eight sketches has squared
norm at most `T`. -/
def GateAccepts {n r : ℕ} (F : PolyMap n r) (q : ℕ) (v T : ℝ) (ρ : Fin 8 → SketchNoise n q)
    (x : Fin n → ℝ) : Prop :=
  ∀ k : Fin 8, sqNorm (sketch F q v (ρ k).1 (ρ k).2 x) ≤ T

/-- `α(u)`: the acceptance probability of the gate for a Gaussian gate input `A ∼ N(u, v I_n)`,
the sketches being independent of `A`. -/
def gateAcceptance {n r : ℕ} (F : PolyMap n r) (q : ℕ) (v T : ℝ) (u : Fin n → ℝ) : ℝ :=
  ((gaussVec n).prod (gateNoise n q)).real
    {p | GateAccepts F q v T p.2 (u + Real.sqrt v • p.1)}

/-- The constant `K_q = 3^{8q} e^{12q}` of Lemma 3.2. -/
def Kconst (q : ℕ) : ℝ := (3 : ℝ) ^ (8 * q) * Real.exp (12 * q)

/-! ## Views and stored histories (§3.1, PDF pp. 8–9) -/

/-- The law of the latent atom index: `P(I = i) = w_i`. -/
def atomLaw {s : ℕ} (w : Fin s → ℝ) : Measure (Fin s) :=
  ∑ i, ENNReal.ofReal (w i) • Measure.dirac i

/-- The randomness of one view pair together with a prior-history randomness `R₀ ∈ Ω₀` and the
eight sketches of a new gate: the atom index `I`, the gate-side noise `G_A`, the query-side noise
`G_B`, `R₀`, and the sketches. Given `I = i`, the gate input is `A = u_i + √v G_A` and the query is
`B = u_i + √v G_B`; all five components are independent. -/
def viewHistoryLaw {s n q : ℕ} (w : Fin s → ℝ) {Ω₀ : Type*} [MeasurableSpace Ω₀] (lam₀ : Measure Ω₀) :
    Measure (Fin s × (Fin n → ℝ) × (Fin n → ℝ) × Ω₀ × (Fin 8 → SketchNoise n q)) :=
  (atomLaw w).prod ((gaussVec n).prod ((gaussVec n).prod (lam₀.prod (gateNoise n q))))

/-- `a₁(u) = P(H₁ | u)`: the probability that the prior history `H₀(A, R₀)` and the appended gate
both accept, for `A ∼ N(u, v I_n)`, `R₀ ∼ lam₀` and fresh sketches, all independent. -/
def appendedAcceptance {n r : ℕ} (F : PolyMap n r) (q : ℕ) (v T : ℝ) {Ω₀ : Type*}
    [MeasurableSpace Ω₀] (lam₀ : Measure Ω₀) (H₀ : (Fin n → ℝ) → Ω₀ → Prop) (u : Fin n → ℝ) : ℝ :=
  ((gaussVec n).prod (lam₀.prod (gateNoise n q))).real
    {p | H₀ (u + Real.sqrt v • p.1) p.2.1 ∧ GateAccepts F q v T p.2.2 (u + Real.sqrt v • p.1)}

end GaussMixGated.ExactReal


