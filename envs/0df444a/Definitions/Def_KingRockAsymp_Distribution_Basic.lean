-- Prove2me | Definitions.Def_KingRockAsymp_Distribution_Basic
-- name    : KingRockAsymp_Distribution_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T12:40:41.358783+00:00
-- url     : https://prove2.me/theorems/0d92b145-b473-4545-9f33-5e28ac267c60
-- title:
--   Set limits, contingent derivatives, proto-/semi-differentiability, B-derivatives, subinvertibility, and assumptions M.1–4 and P.1–4
-- statement:
--   This file fixes the objects of King and Rockafellar's asymptotic theory for solutions of generalized equations $0 \in f(z,x) + N(x)$ with random data.
--
--   **Set limits (p. 3).** For a family of sets $A_i \subseteq E$ in a normed space indexed along a filter (a sequence $\nu \to \infty$, or $t \downarrow 0$), the **upper limit** $\limsup A_i$ is the set of points $x$ such that every ball around $x$ meets $A_i$ for frequently many $i$, and the **lower limit** $\liminf A_i$ the set of $x$ such that every ball around $x$ meets $A_i$ for all $i$ eventually. For sequences these are the paper's $\{x = \lim x^\nu \mid x^\nu \in A^\nu \text{ for infinitely many / all but finitely many } \nu\}$.
--
--   **Multifunctions.** A multifunction $G : E \rightrightarrows F$ has graph $\operatorname{gph} G = \{(z,x) \mid x \in G(z)\}$ and inverse $G^{-1}(x) = \{z \mid x \in G(z)\}$.
--
--   **Contingent derivative (2.2).** For $x \in G(z)$, $DG(z|x)$ is the multifunction whose graph is
--   $$\operatorname{gph} DG(z|x) = \limsup_{t \downarrow 0}\, t^{-1}\big[\operatorname{gph} G - (z,x)\big].$$
--   $G$ is **proto-differentiable** at $(z,x)$ if $\limsup = \liminf$ in (2.2), and **semi-differentiable** (2.3) if for every direction $w$ the set limit
--   $$\lim_{t \downarrow 0,\ w' \to w} t^{-1}\big[G(z + t w') - x\big] = DG(z|x)(w)$$
--   exists (lower and upper limits along $t \downarrow 0$, $w' \to w$ both equal $DG(z|x)(w)$).
--
--   **B-derivatives (2.4) and strong partial B-derivatives (p. 6).** A function $g$ is **B-differentiable** at $z$ with B-derivative $Dg(z)$ if $t^{-1}[g(z + t w') - g(z)] \to Dg(z)(w)$ as $t \downarrow 0$, $w' \to w$, for every $w$. A function $f : Z \times \mathbb R^n \to \mathbb R^m$ has a **strong partial B-derivative** $D_z f(z^*,x^*)$ in $z$ at $(z^*,x^*)$ if $D_z f(z^*,x^*)$ is the B-derivative of $z \mapsto f(z,x^*)$ at $z^*$, and for every $\varepsilon > 0$ there are neighborhoods $\Omega$ of $z^*$ and $U$ of $x^*$ such that, for every $x \in U$, the map $z \mapsto f(z,x) - f(z^*,x) - D_z f(z^*,x^*)(z - z^*)$ is Lipschitz with constant $\varepsilon$ on $\Omega$.
--
--   **The generalized equation.** For $f : Z \times \mathbb R^n \to \mathbb R^m$ and a multifunction $N : \mathbb R^n \rightrightarrows \mathbb R^m$, the solution map (2.1) is $J(z) = \{x \in \mathbb R^n \mid 0 \in f(z,x) + N(x)\}$.
--
--   **Subinvertibility (pp. 4–5).** $F : \mathbb R^n \rightrightarrows \mathbb R^m$ is **subinvertible** at $(x^*,0)$ if $0 \in F(x^*)$ and there are $\varepsilon > 0$, a compact convex neighborhood $U$ of $x^*$ and a mapping $G : \varepsilon B \rightrightarrows U$ with nonempty convex values and closed graph such that $x^* \in G(0)$ and $G(y) \subseteq F^{-1}(y)$ for all $y \in \varepsilon B$, where $B$ is the closed unit ball of $\mathbb R^m$.
--
--   **Analytical assumptions M.1–M.4 (p. 7)** at $(z^*,x^*)$, with $F = f(z^*,\cdot) + N$:
--
--   1. $f$ is jointly continuous and has partial B-derivatives in $x$ and in $z$ at $(z^*,x^*)$, the one in $z$ strong (the separable Banach space $Z$ is imposed by the theorems that use M.1);
--   2. $\operatorname{gph} N$ is closed and $N$ is proto-differentiable at $(x^*, -f(z^*,x^*))$;
--   3. $F$ is subinvertible at $(x^*,0)$;
--   4. $DF^{-1}(0|x^*)(y)$, the contingent derivative of $F^{-1}$ at $(0,x^*)$, has at most one element for every $y \in \mathbb R^m$.
--
--   **Probabilistic assumptions P.1–P.4 (p. 9)** for $f : U \times S \to \mathbb R^m$ and random elements $s_1, s_2, \dots$ of a measurable space $S$:
--
--   1. $f$ is continuous in $x$ on $U$ and measurable in $s$;
--   2. the $s_i$ are independent and identically distributed;
--   3. $E|f(x,s_1)|^2 < \infty$ for some $x \in U$;
--   4. there is $a : S \to \mathbb R$ with $E|a(s_1)|^2 < \infty$ and $|f(x_1,s) - f(x_2,s)| \le a(s)|x_1 - x_2|$ for all $x_1, x_2 \in U$.
--
--   **M-estimates (p. 9).** The empirical mean is $\bar f^\nu(x) = \frac1\nu \sum_{i=1}^\nu f(x,s_i)$, the expectation $Ef(x) = E f(x,s_1)$, and $F = Ef + N$ on $U$.
--
--   **The space $C_m(U)$ (Appendix, p. 16)** of continuous $\mathbb R^m$-valued functions on $U$ carries its Borel $\sigma$-algebra (for the sup norm).
--
--   These objects carry the paper's generalized implicit function theorem for asymptotic distributions (Theorem 2.6) and its application to M-estimates (Theorem 2.7).
--
--   **Formalization Note** Set limits are taken along filters with open balls; for sequences and for $t \downarrow 0$ they coincide with the paper's sequential definitions and are automatically closed, so the paper's restriction to closed sets is not needed. The contingent derivative is defined by (2.2) only; M.4's printed formula $\{u \mid y \in D_x f(z^*,x^*)(u) + DN(x^*|-f(z^*,x^*))(u)\}$ equals it under M.1 (a sum rule), which is not assumed. "B-differentiable" is read as (2.4), which is what the proofs use; the paper's alternative wording ("contingent derivative everywhere single-valued") agrees with it for locally Lipschitz maps on $\mathbb R^n$. Products $Z \times \mathbb R^n$, $\mathbb R^m \times \mathbb R^n$ carry Lean's max norm; none of the notions above depends on the choice among equivalent norms. $s_1$ is `s 0` and the empirical mean sums over `Finset.range ν`. $F = Ef + N$ is empty off $U$, since $f$ is only given on $U$. A Borel `MeasurableSpace` instance is declared on `C(↥U, Rn m)`.
-- source:
--   King & Rockafellar, Asymptotic Theory for Solutions in Statistical Estimation and Stochastic Programming, Math. Oper. Res. 18(1) (1993), §2 (set limits p. 3; (2.1) p. 4; subinvertibility pp. 4–5; (2.2) p. 5; (2.3), (2.4), strong partial B-derivative p. 6; M.1–M.4 p. 7; (2.5), P.1–P.4 p. 9) and Appendix p. 16 (authors' manuscript pagination)

import Mathlib

namespace KingRockAsymp.Distribution

open Set Filter Topology Metric MeasureTheory ProbabilityTheory

/-- `ℝⁿ` with the Euclidean norm `|·|`. -/
abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)

section SetValued

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Kuratowski upper limit (`lim sup`) of a family of sets along a filter (p. 3 for sequences,
p. 5 "the lim sup of a net of sets"): the points `x` such that every ball around `x` meets `A i`
for frequently many `i`. -/
def setLimsup {ι : Type*} (l : Filter ι) (A : ι → Set E) : Set E :=
  {x | ∀ ε > (0 : ℝ), ∃ᶠ i in l, (A i ∩ ball x ε).Nonempty}

/-- Kuratowski lower limit (`lim inf`) of a family of sets along a filter (p. 3): the points `x`
such that every ball around `x` meets `A i` for eventually all `i`. -/
def setLiminf {ι : Type*} (l : Filter ι) (A : ι → Set E) : Set E :=
  {x | ∀ ε > (0 : ℝ), ∀ᶠ i in l, (A i ∩ ball x ε).Nonempty}

/-- The graph `gph G = {(z, x) | x ∈ G(z)}` of a multifunction (p. 4). -/
def graph (G : E → Set F) : Set (E × F) := {p | p.2 ∈ G p.1}

/-- The inverse multifunction `G⁻¹(x) = {z | x ∈ G(z)}`. -/
def svInv (G : E → Set F) : F → Set E := fun y => {x | y ∈ G x}

/-- The difference quotients `t⁻¹[gph G − (z, x)]` of (2.2). -/
def graphQuot (G : E → Set F) (z : E) (x : F) (t : ℝ) : Set (E × F) :=
  (fun p => t⁻¹ • (p - (z, x))) '' graph G

/-- (2.2): the contingent derivative `DG(z|x)`, whose graph is
`lim sup_{t↓0} t⁻¹[gph G − (z, x)]`. -/
def contingentDeriv (G : E → Set F) (z : E) (x : F) : E → Set F :=
  fun w => {v | (w, v) ∈ setLimsup (𝓝[>] (0 : ℝ)) (graphQuot G z x)}

/-- p. 5: `G` is proto-differentiable at `(z, x)` when `lim sup = lim inf` in (2.2). -/
def IsProtoDifferentiable (G : E → Set F) (z : E) (x : F) : Prop :=
  setLiminf (𝓝[>] (0 : ℝ)) (graphQuot G z x) = setLimsup (𝓝[>] (0 : ℝ)) (graphQuot G z x)

/-- The quotients `t⁻¹[G(z + t w′) − x]` of (2.3), indexed by `(t, w′)`. -/
def fiberQuot (G : E → Set F) (z : E) (x : F) (p : ℝ × E) : Set F :=
  (fun y => p.1⁻¹ • (y - x)) '' G (z + p.1 • p.2)

/-- (2.3): `G` is semi-differentiable at `(z, x)`: for every direction `w` the set limit of
`t⁻¹[G(z + t w′) − x]` as `t ↓ 0`, `w′ → w` exists and equals `DG(z|x)(w)`. -/
def IsSemiDifferentiable (G : E → Set F) (z : E) (x : F) : Prop :=
  ∀ w : E,
    setLiminf (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (fiberQuot G z x) = contingentDeriv G z x w ∧
    setLimsup (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (fiberQuot G z x) = contingentDeriv G z x w

/-- (2.4): `g` is B-differentiable at `z` with B-derivative `D`:
`lim_{t↓0, w′→w} t⁻¹[g(z + t w′) − g(z)] = D(w)` for every `w`. -/
def HasBDerivAt (g : E → F) (D : E → F) (z : E) : Prop :=
  ∀ w : E, Tendsto (fun p : ℝ × E => p.1⁻¹ • (g (z + p.1 • p.2) - g z))
    (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 (D w))

end SetValued

section GenEq

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] {n m : ℕ}

/-- p. 6: `f` has a strong partial B-derivative `Dz` in `z` at `(z₀, x₀)`: `Dz` is the partial
B-derivative of `z ↦ f(z, x₀)` at `z₀`, and for every `ε > 0` there are neighborhoods `Ω` of `z₀`
and `U` of `x₀` such that for every `x ∈ U` the map `z ↦ f(z, x) − f(z₀, x) − Dz(z − z₀)` is
Lipschitz with constant `ε` on `Ω`. -/
def HasStrongPartialBDerivZ (f : Z → Rn n → Rn m) (Dz : Z → Rn m) (z₀ : Z) (x₀ : Rn n) : Prop :=
  HasBDerivAt (fun z => f z x₀) Dz z₀ ∧
  ∀ ε > (0 : ℝ), ∃ Ω ∈ 𝓝 z₀, ∃ U ∈ 𝓝 x₀, ∀ x ∈ U,
    LipschitzOnWith (Real.toNNReal ε) (fun z => f z x - f z₀ x - Dz (z - z₀)) Ω

/-- The multifunction `x ↦ f(z, x) + N(x)`. -/
def fPlusN (f : Z → Rn n → Rn m) (N : Rn n → Set (Rn m)) (z : Z) : Rn n → Set (Rn m) :=
  fun x => {y | ∃ v ∈ N x, y = f z x + v}

/-- (2.1): the solution map `J(z) = {x | 0 ∈ f(z, x) + N(x)}` of the generalized equation (1.1). -/
def solMap (f : Z → Rn n → Rn m) (N : Rn n → Set (Rn m)) : Z → Set (Rn n) :=
  fun z => {x | (0 : Rn m) ∈ fPlusN f N z x}

/-- pp. 4–5: `F : ℝⁿ ⇉ ℝᵐ` is subinvertible at `(x₀, 0)`: `0 ∈ F(x₀)`, and there are `ε > 0`, a
compact convex neighborhood `U` of `x₀` and a mapping `G : εB ⇉ U` with nonempty convex values and
closed graph such that `x₀ ∈ G(0)` and `G(y) ⊆ F⁻¹(y)` for all `y ∈ εB` (`B` the closed unit ball
of `ℝᵐ`). -/
def IsSubinvertibleAt (F : Rn n → Set (Rn m)) (x₀ : Rn n) : Prop :=
  (0 : Rn m) ∈ F x₀ ∧ ∃ ε > (0 : ℝ), ∃ U : Set (Rn n), IsCompact U ∧ Convex ℝ U ∧ U ∈ 𝓝 x₀ ∧
    ∃ G : Rn m → Set (Rn n),
      IsClosed {p : Rn m × Rn n | p.1 ∈ closedBall 0 ε ∧ p.2 ∈ G p.1} ∧ x₀ ∈ G 0 ∧
      ∀ y ∈ closedBall (0 : Rn m) ε,
        (G y).Nonempty ∧ Convex ℝ (G y) ∧ G y ⊆ U ∧ G y ⊆ svInv F y

/-- The analytical assumptions M.1–M.4 (p. 7) at `(z₀, x₀) = (z*, x*)`, with `Dz = D_z f(z*, x*)`.
"`Z` is a separable Banach space" (M.1) is carried by the instance arguments
`[CompleteSpace Z] [TopologicalSpace.SeparableSpace Z]` of the theorems that use this structure.
M.4 is stated on the contingent derivative (2.2) of `F⁻¹`, `F = f(z*, ·) + N`. -/
structure AnalyticalAssumptions (f : Z → Rn n → Rn m) (N : Rn n → Set (Rn m)) (z₀ : Z)
    (x₀ : Rn n) (Dz : Z → Rn m) : Prop where
  /-- M.1: `f` is jointly continuous. -/
  continuous : Continuous (fun p : Z × Rn n => f p.1 p.2)
  /-- M.1: `f` has a partial B-derivative in `x` at `(z*, x*)`. -/
  bderiv_x : ∃ Dx : Rn n → Rn m, HasBDerivAt (f z₀) Dx x₀
  /-- M.1: `Dz` is a strong partial B-derivative in `z` at `(z*, x*)`. -/
  strong_z : HasStrongPartialBDerivZ f Dz z₀ x₀
  /-- M.2: `N` is closed. -/
  closed_N : IsClosed (graph N)
  /-- M.2: `N` is proto-differentiable at `(x*, −f(z*, x*))`. -/
  proto_N : IsProtoDifferentiable N x₀ (-f z₀ x₀)
  /-- M.3: `F = f(z*, ·) + N` is subinvertible at `(x*, 0)`. -/
  subinv : IsSubinvertibleAt (fPlusN f N z₀) x₀
  /-- M.4: `DF⁻¹(0|x*)(y)` is at most a singleton for every `y`. -/
  single : ∀ y, (contingentDeriv (svInv (fPlusN f N z₀)) 0 x₀ y).Subsingleton

end GenEq

section MEstimates

variable {n m : ℕ} {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]

/-- The probabilistic assumptions P.1–P.4 (p. 9) on the set `U`; the paper's `s₁` is `s 0`. -/
structure ProbabilisticAssumptions (U : Set (Rn n)) (f : Rn n → S → Rn m) (s : ℕ → Ω → S)
    (P : Measure Ω) : Prop where
  /-- P.1: `f` is continuous in the first variable (on `U`). -/
  cont : ∀ σ : S, ContinuousOn (fun x => f x σ) U
  /-- P.1: `f` is measurable in the second variable. -/
  meas : ∀ x ∈ U, Measurable (f x)
  /-- The `sᵢ` are random variables. -/
  meas_s : ∀ i, Measurable (s i)
  /-- P.2: the `sᵢ` are independent. -/
  indep : iIndepFun s P
  /-- P.2: the `sᵢ` are identically distributed. -/
  ident : ∀ i, IdentDistrib (s i) (s 0) P P
  /-- P.3: there is `x ∈ U` with `E|f(x, s₁)|² < ∞`. -/
  moment : ∃ x ∈ U, MemLp (fun ω => f x (s 0 ω)) 2 P
  /-- P.4: `|f(x₁, s) − f(x₂, s)| ≤ a(s)|x₁ − x₂|` on `U` with `E|a(s₁)|² < ∞`. -/
  lip : ∃ a : S → ℝ, MemLp (fun ω => a (s 0 ω)) 2 P ∧
    ∀ σ : S, ∀ x₁ ∈ U, ∀ x₂ ∈ U, ‖f x₁ σ - f x₂ σ‖ ≤ a σ * ‖x₁ - x₂‖

/-- The empirical mean `f̄ν(x) = (1/ν) Σ_{i=1}^{ν} f(x, sᵢ)` (p. 9), with `sᵢ₊₁` written `s i`. -/
noncomputable def empMean (f : Rn n → S → Rn m) (s : ℕ → Ω → S) (ν : ℕ) (ω : Ω) (x : Rn n) :
    Rn m :=
  (ν : ℝ)⁻¹ • ∑ i ∈ Finset.range ν, f x (s i ω)

/-- The expectation `Ef(x) = E f(x, s₁)`. -/
noncomputable def expect (f : Rn n → S → Rn m) (s : ℕ → Ω → S) (P : Measure Ω) (x : Rn n) :
    Rn m :=
  ∫ ω, f x (s 0 ω) ∂P

/-- The multifunction `F = Ef + N` of Theorem 2.7, on `U` (where `f`, hence `Ef`, is given by
P.1); `F(x) = ∅` for `x ∉ U`. -/
def FEst (U : Set (Rn n)) (f : Rn n → S → Rn m) (s : ℕ → Ω → S) (P : Measure Ω)
    (N : Rn n → Set (Rn m)) : Rn n → Set (Rn m) :=
  fun x => {y | x ∈ U ∧ ∃ v ∈ N x, y = expect f s P x + v}

end MEstimates

section CmU

/-- The Borel σ-algebra on `C_m(U) = C(U, ℝᵐ)` (Appendix, p. 16). -/
noncomputable instance instMeasurableSpaceCmU {n m : ℕ} (U : Set (Rn n)) :
    MeasurableSpace C(↥U, Rn m) :=
  borel _

instance instBorelSpaceCmU {n m : ℕ} (U : Set (Rn n)) : BorelSpace C(↥U, Rn m) :=
  ⟨rfl⟩

end CmU

end KingRockAsymp.Distribution


