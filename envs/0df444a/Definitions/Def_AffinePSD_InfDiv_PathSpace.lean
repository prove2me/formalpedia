-- Prove2me | Definitions.Def_AffinePSD_InfDiv_PathSpace
-- name    : AffinePSD_InfDiv_PathSpace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:49:36.773365+00:00
-- url     : https://prove2.me/theorems/8a2f7c3d-1290-46fd-ad02-6aa76519d8a5
-- title:
--   The canonical path space $\Omega$, the family $\mathcal P$, the convolution $P*Q$ and infinite decomposability (§2, pp. 10–11; Definition 2.7(i))
-- statement:
--   Let $S_d^+\cup\{\Delta\}$ be the one-point compactification of $S_d^+$, with its Borel σ-algebra; $\Delta$ is the cemetery. Extend addition by $x+\Delta=\Delta+x=\Delta$. The **canonical space** $\Omega$ consists of paths $\omega:\mathbb R_+\to S_d^+\cup\{\Delta\}$, with the canonical process $X_t(\omega)=\omega(t)$ and $\mathcal F^X=\sigma(X_t,\ t\ge0)$.
--
--   **The family $\mathcal P$.** A family $(P_x)_{x\in S_d^+}$ of probability measures on $(\Omega,\mathcal F^X)$ belongs to $\mathcal P$ (with transition family $p$) if:
--
--   1. $P_x[X_0=x]=1$ for every $x$;
--   2. paths stay at $\Delta$: $P_x[X_s=\Delta,\ X_t\ne\Delta]=0$ for $s\le t$;
--   3. $p$ is a stochastically continuous sub-stochastic transition family;
--   4. $X$ is Markov with transition family $p$: for $0\le t_1\le\dots\le t_N$ and Borel $A_1,\dots,A_N\subseteq S_d^+$,
--   $$P_x[X_{t_1}\in A_1,\dots,X_{t_N}\in A_N]=\int_{A_1}p_{t_1}(x,dy_1)\int_{A_2}p_{t_2-t_1}(y_1,dy_2)\cdots\int_{A_N}p_{t_N-t_{N-1}}(y_{N-1},dy_N).$$
--
--   **Convolution.** For probability measures $P,Q$ on $\Omega$, $P*Q$ is the push-forward of $P\times Q$ under $(\omega,\omega')\mapsto\omega+\omega'$ (pointwise addition). The $k$-fold convolution $P^{(1)}*\dots*P^{(k)}$ is formed iteratively.
--
--   **Infinite decomposability** (Definition 2.7(i)). $(P_x)\in\mathcal P$ is infinitely decomposable if for each $k\ge1$ there is $(P^{(k)}_x)\in\mathcal P$ with
--   $$P_{x^{(1)}+\dots+x^{(k)}}=P^{(k)}_{x^{(1)}}*\dots*P^{(k)}_{x^{(k)}}\qquad\text{for all }x^{(1)},\dots,x^{(k)}\in S_d^+.$$
--
--   The file also defines the Laplace functional $e^{-\sum_{i=1}^N\langle u^{(i)},X_{t_i}\rangle}$ of a path, with the convention $f(\Delta)=0$: it is $0$ on a path that is at $\Delta$ at some $t_i$.
--
--   **Formalization Note** The paper realizes $X$ on the càdlàg space $D(S_d^+\cup\{\Delta\})$ with paths absorbed at $\Delta$. Here $\Omega$ is the space of all paths $\mathbb R_{\ge0}\to S_d^+\cup\{\Delta\}$ with the product σ-algebra; $\mathcal F^X$ on the càdlàg subspace is the trace of that σ-algebra. Every notion used in Theorem 2.9 is determined by finite-dimensional distributions: membership in $\mathcal P$, the convolution (whose finite-dimensional distributions are the convolutions of those of the factors), and the marginals. So this reading is equivalent for the statements of the mission, and absorption at $\Delta$ is imposed in law (item 2). The paper does not say what $\Delta+x$ is. Taking $\Delta$ absorbing is the only reading under which $\omega+\omega'$ is again a path of $\Omega$. The Markov property is encoded through the finite-dimensional distributions, tested on indicators of Borel sets (which generate the bounded measurable test functions). The empty convolution is the point mass at the zero path, and the one-fold convolution is the measure itself; associativity makes the bracketing irrelevant. The sum map is measurable, so the push-forward is a genuine one.
-- source:
--   Cuchiero, Filipović, Mayerhofer, Teichmann, Affine processes on positive semidefinite matrices, arXiv:0910.0137v3 (2011), §2, p. 10 (Ω), p. 11 (𝒫, convolution), Definition 2.7(i), pp. 11–12; f(Δ) = 0 convention, p. 7

import Mathlib
import Definitions.Def_AffinePSD_InfDiv_Cone
import Definitions.Def_AffinePSD_Necessity_Process

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal OnePoint

namespace AffinePSD.InfDiv

/-- The extended state space `S_d^+ ∪ {Δ}`, the one-point compactification of `S_d^+`
(arXiv:0910.0137v3, §1.2, p. 6); the cemetery `Δ` is `∞`. -/
abbrev Ext (d : ℕ) := OnePoint (AffinePSD.Necessity.Cone d)

/-- The Borel σ-algebra on `S_d^+ ∪ {Δ}`. -/
instance instMeasurableSpaceExt (d : ℕ) : MeasurableSpace (Ext d) := borel _

instance instBorelSpaceExt (d : ℕ) : BorelSpace (Ext d) := ⟨rfl⟩

/-- Addition on `S_d^+ ∪ {Δ}`: `x + y` for `x, y ∈ S_d^+`, and `Δ` as soon as one summand is `Δ`.
Formalization Note: the paper writes `ω + ω′` without saying what `Δ + x` is; taking `Δ` absorbing
is the only reading under which `ω + ω′` is again a path of `Ω`. -/
def addE {d : ℕ} : Ext d → Ext d → Ext d
  | (x : AffinePSD.Necessity.Cone d), (y : AffinePSD.Necessity.Cone d) => ((coneAdd x y : AffinePSD.Necessity.Cone d) : Ext d)
  | _, _ => (∞ : Ext d)

/-- The canonical path space. Formalization Note: the paper's `Ω = D(S_d^+ ∪ {Δ})` is the space of
càdlàg paths `ω : ℝ_+ → S_d^+ ∪ {Δ}` that stay at `Δ` once there, with `F^X = σ(X_t, t ≥ 0)`, the
trace of the product σ-algebra. Every notion of Theorem 2.9 is determined by finite-dimensional
distributions, so all paths `ℝ≥0 → S_d^+ ∪ {Δ}` with the product σ-algebra are used, and absorption
at `Δ` is imposed in law (see `InPWith`). The canonical process is `X_t(ω) = ω t`. -/
abbrev Path (d : ℕ) := ℝ≥0 → Ext d

/-- The path identically equal to the zero matrix (the neutral element of `∗`). -/
def zeroPath {d : ℕ} : Path d := fun _ => ((⟨0, Matrix.PosSemidef.zero⟩ : AffinePSD.Necessity.Cone d) : Ext d)

/-- The convolution `P ∗ Q` of two probability measures on paths (§2, p. 11): the push-forward of
`P × Q` under `(ω, ω′) ↦ ω + ω′` (pointwise `addE`). -/
noncomputable def conv {d : ℕ} (P Q : Measure (Path d)) : Measure (Path d) :=
  (P.prod Q).map (fun q t => addE (q.1 t) (q.2 t))

/-- The convolution of a finite list of measures on paths, `P_1 ∗ (P_2 ∗ (⋯ ∗ P_k))`
(the empty convolution is the point mass at the zero path). -/
noncomputable def convL {d : ℕ} : List (Measure (Path d)) → Measure (Path d)
  | [] => Measure.dirac zeroPath
  | [P] => P
  | P :: rest => conv P (convL rest)

/-- The `k`-fold convolution `Q_0 ∗ ⋯ ∗ Q_{k−1}`. -/
noncomputable def convK {d : ℕ} (k : ℕ) (Q : Fin k → Measure (Path d)) : Measure (Path d) :=
  convL (List.ofFn Q)

/-- The iterated kernel integral
`∫_{A_1} p_{t_1 − s}(x, dy_1) ∫_{A_2} p_{t_2 − t_1}(y_1, dy_2) ⋯ ∫_{A_N} p_{t_N − t_{N−1}}(y_{N−1}, dy_N) 1`
for a list `[(t_1, A_1), …, (t_N, A_N)]`. -/
noncomputable def iterL {d : ℕ} (p : ℝ → Kernel (AffinePSD.Necessity.Cone d) (AffinePSD.Necessity.Cone d)) :
    List (ℝ≥0 × Set (AffinePSD.Necessity.Cone d)) → ℝ≥0 → AffinePSD.Necessity.Cone d → ℝ≥0∞
  | [], _, _ => 1
  | (t, A) :: rest, s, x => ∫⁻ y in A, iterL p rest t y ∂(p ((t : ℝ) - (s : ℝ)) x)

/-- `(P_x)_{x ∈ S_d^+} ∈ 𝒫` with transition family `p` (§2, p. 11): every `P_x` is a probability
measure on paths, `P_x[X_0 = x] = 1`, paths stay at `Δ` once there (in law), `p` is a
stochastically continuous sub-stochastic transition family, and the finite-dimensional
distributions of `X` under `P_x` are those of the Markov process with transition family `p`:
for `0 ≤ t_1 ≤ ⋯ ≤ t_N` and Borel `A_i ⊆ S_d^+`,
`P_x[X_{t_1} ∈ A_1, …, X_{t_N} ∈ A_N] = ∫_{A_1} p_{t_1}(x,dy_1) ⋯ ∫_{A_N} p_{t_N−t_{N−1}}(y_{N−1},dy_N)`.
Formalization Note: the Markov property is encoded by the finite-dimensional distributions;
indicators of Borel sets generate the bounded measurable test functions. -/
def InPWith {d : ℕ} (Px : AffinePSD.Necessity.Cone d → Measure (Path d)) (p : ℝ → Kernel (AffinePSD.Necessity.Cone d) (AffinePSD.Necessity.Cone d)) : Prop :=
  (∀ x, IsProbabilityMeasure (Px x)) ∧
  (∀ x : AffinePSD.Necessity.Cone d, Px x {ω | ω 0 = (x : Ext d)} = 1) ∧
  (∀ x (s t : ℝ≥0), s ≤ t → Px x {ω | ω s = (∞ : Ext d) ∧ ω t ≠ (∞ : Ext d)} = 0) ∧
  AffinePSD.Necessity.IsTransition p ∧ AffinePSD.Necessity.IsStochCont p ∧
  ∀ x (L : List (ℝ≥0 × Set (AffinePSD.Necessity.Cone d))), L.Pairwise (fun a b => a.1 ≤ b.1) →
    (∀ a ∈ L, MeasurableSet a.2) →
    Px x {ω | ∀ a ∈ L, ∃ y ∈ a.2, ω a.1 = (y : Ext d)} = iterL p L 0 x

/-- `(P_x)_{x ∈ S_d^+} ∈ 𝒫` (§2, p. 11): a stochastically continuous Markov family on `S_d^+` with
`P_x[X_0 = x] = 1`. -/
def InP {d : ℕ} (Px : AffinePSD.Necessity.Cone d → Measure (Path d)) : Prop :=
  ∃ p : ℝ → Kernel (AffinePSD.Necessity.Cone d) (AffinePSD.Necessity.Cone d), InPWith Px p

/-- Definition 2.7(i) (pp. 11–12): `(P_x) ∈ 𝒫` is infinitely decomposable if for each `k ≥ 1` there
is `(P^{(k)}_x) ∈ 𝒫` with `P_{x^{(1)} + ⋯ + x^{(k)}} = P^{(k)}_{x^{(1)}} ∗ ⋯ ∗ P^{(k)}_{x^{(k)}}`
for all `x^{(1)}, …, x^{(k)} ∈ S_d^+`. -/
def InfDecomp {d : ℕ} (Px : AffinePSD.Necessity.Cone d → Measure (Path d)) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ Q : AffinePSD.Necessity.Cone d → Measure (Path d), InP Q ∧
    ∀ xs : Fin k → AffinePSD.Necessity.Cone d, Px (coneSum xs) = convK k (fun i => Q (xs i))

/-- The Laplace functional `e^{−Σ_{i=1}^N ⟨u^{(i)}, X_{t_i}(ω)⟩}` of a path at times
`t = (t_1, …, t_N)` and directions `u = (u^{(1)}, …, u^{(N)}) ∈ (S_d^+)^N`, with the convention
`f(Δ) = 0` (§2, p. 7): it is `0` on paths that are at `Δ` at some `t_i`. -/
noncomputable def lapPath {d N : ℕ} (t : Fin N → ℝ≥0) (u : Fin N → AffinePSD.Necessity.Cone d) (ω : Path d) : ℝ :=
  ∏ i, (ω (t i)).elim 0 (fun y => Real.exp (- AffinePSD.Necessity.tr (u i).1 y.1))

end AffinePSD.InfDiv


