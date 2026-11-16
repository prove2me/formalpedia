-- Prove2me | Definitions.Def_TopicalIrreducibility_Relations_Supplement_Conditions
-- name    : TopicalIrreducibility_Relations_Supplement_Conditions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T15:19:32.001975+00:00
-- url     : https://prove2.me/theorems/8dfbc200-3498-43ae-9455-9f881809461e
-- title:
--   Eq. (3.1), Definitions 3.1, 3.3, pp. 2–3, 6–7 — Hilbert's projective metric, slice spaces, parts, partial irreducibility, imperturbability
-- statement:
--   Let $f:\mathbb R^n_{\ge0}\to\mathbb R^n_{\ge0}$, write $[n]=\{1,\dots,n\}$, $e_J$ for the indicator vector of $J\subseteq[n]$ and $\mathbf 1=e_{[n]}$.
--
--   1. **Hilbert's projective metric** (p. 2). For $x,y\in\mathbb R^n_{>0}$,
--   $$
--   d_H(x,y)=\inf\{\log(\beta/\alpha):\alpha x\le y\le\beta x\}=\log\frac{\max_i y_i/x_i}{\min_i y_i/x_i}.
--   $$
--   A set $W\subseteq\mathbb R^n_{>0}$ is **bounded in Hilbert's projective metric** if there is a real $B$ with $d_H(x,y)\le B$ for all $x,y\in W$ (the empty set is bounded).
--   2. **Slice space** (p. 3). For real $\alpha,\beta>0$, $S_\alpha^\beta(f)=\{x\in\mathbb R^n_{>0}:\alpha x\le f(x)\le\beta x\}$.
--   3. **Eigenvector in $\mathbb R^n_{>0}$.** A vector $u\in\mathbb R^n_{>0}$ with $f(u)=\lambda u$ for some real $\lambda>0$.
--   4. **Diagonal composition.** For $d\in\mathbb R^n$ with positive entries and $D=\operatorname{diag}(d)$, $(D\circ f)(x)_i=d_i\,f(x)_i$.
--   5. **Hilbert metric uniform perturbation** (p. 7). $g$ is one of $f$ if there is a real $C$ with $d_H(f(x),g(x))\le C$ for all $x\in\mathbb R^n_{>0}$.
--   6. **Parts** (Eq. (3.1), p. 6). $P_J=\{x\in\mathbb R^n_{\ge0}: x_i>0\iff i\in J\}$.
--   7. **Definition 3.1.** $f$ is **partially irreducible** if it has no invariant parts other than $P_\emptyset=\{0\}$ and $P_{[n]}=\mathbb R^n_{>0}$: there is no nonempty proper $J$ with $f(P_J)\subseteq P_J$.
--   8. **Definition 3.3.** $f$ is **imperturbable** if there are no nonempty subsets $I\subseteq J\subsetneq[n]$ such that $f(e_I)_i>0$ for all $i\in I$ and $\lim_{t\to\infty}f(\mathbf 1+te_J)_i<\infty$ for all $i\notin J$.
--
--   These are the objects of §3, "Other conditions like irreducibility", whose relations to positive eigenvectors are Theorems 3.4 and 3.5.
--
--   **Formalization Note** The cone, interior, m-topicality, indicator vectors and "nonempty proper" subsets are the published base definitions of this mission. $d_H$ is the published `CompOT.SinkhornConv.hilbertDist`, $\log\max_{i,j}(x_iy_j)/(x_jy_i)$, applied to the real coordinates; on positive vectors it equals the formula above, and it is only applied to interior vectors (on $n=0$ its value is $0$, and the empty vector counts as an interior eigenvector with $\lambda=1$). Scalars $\alpha,\beta,\lambda,d_i$ are positive elements of `ℝ≥0`. As in the base Definition 2.3, "$\lim_{t\to\infty}f(\mathbf 1+te_J)_i<\infty$" is encoded as a finite bound on the whole ray $t\ge0$, one bound per coordinate; for an order-preserving $f$ the ray is monotone, so the two are equivalent.
-- source:
--   Brian Lins, Irreducibility for Topical Maps, STOC 2027 submission #201 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/201.pdf, p. 2 (Hilbert projective metric), p. 3 (slice spaces), p. 6 (Eq. (3.1), Definition 3.1, Definition 3.3), p. 7 (Definition 3.3 continued; Hilbert metric uniform perturbation); PDF page = printed page

import Mathlib
import Definitions.Def_TopicalIrreducibility_Relations_MTopical
import Definitions.Def_TopicalIrreducibility_Relations_Irreducibility
import Definitions.Def_CompOT_SinkhornConv_hilbertDist

open scoped NNReal

namespace TopicalIrreducibility.Relations.Supplement

open TopicalIrreducibility.Relations

/-- Hilbert's projective metric on the standard cone (p. 2):
`d_H(x, y) = inf {log(β/α) : α x ≤ y ≤ β x}`, which for `x, y ∈ ℝⁿ_{>0}` equals
`log (max_i (y_i/x_i) / min_i (y_i/x_i)) = log max_{i,j} (x_i y_j)/(x_j y_i)`.
It reuses the published `CompOT.SinkhornConv.hilbertDist` on the real coercions of the
coordinates. It is only applied to interior vectors; on `Fin 0` its value is `0`. -/
noncomputable def hDist {n : ℕ} (x y : StdCone n) : ℝ :=
  CompOT.SinkhornConv.hilbertDist (fun i => (x i : ℝ)) (fun i => (y i : ℝ))

/-- A set `W ⊆ ℝⁿ_{>0}` is bounded in Hilbert's projective metric (pp. 2–3): its Hilbert
diameter is finite, i.e. some real `B` bounds `d_H(x, y)` for all `x, y ∈ W`. The empty set is
bounded. -/
def HilbertBounded {n : ℕ} (W : Set (StdCone n)) : Prop :=
  ∃ B : ℝ, ∀ x ∈ W, ∀ y ∈ W, hDist x y ≤ B

/-- The slice space `S_α^β(f) = {x ∈ ℝⁿ_{>0} : α x ≤ f(x) ≤ β x}` (p. 3). -/
def sliceSpace {n : ℕ} (f : StdCone n → StdCone n) (α β : ℝ≥0) : Set (StdCone n) :=
  {x | IsInterior x ∧ α • x ≤ f x ∧ f x ≤ β • x}

/-- `g` has an eigenvector in `ℝⁿ_{>0}`: an interior `u` and a real `λ > 0` with `g(u) = λ u`.
For `n > 0` an interior `u` is nonzero; for an m-topical `g` every eigenvalue at an interior
vector is automatically positive. On `Fin 0` the empty vector qualifies (with `λ = 1`). -/
def HasInteriorEigenvector {n : ℕ} (g : StdCone n → StdCone n) : Prop :=
  ∃ u : StdCone n, IsInterior u ∧ ∃ l : ℝ≥0, 0 < l ∧ g u = l • u

/-- The composition `D ∘ f` with the diagonal matrix `D = diag(d)`:
`(D ∘ f)(x)_i = d_i f(x)_i` (Theorem 3.4 (3), p. 7). -/
def diagComp {n : ℕ} (d : Fin n → ℝ≥0) (f : StdCone n → StdCone n) :
    StdCone n → StdCone n :=
  fun x i => d i * f x i

/-- `g` is a Hilbert metric uniform perturbation of `f` (p. 7): the Hilbert projective distance
between `f(x)` and `g(x)` is bounded uniformly over `x ∈ ℝⁿ_{>0}`. -/
def IsHilbertUniformPerturbation {n : ℕ} (f g : StdCone n → StdCone n) : Prop :=
  ∃ C : ℝ, ∀ x : StdCone n, IsInterior x → hDist (f x) (g x) ≤ C

/-- The part `P_J = {x ∈ ℝⁿ_{≥0} : x_i > 0 iff i ∈ J}`, Eq. (3.1), p. 6. -/
def part {n : ℕ} (J : Finset (Fin n)) : Set (StdCone n) :=
  {x | ∀ i, 0 < x i ↔ i ∈ J}

/-- Definition 3.1 (p. 6): `f` is partially irreducible if it has no invariant parts other than
`P_∅ = {0}` and `P_[n] = ℝⁿ_{>0}`, i.e. for no nonempty proper `J` is `f(P_J) ⊆ P_J`. -/
def PartiallyIrreducible {n : ℕ} (f : StdCone n → StdCone n) : Prop :=
  ∀ J : Finset (Fin n), IsNontrivialProper J → ¬ Set.MapsTo f (part J) (part J)

/-- Definition 3.3 (pp. 6–7): `f` is imperturbable if there are no nonempty subsets
`I ⊆ J ⊊ [n]` such that `f(e_I)_i > 0` for all `i ∈ I` and `lim_{t→∞} f(1 + t e_J)_i < ∞` for
all `i ∉ J`. As in Definition 2.3 of the base mission, for an order-preserving `f` the ray
`t ↦ f(1 + t e_J)_i` is monotone, so its limit is finite exactly when the whole
nonnegative-real ray is bounded; each outside coordinate has its own bound. -/
def Imperturbable {n : ℕ} (f : StdCone n → StdCone n) : Prop :=
  ¬ ∃ I J : Finset (Fin n), I.Nonempty ∧ I ⊆ J ∧ J ≠ Finset.univ ∧
    (∀ i ∈ I, 0 < f (indicatorVec I) i) ∧
    ∀ i, i ∉ J → ∃ B : ℝ≥0, ∀ t : ℝ≥0, f (1 + t • indicatorVec J) i ≤ B

end TopicalIrreducibility.Relations.Supplement


