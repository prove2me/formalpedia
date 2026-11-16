-- Prove2me | Definitions.Def_GaussPart_Supplement_BoolFn
-- name    : GaussPart_Supplement_BoolFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:00:28.475782+00:00
-- url     : https://prove2.me/theorems/05e636d0-701f-4379-a8f3-6b66775a5113
-- title:
--   Boolean functions, $K$-multi-index models, closure under affine restrictions, $-\mathcal F$
-- statement:
--   Throughout, functions on $\mathbb R^d$ are real valued. A **Boolean function** is a Borel measurable $f:\mathbb R^d\to\{-1,+1\}$; a function is **sign valued** if every value is $1$ or $-1$.
--
--   A Boolean function $f$ is a **$K$-multi-index model** ($K$-MIM) if there is a linear subspace $U\subseteq\mathbb R^d$ with $\dim U\le K$ such that
--   $$
--   f(x)=f(\mathrm{proj}_U x)\qquad\text{for every }x\in\mathbb R^d .
--   $$
--   A class $\mathcal F$ is **closed under affine restrictions** if for every $f\in\mathcal F$, every subspace $W\subseteq\mathbb R^d$ and every $b\in W^\perp$ the function $x\mapsto f(b+\mathrm{proj}_W x)$ belongs to $\mathcal F$.
--
--   For a $K\times d$ matrix $W$, $x\mapsto Wx$ is the linear map $\mathbb R^d\to\mathbb R^K$; a real polynomial in the $d$ coordinates is evaluated at $x$ in the usual way; and $-\mathcal F=\{-f: f\in\mathcal F\}$.
--
--   These are the basic objects of the paper's learning results: the concept classes are classes of $K$-MIMs closed under affine restrictions (Definitions 1.5, 4.1, F.1), and the reliable-learning reduction passes from $\mathcal F$ to $-\mathcal F$ (Lemma 6.3).
--
--   **Formalization Note** Measurability is the paper's convention for Boolean functions (Definition A.1); the subspace projection is Mathlib's orthogonal projection.
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Definition 1.3, p.2 (PDF p.4); Definition 1.5 (i), p.3; Definition 4.1 item 1, p.35; Definition A.1, p.69; Lemma 6.3, p.61

import Mathlib
import Definitions.Def_GaussPart_Cell

open scoped RealInnerProductSpace

namespace GaussPart

namespace Supplement

/-- A **Boolean function** on `ℝᵈ` (arXiv:2611.05264, sha256 7e0ca6d4…, Definition 1.3, p.2, PDF p.4;
Definition A.1, p.69, PDF p.71): a Borel measurable map `f : ℝᵈ → {±1}`.

**Formalization Note.** Boolean functions are real valued with every value `1` or `-1`, so that
`p_l ≤ f ≤ p_u` (Definition 1.5) is a real inequality. Measurability is the page's convention
("Borel measurable Boolean function", Definition A.1); the Gaussian surface area is defined only for
such functions. -/
def IsBoolFn {d : ℕ} (f : Vec d → ℝ) : Prop :=
  Measurable f ∧ ∀ x, f x = 1 ∨ f x = -1

/-- Every value is `1` or `-1`: a hypothesis `h : ℝᵈ → {±1}` as the learners of the paper output. -/
def IsSignValued {d : ℕ} (h : Vec d → ℝ) : Prop :=
  ∀ x, h x = 1 ∨ h x = -1

/-- **Definition 1.3** (multi-index model), p.2 (PDF p.4): `f` is a `K`-MIM if there is a subspace
`U ⊆ ℝᵈ` of dimension at most `K` with `f(x) = f(proj_U x)` for every `x`. -/
def IsKMIM {d : ℕ} (K : ℕ) (f : Vec d → ℝ) : Prop :=
  ∃ U : Submodule ℝ (Vec d), Module.finrank ℝ U ≤ K ∧ ∀ x, f x = f (U.starProjection x)

/-- **Closure under affine restrictions** (Definition 4.1 item 1, p.35, PDF p.37; Definition 1.5 (i),
p.3, PDF p.5): for every `f ∈ F`, every subspace `W` and every `b ∈ W^⊥`, the function
`x ↦ f(b + proj_W x)` belongs to `F`. -/
def ClosedUnderAffineRestr {d : ℕ} (F : Set (Vec d → ℝ)) : Prop :=
  ∀ f ∈ F, ∀ W : Submodule ℝ (Vec d), ∀ b ∈ Wᗮ, (fun x => f (b + W.starProjection x)) ∈ F

/-- The linear map `x ↦ Wx` for a `K × d` matrix `W`, as a map `ℝᵈ → ℝᴷ` of Euclidean spaces. -/
noncomputable def matVec {K d : ℕ} (W : Matrix (Fin K) (Fin d) ℝ) (x : Vec d) : Vec K :=
  WithLp.toLp 2 (W.mulVec fun i => x i)

/-- The value at `x ∈ ℝᵈ` of a real polynomial in the `d` coordinates. -/
noncomputable def evalPoly {d : ℕ} (p : MvPolynomial (Fin d) ℝ) (x : Vec d) : ℝ :=
  MvPolynomial.eval (fun i => x i) p

/-- The class `−F = {−f : f ∈ F}` (Lemma 6.3, p.61, PDF p.63). -/
def negClass {d : ℕ} (F : Set (Vec d → ℝ)) : Set (Vec d → ℝ) :=
  (fun f x => -f x) '' F

end Supplement

end GaussPart


