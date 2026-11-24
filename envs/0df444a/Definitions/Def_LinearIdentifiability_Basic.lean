-- Prove2me | Definitions.Def_LinearIdentifiability_Basic
-- name    : LinearIdentifiability_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T07:33:28.045964+00:00
-- url     : https://prove2.me/theorems/8506bc46-c3f6-4e8e-b49a-50c0774f006e
-- title:
--   Discriminative softmax models, linear similarity and diversity matrices
-- statement:
--   Objects of Sections 2-3 and Appendix C of Roeder, Metz and Kingma (2020).
--
--   1. **Data model (Section 2.1).** $p_{\mathcal D}(x,y,S)$ is an empirical (finitely supported) probability distribution over inputs $x\in X$, targets $y\in Y$ and finite candidate sets $S\subseteq Y$. A pair $(x,S)$ *occurs in the data* if $p_{\mathcal D}(x,S)>0$, and then $p_{\mathcal D}(y\mid x,S)>0\iff y\in S$. The input support is the set of $x$ with $p_{\mathcal D}(x)>0$ and the target support is the set of $y$ with $p_{\mathcal D}(y)>0$.
--   2. **Canonical discriminative form (eq. 1).** For a representation $f:X\to\mathbb R^M$ and a context map $g:Y\to\mathbb R^M$,
--   $$p(y\mid x,S)=\frac{\exp(f(x)^\top g(y))}{\sum_{y'\in S}\exp(f(x)^\top g(y'))}.$$
--   3. **Equality of models (eq. 4).** $p'=p^*$ means that the models $(f',g')$ and $(f^*,g^*)$ give the same $p(y\mid x,S)$ for every $(x,S)$ that occurs in the data and every $y\in S$.
--   4. **Linear similarity (Definition 1, eq. 3).** $(f',g')$ and $(f^*,g^*)$ are linearly similar if $f'(x)=Af^*(x)$ for all $x$ and $g'(y)=Bg^*(y)$ for all $y$, for invertible $M\times M$ matrices $A,B$. For a parameterisation $\theta\mapsto(f_\theta,g_\theta)$ of $\Theta$, $\theta'\sim_L\theta^*$ means that $(f_{\theta'},g_{\theta'})$ and $(f_{\theta^*},g_{\theta^*})$ are linearly similar.
--   5. **Diversity matrices.** For tuples $(y_A^{(i)},y_B^{(i)})_{i=1}^M$, $L$ is the $M\times M$ matrix with columns $g(y_A^{(i)})-g(y_B^{(i)})$ (Section 3.2). For tuples $(x^{(i)},S^{(i)})_{i=0}^M$, the $(M+1)\times(M+1)$ matrix $\mathbf M$ has columns $\tilde f(x^{(i)},S^{(i)})$ (Appendix C.1).
--   6. **Augmented representations (Appendix C, eqs. 10-12).** $Z(x,S)=\log\sum_{y'\in S}\exp(f(x)^\top g(y'))$, $\tilde f(x,S)=[-Z(x,S);f(x)]\in\mathbb R^{M+1}$ and $\tilde g(y)=[1;g(y)]\in\mathbb R^{M+1}$.
--
--   **Formalization Note** The data distribution is a `PMF` on $X\times Y\times\mathrm{Finset}\,Y$ with finite support; only its support enters the statements. The parameter space $\Theta$ appears only in Definition 1: the theorems quantify directly over the four functions $f',g',f^*,g^*$, which is equivalent to quantifying over all parameterisations and all $\theta',\theta^*$. A vector of $\mathbb R^M$ is a function $\mathrm{Fin}\,M\to\mathbb R$, and a matrix is invertible when its determinant is a unit.
-- source:
--   Roeder, Metz and Kingma, On Linear Identifiability of Learned Representations, arXiv:2007.00810v3 (2020), Section 2.1 (data model, p. 2), Section 2.2 (eq. (1), p. 3), Section 3.2 (Definition 1, eq. (3), diversity condition, p. 4), Appendix C (eqs. (9)-(12), p. 14) and Appendix C.1 (p. 14)

import Mathlib

/-!
Roeder, Metz and Kingma, *On Linear Identifiability of Learned Representations*,
arXiv:2007.00810v3 (2020): the data model of Section 2.1, the canonical discriminative form
(eq. (1)) of Section 2.2, the linear similarity relation of Definition 1 (Section 3.2), the matrices
of the diversity conditions (Section 3.2 and Appendix C.1), and the augmented representations of
Appendix C, eqs. (9)-(12).
-/

open Matrix

noncomputable section

namespace LinearIdentifiability

variable {X Y : Type*} {M : ℕ}

/-- Section 2.1: `p_D(x, S) > 0`, i.e. the pair `(x, S)` occurs in the data distribution
`p_D(x, y, S)` (some target `y` has positive probability together with `x` and `S`). -/
def IsSupported (pD : PMF (X × Y × Finset Y)) (x : X) (S : Finset Y) : Prop :=
  ∃ y, pD (x, y, S) ≠ 0

/-- Section 2.1: `p_D` is an empirical distribution (finitely supported) over inputs `x`, targets
`y` and finite candidate sets `S`, and `S` is the set of possible values of `y` given `x`:
`p_D(y | x, S) > 0 ⇔ y ∈ S` whenever `p_D(x, S) > 0`. -/
def IsDataDistribution (pD : PMF (X × Y × Finset Y)) : Prop :=
  pD.support.Finite ∧ ∀ x S, IsSupported pD x S → ∀ y, (pD (x, y, S) ≠ 0 ↔ y ∈ S)

/-- Section 2.1: the inputs `x` that occur in the data, `p_D(x) > 0`. -/
def inputSupport (pD : PMF (X × Y × Finset Y)) : Set X :=
  {x | ∃ S, IsSupported pD x S}

/-- Section 2.1: the targets `y` that occur in the data, `p_D(y) > 0`. -/
def targetSupport (pD : PMF (X × Y × Finset Y)) : Set Y :=
  {y | ∃ x S, pD (x, y, S) ≠ 0}

/-- Section 2.2, eq. (1): the canonical discriminative form
`p_θ(y | x, S) = exp(f(x)ᵀ g(y)) / ∑_{y' ∈ S} exp(f(x)ᵀ g(y'))`, for a representation
`f : X → ℝ^M` and a context map `g : Y → ℝ^M`. -/
def modelProb (f : X → Fin M → ℝ) (g : Y → Fin M → ℝ) (x : X) (S : Finset Y) (y : Y) : ℝ :=
  Real.exp (f x ⬝ᵥ g y) / ∑ y' ∈ S, Real.exp (f x ⬝ᵥ g y')

/-- Section 3.1-3.2, eq. (4): `p' = p*`, the two models `(f', g')` and `(f*, g*)` of the form (1)
assign the same conditional probability `p(y | x, S)` to every `(x, S)` occurring in the data and
every `y ∈ S`. -/
def ModelsAgreeOnData (pD : PMF (X × Y × Finset Y)) (f' : X → Fin M → ℝ) (g' : Y → Fin M → ℝ)
    (fstar : X → Fin M → ℝ) (gstar : Y → Fin M → ℝ) : Prop :=
  ∀ x S, IsSupported pD x S → ∀ y ∈ S, modelProb f' g' x S y = modelProb fstar gstar x S y

/-- Definition 1, eq. (3), on representation functions: `f' = A f*` and `g' = B g*` for invertible
`M × M` matrices `A` and `B`. -/
def LinearlySimilar (f' fstar : X → Fin M → ℝ) (g' gstar : Y → Fin M → ℝ) : Prop :=
  ∃ A B : Matrix (Fin M) (Fin M) ℝ, IsUnit A.det ∧ IsUnit B.det ∧
    (∀ x, f' x = A *ᵥ fstar x) ∧ (∀ y, g' y = B *ᵥ gstar y)

/-- Definition 1, eq. (3): the relation `θ' ∼_L θ*` on the parameter space `Θ`, for a
parameterisation `θ ↦ (f_θ, g_θ)`. -/
def LinSim {Θ : Type*} (f : Θ → X → Fin M → ℝ) (g : Θ → Y → Fin M → ℝ) (θ' θstar : Θ) : Prop :=
  LinearlySimilar (f θ') (f θstar) (g θ') (g θstar)

/-- Section 3.2 (diversity condition): the `M × M` matrix `L` whose `i`-th column is
`g(y_A^{(i)}) - g(y_B^{(i)})`, for tuples `(y_A^{(i)}, y_B^{(i)}) = (a i, b i)`. -/
def diffMatrix (g : Y → Fin M → ℝ) (a b : Fin M → Y) : Matrix (Fin M) (Fin M) ℝ :=
  fun j i => g (a i) j - g (b i) j

/-- Appendix C, eq. (12): the log-normaliser `Z(x, S) = log ∑_{y' ∈ S} exp(f(x)ᵀ g(y'))`. -/
def logNormalizer (f : X → Fin M → ℝ) (g : Y → Fin M → ℝ) (x : X) (S : Finset Y) : ℝ :=
  Real.log (∑ y' ∈ S, Real.exp (f x ⬝ᵥ g y'))

/-- Appendix C, eq. (10): the augmented representation `f̃(x, S) = [-Z(x, S); f(x)] ∈ ℝ^{M+1}`. -/
def augF (f : X → Fin M → ℝ) (g : Y → Fin M → ℝ) (x : X) (S : Finset Y) : Fin (M + 1) → ℝ :=
  vecCons (-logNormalizer f g x S) (f x)

/-- Appendix C, eq. (11): the augmented context map `g̃(y) = [1; g(y)] ∈ ℝ^{M+1}`. -/
def augG (g : Y → Fin M → ℝ) (y : Y) : Fin (M + 1) → ℝ :=
  vecCons 1 (g y)

/-- Appendix C.1 (diversity condition for `g`): the `(M+1) × (M+1)` matrix whose `i`-th column is
`f̃(x^{(i)}, S^{(i)})`, `i = 0, …, M`. -/
def augFMatrix (f : X → Fin M → ℝ) (g : Y → Fin M → ℝ) (xs : Fin (M + 1) → X)
    (Ss : Fin (M + 1) → Finset Y) : Matrix (Fin (M + 1)) (Fin (M + 1)) ℝ :=
  fun j i => augF f g (xs i) (Ss i) j

end LinearIdentifiability


