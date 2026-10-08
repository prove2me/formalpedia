-- Prove2me | Definitions.Def_RadGauss_LipschitzGaussian_Classes
-- name    : RadGauss_LipschitzGaussian_Classes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T08:40:16.061549+00:00
-- url     : https://prove2.me/theorems/2b97a47f-108b-487f-beb2-88c7295c1896
-- title:
--   Direct sums, φ∘F, and boolean combinations g(F_1,…,F_k) of function classes (Theorems 14 and 16)
-- statement:
--   This file collects the class constructions of Sections 3.2 and 3.3.
--
--   1. **Direct sum.** Let $\mathcal A = \mathbb R^m$ with its Euclidean structure. A class $F$ of maps $\mathcal X \to \mathcal A$ is a *subset of the direct sum* of real-valued classes $F_1, \dots, F_m$ when every $f \in F$ has the form $x \mapsto (f_1(x), \dots, f_m(x))$ with $f_i \in F_i$ for each $i$.
--   2. **Composition class.** For $\phi : \mathcal Y \times \mathcal A \to \mathbb R$ and $f : \mathcal X \to \mathcal A$, the function $\phi \circ f$ on $\mathcal X \times \mathcal Y$ is
--   $$
--   (\phi\circ f)(x, y) = \phi\bigl(y, f(x)\bigr),
--   $$
--   and $\phi \circ F = \{\phi \circ f : f \in F\}$.
--   3. **Boolean combination.** For a boolean function $g : \{\pm1\}^k \to \{\pm1\}$ and classes $F_1, \dots, F_k$ of $\{\pm1\}$-valued functions on $\mathcal X$,
--   $$
--   g(F_1, \dots, F_k) = \bigl\{\, x \mapsto g\bigl(f_1(x), \dots, f_k(x)\bigr) : f_j \in F_j \,\bigr\},
--   $$
--   regarded as a class of real-valued functions.
--
--   These are the objects whose Gaussian complexities Theorems 14 and 16 compare.
--
--   **Formalization Note** $\{\pm1\}$ is encoded as the unit group $\mathbb Z^\times = \{1, -1\}$, coerced to $\mathbb R$; a $\{\pm1\}$-valued class is a set of maps $\mathcal X \to \mathbb Z^\times$, and `signClass` views it as a class of real-valued functions. $\phi$ is written curried, $\phi\,y\,a = \phi(y,a)$.
-- source:
--   Bartlett, Mendelson, Rademacher and Gaussian Complexities: Risk Bounds and Structural Results, J. Mach. Learn. Res. 3 (2002), p. 471 (PDF p. 9), Theorem 14; p. 472 (PDF p. 10), Theorem 16

import Mathlib

namespace RadGauss.LipschitzGaussian

/-- **Direct sum** (Theorem 14, p. 471). A class `F` of functions from `X` to
`A = ℝ^m` (with its Euclidean structure) is a subset of the direct sum of the real classes
`F_1, …, F_m` when every `f ∈ F` has the form `x ↦ (f_1(x), …, f_m(x))` with `f_i ∈ F_i`, that is,
when its `i`-th coordinate function lies in `F_i` for every `i`. -/
def SubsetDirectSum {X : Type*} {m : ℕ} (F : Set (X → EuclideanSpace ℝ (Fin m)))
    (Fi : Fin m → Set (X → ℝ)) : Prop :=
  ∀ f ∈ F, ∀ i : Fin m, (fun x => (f x).ofLp i) ∈ Fi i

/-- **The class φ ∘ F** (Theorem 14, p. 471): for `φ : 𝒴 × A → ℝ` (written curried, `φ y a`)
and `f ∈ F`, `φ ∘ f` is the map `(x, y) ↦ φ(y, f(x))` on `𝒳 × 𝒴`; `φ ∘ F` is the set of all of
them. -/
def compClass {X Y A : Type*} (φ : Y → A → ℝ) (F : Set (X → A)) : Set (X × Y → ℝ) :=
  {h | ∃ f ∈ F, h = fun z => φ z.2 (f z.1)}

/-- A `{±1}`-valued function, encoded as a map into `ℤˣ = {1, -1}`, viewed as a real-valued
function through the coercion `ℤˣ → ℤ → ℝ`. -/
def signToReal {X : Type*} (f : X → ℤˣ) : X → ℝ := fun x => ((f x : ℤ) : ℝ)

/-- A class of `{±1}`-valued functions (maps into `ℤˣ`), viewed as a class of real-valued
functions. -/
def signClass {X : Type*} (F : Set (X → ℤˣ)) : Set (X → ℝ) := signToReal '' F

/-- **Boolean combination** (Theorem 16, p. 472): for a fixed boolean function
`g : {±1}^k → {±1}` and classes `F_1, …, F_k` of `{±1}`-valued functions,
`g(F_1, …, F_k) = {x ↦ g(f_1(x), …, f_k(x)) : f_j ∈ F_j}`, viewed as a class of real-valued
functions. -/
def boolComb {X : Type*} {k : ℕ} (g : (Fin k → ℤˣ) → ℤˣ) (F : Fin k → Set (X → ℤˣ)) :
    Set (X → ℝ) :=
  {h | ∃ f : Fin k → X → ℤˣ, (∀ j, f j ∈ F j) ∧ h = signToReal (fun x => g (fun j => f j x))}

end RadGauss.LipschitzGaussian


