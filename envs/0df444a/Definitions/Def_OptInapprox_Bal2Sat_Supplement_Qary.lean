-- Prove2me | Definitions.Def_OptInapprox_Bal2Sat_Supplement_Qary
-- name    : OptInapprox_Bal2Sat_Supplement_Qary
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:52:45.236821+00:00
-- url     : https://prove2.me/theorems/f438aacf-e6fd-4ae9-8a79-17fc04e4564f
-- title:
--   Definitions 5–7,16–20 and §11.2 — q-ary products and orthogonal subset components
-- statement:
--   The alphabet is $[q]=\{0,\ldots,q-1\}$, the input space is its uniform product $[q]^n$, and $\Delta_q$ is the set of nonnegative vectors with coordinate sum one. Symbols embed as standard-basis vertices. For vector-valued $f$, the noise operator and stability are
--
--   $$K_\rho(a,b)=\rho\mathbf1_{a=b}+\frac{1-\rho}{q},\quad T_\rho f(x)=\sum_y\prod_i K_\rho(x_i,y_i)f(y),\quad S_\rho(f)=\mathbb E_x\langle f(x),T_\rho f(x)\rangle.$$
--
--   The kernel is a conditional probability for $q\ge2$ and $-1/(q-1)\le\rho\le1$. Influence averages conditional vector variance over the other input coordinates, summing over all output coordinates, as in Definition 7. This resolves the erroneous $f^i$ in Definition 20; the projection sum in Definitions 6 and 19 runs over the output dimension, rather than the printed $n$.
--
--   The subspace $X_S$ consists of functions depending only on $x_S$ and orthogonal to every proper-subset dependence space. The component $f_S$ is the genuine orthogonal projection onto $X_S$. Using the dependence spaces is equivalent to the source's recursive orthogonality to the proper-subset $X_T$, since those components span the dependence spaces. Low-degree influence is $\sum_{S\ni i,\,|S|\le k}\|f_S\|_2^2$.
--
--   **Formalization Note** Flattened Euclidean coordinates give the finite function space its unnormalized inner product. Multiplication by the positive factor $q^{-n}$ gives the uniform inner product and leaves every orthogonal projection unchanged. Uniform expectations and norm squares use that factor explicitly. The zero-dimensional cube is a point.
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), pp. 8–9,27–29, Definitions 5–7 and 16–20, §11.2 (15), Proposition 11.2

import Mathlib

namespace OptInapprox.Bal2Sat.Supplement

noncomputable section
open scoped BigOperators

abbrev QCube (q n : ℕ) := Fin n → Fin q

/-- The simplex, including its standard-basis vertices. -/
def simplex (q : ℕ) : Set (Fin q → ℝ) :=
  {a | (∀ j, 0 ≤ a j) ∧ ∑ j, a j = 1}

def basisVertex {q : ℕ} (a : Fin q) : Fin q → ℝ := fun j => if j = a then 1 else 0

/-- Uniform product expectation, also valid on the one-point zero-dimensional cube. -/
def qExpect {q n : ℕ} (f : QCube q n → ℝ) : ℝ :=
  (q ^ n : ℝ)⁻¹ * ∑ x, f x

def qDot {d : ℕ} (u v : Fin d → ℝ) : ℝ := ∑ j, u j * v j

/-- Conditional mass Kρ(a,b), not the joint mass Kρ(a,b)/q. -/
def coordKernel (q : ℕ) (ρ : ℝ) (a b : Fin q) : ℝ :=
  ρ * (if a = b then 1 else 0) + (1 - ρ) / q

def qKernel {q n : ℕ} (ρ : ℝ) (x y : QCube q n) : ℝ :=
  ∏ i, coordKernel q ρ (x i) (y i)

/-- Conditional expectation, defined without Fourier coefficients. -/
def qNoise {q n d : ℕ} (ρ : ℝ) (f : QCube q n → Fin d → ℝ) :
    QCube q n → Fin d → ℝ :=
  fun x j => ∑ y, qKernel ρ x y * f y j

/-- Expected inner product under a correlated uniform pair. -/
def qStability {q n d : ℕ} (ρ : ℝ) (f : QCube q n → Fin d → ℝ) : ℝ :=
  qExpect (fun x => ∑ y, qKernel ρ x y * qDot (f x) (f y))

def qBalanced {q n : ℕ} (f : QCube q n → Fin q → ℝ) : Prop :=
  ∀ j, qExpect (fun x => f x j) = 1 / q

/-- Expected conditional vector variance (Definition 7, resolving Definition 20's typo). -/
def qInfluence {q n d : ℕ} (f : QCube q n → Fin d → ℝ) (i : Fin n) : ℝ :=
  qExpect fun x =>
    (q : ℝ)⁻¹ * (∑ a : Fin q, qDot (f (Function.update x i a)) (f (Function.update x i a))) -
    qDot (fun j => (q : ℝ)⁻¹ * ∑ a : Fin q, f (Function.update x i a) j)
      (fun j => (q : ℝ)⁻¹ * ∑ a : Fin q, f (Function.update x i a) j)

/-- Euclidean coordinates for the finite function space. The uniform L² product differs
by the positive common factor q^(-n), which does not change orthogonal projections. -/
abbrev QSpace (q n d : ℕ) := EuclideanSpace ℝ (QCube q n × Fin d)

/-- The subspace of functions depending only on the indicated subset. -/
def dependentSpace (q n d : ℕ) (S : Finset (Fin n)) : Submodule ℝ (QSpace q n d) where
  carrier := {f | ∀ x y : QCube q n, (∀ i ∈ S, x i = y i) → ∀ j, f (x,j) = f (y,j)}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg x y h j
    simp only [Set.mem_ofPred_eq] at hf hg
    change f (x,j) + g (x,j) = f (y,j) + g (y,j)
    rw [hf x y h j, hg x y h j]
  smul_mem' := by
    intro a f hf x y h j
    simp only [Set.mem_ofPred_eq] at hf
    change a * f (x,j) = a * f (y,j)
    rw [hf x y h j]

/-- X_S: dependence on S and orthogonality to every proper-subset dependence space.
Their span equals the sum of the proper-subset X_T in the source's recursive definition. -/
def subsetSpace (q n d : ℕ) (S : Finset (Fin n)) : Submodule ℝ (QSpace q n d) :=
  dependentSpace q n d S ⊓
    (⨆ T : {T : Finset (Fin n) // T ⊂ S}, dependentSpace q n d T.val)ᗮ

/-- Genuine orthogonal projection onto X_S, not one Walsh character per subset. -/
def subsetComponent {q n d : ℕ} (f : QCube q n → Fin d → ℝ)
    (S : Finset (Fin n)) : QCube q n → Fin d → ℝ :=
  let v : QSpace q n d := WithLp.toLp 2 (fun p => f p.1 p.2)
  let w := (subsetSpace q n d S).starProjection v
  fun x j => w (x,j)

def qNormSq {q n d : ℕ} (f : QCube q n → Fin d → ℝ) : ℝ :=
  qExpect (fun x => qDot (f x) (f x))

/-- Proposition 11.2 is a definition, not an additional theorem target. -/
def qLowInfluence {q n d : ℕ} (f : QCube q n → Fin d → ℝ) (k : ℕ) (i : Fin n) : ℝ :=
  ∑ S : Finset (Fin n), if i ∈ S ∧ S.card ≤ k then qNormSq (subsetComponent f S) else 0

end
end OptInapprox.Bal2Sat.Supplement


