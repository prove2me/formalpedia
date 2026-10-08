-- Prove2me | Definitions.Def_RobustUncLP_Ellipsoidal_Setting
-- name    : RobustUncLP_Ellipsoidal_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T11:49:58.620187+00:00
-- url     : https://prove2.me/theorems/6210625e-da65-450e-863b-f35aeb04ca28
-- title:
--   §2.1, §3.1, pp. 3–8 — uncertain LP (6), robust feasible set (12), ellipsoids (14), ellipsoidal uncertainty: conditions A, B, C
-- statement:
--   This file fixes the objects of Section 3 of Ben-Tal and Nemirovski's *Robust solutions of uncertain linear programs*.
--
--   **Uncertain LP and robust feasibility.** An uncertain linear program in the form (6) is
--   $$\min\{c^Tx \mid Ax \ge 0,\ f^Tx = 1\},$$
--   with fixed $c, f \in \mathbb R^n$ and a data matrix $A \in \mathbb R^{m\times n}$ known only to lie in an **uncertainty set** $\mathcal U \subseteq \mathbb R^{m\times n}$. The feasible set of the instance with data $A$ is $\{x \mid Ax \ge 0,\ f^Tx = 1\}$. A point $x$ is **robust feasible** (r-feasible) if it is feasible for every instance:
--   $$G_{\mathcal U} = \{x \in \mathbb R^n \mid Ax \ge 0 \ \ \forall A \in \mathcal U,\ \ f^Tx = 1\}. \tag{12}$$
--
--   **Euclidean norm.** For $v \in \mathbb R^M$, $\|v\| = \sqrt{v_1^2 + \dots + v_M^2}$.
--
--   **Ellipsoids.** For an affine map $\Pi : \mathbb R^L \to \mathbb R^{m\times n}$, $\Pi(u) = P^0 + \sum_{j=1}^L u_j P^j$, and an $M\times L$ matrix $Q$, the ellipsoid (14) is
--   $$U(\Pi, Q) = \{\Pi(u) \mid \|Qu\| \le 1\}.$$
--   A singular $Q$ gives an "ellipsoidal cylinder".
--
--   **Ellipsoidal uncertainty.** The data $(\Pi_\ell, Q_\ell)$, $\ell = 0, \dots, k$, define
--   $$\mathcal U = \bigcap_{\ell=0}^k U(\Pi_\ell, Q_\ell) \qquad \text{(condition A, (15))}.$$
--   Condition B says that $\mathcal U$ is bounded, and condition C (the "Slater condition") that some matrix $A$ satisfies, for every $\ell$, $A = \Pi_\ell(u^\ell)$ for some $u^\ell$ with $\|Q_\ell u^\ell\| < 1$.
--
--   These are the hypotheses of Theorem 3.1 and of the Appendix's claims (I)–(III).
--
--   **Formalization Note** Indices $\ell = 0,\dots,k$ are `Fin (k + 1)`. `euclidNorm` writes the Euclidean norm out because Mathlib's norm on `Fin M → ℝ` is the sup norm. The map $\Pi_\ell$ need not be injective: the page says "affine embedding", but nothing uses injectivity, so dropping it generalizes. Boundedness of a set of matrices (`UncBounded`) is a uniform bound on all entries, which is equivalent to boundedness in any norm on $\mathbb R^{m\times n}$. Condition C is required for every $\ell = 0,\dots,k$. The page's words say "$\ell = 1,\dots,k$" while its display says "$\forall \ell \le k$", and the Appendix's use of (II) needs every $\ell = 0, \dots, k$.
-- source:
--   Ben-Tal & Nemirovski, Robust solutions of uncertain linear programs, Oper. Res. Lett. 25 (1999); authors' manuscript, p. 3 (6), p. 4 (12), p. 7 (14), p. 8 (15) and conditions A, B, C

import Mathlib
import Definitions.Def_RobustUncLP_WorstCase_Setting

namespace RobustUncLP.Ellipsoidal

open Matrix

/-- The Euclidean norm `‖v‖ = √(vᵀv)` of `v ∈ ℝ^M`. Written out because the norm Mathlib puts
on `Fin M → ℝ` is the sup norm; every `‖·‖` of Ben-Tal & Nemirovski (1999) is Euclidean
(p. 7, after (13)). -/
noncomputable def euclidNorm {M : ℕ} (v : Fin M → ℝ) : ℝ :=
  Real.sqrt (∑ j, v j ^ 2)

/-- Feasible set of one instance of the uncertain LP (6), p. 3:
`{x | Ax ≥ 0, fᵀx = 1}` for the data matrix `A`. -/
def instFeas {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (f : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ (A *ᵥ x) i) ∧ f ⬝ᵥ x = 1}

/-- A set of `m × n` matrices is bounded (condition B, p. 8): all entries of all its members
are bounded by one constant. -/
def UncBounded {m n : ℕ} (U : Set (Matrix (Fin m) (Fin n) ℝ)) : Prop :=
  ∃ C : ℝ, ∀ A ∈ U, ∀ a b, |A a b| ≤ C

/-- The data of an ellipsoidal uncertainty (15), p. 8: for `ℓ = 0, …, k` an affine map
`Π_ℓ : ℝ^{L_ℓ} → ℝ^{m×n}`, `Π_ℓ(u) = P0 ℓ + ∑_j u_j • P ℓ j`, and an `M_ℓ × L_ℓ` matrix `Q_ℓ`. -/
structure EllipsoidalData (m n k : ℕ) where
  /-- `L ℓ`: dimension of the parameter space of `Π_ℓ`. -/
  L : Fin (k + 1) → ℕ
  /-- `M ℓ`: number of rows of `Q_ℓ`. -/
  M : Fin (k + 1) → ℕ
  /-- Constant term of the affine map `Π_ℓ`. -/
  P0 : Fin (k + 1) → Matrix (Fin m) (Fin n) ℝ
  /-- Coefficient matrices of the affine map `Π_ℓ`. -/
  P : (ℓ : Fin (k + 1)) → Fin (L ℓ) → Matrix (Fin m) (Fin n) ℝ
  /-- The matrix `Q_ℓ`. -/
  Q : (ℓ : Fin (k + 1)) → Matrix (Fin (M ℓ)) (Fin (L ℓ)) ℝ

namespace EllipsoidalData

variable {m n k : ℕ}

/-- The affine map `Π_ℓ(u) = P0_ℓ + ∑_j u_j P_ℓ^j`. -/
def Pi (D : EllipsoidalData m n k) (ℓ : Fin (k + 1)) (u : Fin (D.L ℓ) → ℝ) :
    Matrix (Fin m) (Fin n) ℝ :=
  D.P0 ℓ + ∑ j, u j • D.P ℓ j

/-- The ellipsoid (14), p. 7: `U(Π_ℓ, Q_ℓ) = {Π_ℓ(u) | ‖Q_ℓ u‖ ≤ 1}`. -/
def ellipsoid (D : EllipsoidalData m n k) (ℓ : Fin (k + 1)) :
    Set (Matrix (Fin m) (Fin n) ℝ) :=
  {A | ∃ u, A = D.Pi ℓ u ∧ euclidNorm (D.Q ℓ *ᵥ u) ≤ 1}

/-- Condition A, (15), p. 8: `𝒰 = ⋂_{ℓ=0}^k U(Π_ℓ, Q_ℓ)`. -/
def uncSet (D : EllipsoidalData m n k) : Set (Matrix (Fin m) (Fin n) ℝ) :=
  ⋂ ℓ, D.ellipsoid ℓ

/-- Condition C ("Slater condition"), p. 8, read for every `ℓ = 0, …, k`: one matrix `A` is
`Π_ℓ(u^ℓ)` with `‖Q_ℓ u^ℓ‖ < 1` for every `ℓ`. -/
def SlaterC (D : EllipsoidalData m n k) : Prop :=
  ∃ A : Matrix (Fin m) (Fin n) ℝ, ∀ ℓ, ∃ u, A = D.Pi ℓ u ∧ euclidNorm (D.Q ℓ *ᵥ u) < 1

end EllipsoidalData

end RobustUncLP.Ellipsoidal


