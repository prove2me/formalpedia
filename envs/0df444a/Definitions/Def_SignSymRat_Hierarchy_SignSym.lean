-- Prove2me | Definitions.Def_SignSymRat_Hierarchy_SignSym
-- name    : SignSymRat_Hierarchy_SignSym
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:06:56.127972+00:00
-- url     : https://prove2.me/theorems/020fc4d6-7197-4bc1-ad21-135009749b83
-- title:
--   Definition 4.1 and the sign-symmetric dual
-- statement:
--   A monomial exponent $\alpha\in\mathbb N^n$ pairs with a sign vector $r\in\{0,1\}^n$ by $r^T\alpha$ modulo $2$. For finite $A$, the sign-symmetry group and its closure are
--
--   $$R(A)=\{r:r^T\alpha=0\pmod2\ \forall\alpha\in A\},\qquad \bar A=\{\alpha:r^T\alpha=0\pmod2\ \forall r\in R(A)\}.$$
--
--   The action $\theta_r$ replaces each $x_a$ with $(-1)^{r_a}x_a$. The support sets $A_i$ are exactly (4.1)–(4.2). Program (SD) restricts each auxiliary polynomial $h_i$ to $\mathbb R[\bar A_i]$ and uses the ratio inequalities on $K$. This is the untruncated sign-symmetric comparison value $\rho^s$.
--
--   **Formalization Note** The paper's $i=1$ is Lean's `0`; $i\ne0$ denotes every other ratio. A sign vector is represented in `ZMod 2`. The value $\rho^s$ is extended real, with value $-\infty$ if the program is infeasible.
-- source:
--   Guo, Wang & Zheng, Exploiting Sign Symmetries in Minimizing Sums of Rational Functions, arXiv:2405.09419v1, p. 10, Definition 4.1, (4.1), (4.2), (SD)

import Mathlib
import Definitions.Def_SignSymRat_Hierarchy_Setting

open MvPolynomial

namespace SignSymRat.Hierarchy

variable {n m N : ℕ}

/-- The mod-two pairing of a sign vector and a monomial exponent. -/
def pair (r : Fin n → ZMod 2) (α : Fin n →₀ ℕ) : ZMod 2 :=
  ∑ i : Fin n, r i * (α i : ZMod 2)

/-- Definition 4.1: the sign symmetries R(A). -/
def signSym (A : Finset (Fin n →₀ ℕ)) : Finset (Fin n → ZMod 2) :=
  Finset.univ.filter fun r => ∀ α ∈ A, pair r α = 0

/-- Definition 4.1: the symmetry closure A-bar. -/
def symClosure (A : Finset (Fin n →₀ ℕ)) : Set (Fin n →₀ ℕ) :=
  {α | ∀ r ∈ signSym A, pair r α = 0}

/-- The sign-substitution map θ_r on polynomials. -/
noncomputable def theta (r : Fin n → ZMod 2)
    (f : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  aeval (fun i => C ((-1 : ℝ) ^ (r i).val) * X i) f

/-- Coordinate sign reversal r(a). -/
def flip (r : Fin n → ZMod 2) (a : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (-1 : ℝ) ^ (r i).val * a i

/-- Membership in ℝ[S]: every support exponent belongs to S. -/
def SupportedIn (S : Set (Fin n →₀ ℕ))
    (f : MvPolynomial (Fin n) ℝ) : Prop :=
  (f.support : Set (Fin n →₀ ℕ)) ⊆ S

/-- Formula (4.1), used for every non-distinguished ratio. -/
def SRFO.Arest (P : SRFO n m N) (i : Fin N) : Finset (Fin n →₀ ℕ) :=
  (P.p i).support ∪ (P.q i).support ∪
    Finset.univ.biUnion (fun j : Fin m => (P.g j).support)

/-- Formula (4.2) at index zero, formula (4.1) elsewhere. -/
def SRFO.Aset (P : SRFO n m N) [NeZero N] (i : Fin N) :
    Finset (Fin n →₀ ℕ) :=
  if i = 0 then
    (P.p 0).support ∪ (P.q 0).support ∪
      (Finset.univ.erase (0 : Fin N)).biUnion P.Arest
  else P.Arest i

/-- The average of the θ_r transforms over R(A). -/
noncomputable def symAvg (A : Finset (Fin n →₀ ℕ))
    (f : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  ((1 : ℝ) / (signSym A).card) • ∑ r ∈ signSym A, theta r f

/-- Feasibility in the sign-symmetric polynomial dual (SD). -/
def SRFO.SFeasible (P : SRFO n m N) [NeZero N]
    (c : ℝ) (h : Fin N → MvPolynomial (Fin n) ℝ) : Prop :=
  (∀ x ∈ P.K,
    c ≤ eval x (P.p 0) / eval x (P.q 0) +
      ∑ i ∈ Finset.univ.erase (0 : Fin N), eval x (h i)) ∧
  (∀ i : Fin N, i ≠ 0 →
    (∀ x ∈ P.K, eval x (h i) ≤ eval x (P.p i) / eval x (P.q i)) ∧
    SupportedIn (symClosure (P.Aset i)) (h i))

/-- The value ρˢ of (SD), including infeasibility. -/
noncomputable def SRFO.rhoS (P : SRFO n m N) [NeZero N] : EReal :=
  sSup ((fun c : ℝ => (c : EReal)) '' {c | ∃ h, P.SFeasible c h})

end SignSymRat.Hierarchy


