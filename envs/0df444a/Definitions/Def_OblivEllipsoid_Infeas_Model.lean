-- Prove2me | Definitions.Def_OblivEllipsoid_Infeas_Model
-- name    : OblivEllipsoid_Infeas_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T16:22:45.565238+00:00
-- url     : https://prove2.me/theorems/3961cf48-059f-4ade-bfcf-b5705dbcd402
-- title:
--   Assumption 1.1, (P), (Alt), (LB), the Burrell–Todd ellipsoid, OEA, and its potential
-- statement:
--   Let $A\in\mathbb R^{n\times m}$ have columns $a_i$, and let $u\in\mathbb R^m$. The primal system is $A^\top x\le u$. A type-L certificate is a vector $\lambda\ge0$ with $A\lambda=0$ and $u^\top\lambda<0$. Assumption 1.1 says that the positive cone of the columns of $A$ is all of $\mathbb R^n$ and each column has Euclidean norm one. A certified lower-bound pair $(\ell,\Lambda)$ satisfies $A\Lambda=-A$, $\Lambda\ge0$ entrywise, and $\ell\le-\Lambda^\top u$.
--
--   For $d>0$, the Burrell–Todd ellipsoid and its scale are
--   $$E(d,\ell)=\{x:(A^\top x-\ell)^\top D(A^\top x-u)\le0\},\qquad f(d,\ell)=v(\ell)^\top Dv(\ell)-t(d,\ell)^\top Dt(d,\ell),$$
--   where $D=\operatorname{diag}(d)$, $r=(u+\ell)/2$, $v=(u-\ell)/2$, $B=ADA^\top$, $y=B^{-1}ADr$, and $t=A^\top y-r$. Its slab radius is $\gamma_i=\sqrt{f a_i^\top B^{-1}a_i}$. The model also defines the Burrell–Todd lower bound $L_i=a_i^\top y-\gamma_i$, its certificate vectors from (17), the condition measure $\tau(A,u)=|\max_x\min_i(u_i-a_i^\top x)|$, and the potential $\phi$ of page 21.
--
--   Algorithm 4 and Procedures 2–3 are relations recording every result the paper permits. A state contains $(d,\ell,\Lambda)$; one pass yields a feasible point, a type-L certificate, or a next state. The reachability relation counts completed passes that reach Step 12. This common model makes the convergence theorem and its milestones statements about the same algorithm.
--
--   **Formalization Note** The paper's $[m]=\{1,\dots,m\}$ is `Fin m`; $e_j$ is `Pi.single j 1`. Euclidean norms are expressed by sums of squares because the Lean function type carries a sup norm. Matrix inverses, square roots, logarithms, and real suprema are total in Lean; their valid domains are supplied by the theorem hypotheses and algorithm guards.
-- source:
--   Lamperski, Freund & Todd, An Oblivious Ellipsoid Algorithm for Solving a System of (In)Feasible Linear Inequalities, arXiv:1910.03114v5, pp. 2–22, §1, §3, §4, Procedure 2 (p. 16), Procedure 3 (p. 17), Algorithm 4 (p. 20), potential (p. 21)

import Mathlib

open Matrix

namespace OblivEllipsoid.Infeas

variable {n m : ℕ}

/-- The column aᵢ of the constraint matrix. -/
def col (A : Matrix (Fin n) (Fin m) ℝ) (i : Fin m) : Fin n → ℝ := fun k => A k i

/-- Assumption 1.1: positive conic spanning and unit Euclidean columns. -/
def Assumption11 (A : Matrix (Fin n) (Fin m) ℝ) : Prop :=
  (∀ x : Fin n → ℝ, ∃ lam : Fin m → ℝ, 0 ≤ lam ∧ A *ᵥ lam = x) ∧
  (∀ i : Fin m, ∑ k : Fin n, A k i ^ 2 = 1)

/-- The primal system (P). -/
def IsFeasible (A : Matrix (Fin n) (Fin m) ℝ) (u : Fin m → ℝ)
    (x : Fin n → ℝ) : Prop := Aᵀ *ᵥ x ≤ u

/-- The alternative system (Alt), a type-L certificate. -/
def IsAlt (A : Matrix (Fin n) (Fin m) ℝ) (u lam : Fin m → ℝ) : Prop :=
  A *ᵥ lam = 0 ∧ 0 ≤ lam ∧ u ⬝ᵥ lam < 0

/-- A certified lower bound on one constraint, (LB i). -/
def CertLBi (A : Matrix (Fin n) (Fin m) ℝ) (u : Fin m → ℝ)
    (i : Fin m) (li : ℝ) (lam : Fin m → ℝ) : Prop :=
  A *ᵥ lam = -(col A i) ∧ 0 ≤ lam ∧ li ≤ -(lam ⬝ᵥ u)

/-- A vector of certified lower bounds, (LB). -/
def CertLB (A : Matrix (Fin n) (Fin m) ℝ) (u ell : Fin m → ℝ)
    (Lam : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  A * Lam = -A ∧ (∀ i j, 0 ≤ Lam i j) ∧ ell ≤ -(Lamᵀ *ᵥ u)

/-- Midpoint r(ℓ) of the lower and upper bounds. -/
noncomputable def r (u ell : Fin m → ℝ) : Fin m → ℝ := (1 / 2 : ℝ) • (u + ell)
/-- Half-width v(ℓ). -/
noncomputable def v (u ell : Fin m → ℝ) : Fin m → ℝ := (1 / 2 : ℝ) • (u - ell)
/-- B(d) = A D Aᵀ. -/
def B (A : Matrix (Fin n) (Fin m) ℝ) (d : Fin m → ℝ) :
    Matrix (Fin n) (Fin n) ℝ := A * diagonal d * Aᵀ
/-- The ellipsoid centre. -/
noncomputable def y (A : Matrix (Fin n) (Fin m) ℝ) (u d ell : Fin m → ℝ) :
    Fin n → ℝ := (B A d)⁻¹ *ᵥ (A *ᵥ (d * r u ell))
/-- The centre's residual. -/
noncomputable def t (A : Matrix (Fin n) (Fin m) ℝ) (u d ell : Fin m → ℝ) :
    Fin m → ℝ := Aᵀ *ᵥ y A u d ell - r u ell
/-- The squared ellipsoid scale f(d,ℓ). -/
noncomputable def f (A : Matrix (Fin n) (Fin m) ℝ) (u d ell : Fin m → ℝ) : ℝ :=
  (∑ i : Fin m, d i * (v u ell i) ^ 2) -
  (∑ i : Fin m, d i * (t A u d ell i) ^ 2)
/-- The Burrell–Todd ellipsoid (12). -/
def E (A : Matrix (Fin n) (Fin m) ℝ) (u d ell : Fin m → ℝ) :
    Set (Fin n → ℝ) :=
  {x | ∑ i : Fin m, d i * ((Aᵀ *ᵥ x) i - ell i) * ((Aᵀ *ᵥ x) i - u i) ≤ 0}
/-- Closed form (14) for the slab radius. -/
noncomputable def slabRadius (A : Matrix (Fin n) (Fin m) ℝ)
    (u d ell : Fin m → ℝ) (i : Fin m) : ℝ :=
  Real.sqrt (f A u d ell * (col A i ⬝ᵥ ((B A d)⁻¹ *ᵥ col A i)))
/-- The strengthened lower bound Lᵢ. -/
noncomputable def Lb (A : Matrix (Fin n) (Fin m) ℝ)
    (u d ell : Fin m → ℝ) (i : Fin m) : ℝ :=
  col A i ⬝ᵥ y A u d ell - slabRadius A u d ell i
/-- The vector λ̂ᵢ in (17). -/
noncomputable def lamHat (A : Matrix (Fin n) (Fin m) ℝ)
    (u d ell : Fin m → ℝ) (i : Fin m) : Fin m → ℝ :=
  slabRadius A u d ell i • (d * t A u d ell) -
    d * (Aᵀ *ᵥ ((B A d)⁻¹ *ᵥ col A i))
def posPart (w : Fin m → ℝ) : Fin m → ℝ := fun k => max (w k) 0
def negPart (w : Fin m → ℝ) : Fin m → ℝ := fun k => max (-w k) 0
/-- The vector λ̃ᵢ in (17). -/
noncomputable def lamTilde (A : Matrix (Fin n) (Fin m) ℝ)
    (u d ell : Fin m → ℝ) (Lam : Matrix (Fin m) (Fin m) ℝ)
    (i : Fin m) : Fin m → ℝ :=
  Lam *ᵥ negPart (lamHat A u d ell i) + posPart (lamHat A u d ell i)

/-- Maximin slack z*, equation (15). -/
noncomputable def zStar (A : Matrix (Fin n) (Fin m) ℝ) (u : Fin m → ℝ) : ℝ :=
  sSup (Set.range fun x : Fin n → ℝ => ⨅ i : Fin m, (u i - col A i ⬝ᵥ x))
/-- Condition measure τ(A,u), equation (15). -/
noncomputable def tau (A : Matrix (Fin n) (Fin m) ℝ) (u : Fin m → ℝ) : ℝ :=
  |zStar A u|
/-- The factor μᵢ of the potential. -/
noncomputable def mu (A : Matrix (Fin n) (Fin m) ℝ)
    (u d ell : Fin m → ℝ) (i : Fin m) : ℝ :=
  max ((d i / f A u d ell) ^ (-(1 / 2 : ℝ)))
    (((m : ℝ) / ((m : ℝ) + 1)) * tau A u)
/-- The potential φ on page 21. -/
noncomputable def potential (A : Matrix (Fin n) (Fin m) ℝ)
    (u d ell : Fin m → ℝ) : ℝ := ∏ i : Fin m, mu A u d ell i

/-- The lower-bound update (18). -/
noncomputable def ell1 (A : Matrix (Fin n) (Fin m) ℝ)
    (u d ell : Fin m → ℝ) (j : Fin m) : Fin m → ℝ :=
  ell - (2 * (t A u d ell j - v u ell j) /
    (d j * slabRadius A u d ell j ^ 2)) • Pi.single j 1
/-- The rescaling (21). -/
noncomputable def d1 (A : Matrix (Fin n) (Fin m) ℝ)
    (u d ell : Fin m → ℝ) (j : Fin m) : Fin m → ℝ :=
  (1 / f A u d (ell1 A u d ell j)) • d
/-- The lower-bound update (22). -/
noncomputable def ell2 (A : Matrix (Fin n) (Fin m) ℝ)
    (u d ell : Fin m → ℝ) (j : Fin m) : Fin m → ℝ :=
  let e1 := ell1 A u d ell j
  let dd1 := d1 A u d ell j
  e1 + (2 * (2 * v u e1 j - slabRadius A u dd1 e1 j) /
    (((m : ℝ) - 1) * dd1 j * slabRadius A u dd1 e1 j ^ 2 + 2)) • Pi.single j 1
/-- The d update (23). -/
noncomputable def d2 (A : Matrix (Fin n) (Fin m) ℝ)
    (u d ell : Fin m → ℝ) (j : Fin m) : Fin m → ℝ :=
  let e1 := ell1 A u d ell j
  let dd1 := d1 A u d ell j
  dd1 + ((2 / ((m : ℝ) - 1)) *
    (1 / slabRadius A u dd1 e1 j ^ 2)) • Pi.single j 1
/-- Final rescaling (24). -/
noncomputable def d3 (A : Matrix (Fin n) (Fin m) ℝ)
    (u d ell : Fin m → ℝ) (j : Fin m) : Fin m → ℝ :=
  (1 / f A u (d2 A u d ell j) (ell2 A u d ell j)) • d2 A u d ell j

structure State (m : ℕ) where
  d : Fin m → ℝ
  ell : Fin m → ℝ
  Lam : Matrix (Fin m) (Fin m) ℝ

inductive Outcome (n m : ℕ)
  | solution (x : Fin n → ℝ)
  | certificate (lam : Fin m → ℝ)
  | next (s : State m)

/-- Replace exactly one certificate column. -/
def replaceColumn (Lam : Matrix (Fin m) (Fin m) ℝ)
    (j : Fin m) (w : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun row k => if k = j then w row else Lam row k

/-- Every possible output of Procedure 2, including all specified choices. -/
noncomputable def Proc2 (A : Matrix (Fin n) (Fin m) ℝ)
    (u d ell : Fin m → ℝ) (Lam : Matrix (Fin m) (Fin m) ℝ)
    (out : Fin m → ℝ) : Prop :=
  (¬ ell ≤ u ∧ ∃ j : Fin m, u j < ell j ∧ out = Lam.col j + Pi.single j 1) ∨
  (ell ≤ u ∧ ∃ (i : Fin m) (beta : ℝ), 0 ≤ beta ∧
    f A u d (ell - beta • Pi.single i 1) = 0 ∧
    let e1 := ell - beta • Pi.single i 1
    ∃ (j k : Fin m) (epsilon : ℝ),
      col A j ⬝ᵥ y A u d e1 ≤ u j ∧
      u k < col A k ⬝ᵥ y A u d e1 ∧
      0 < epsilon ∧
      0 < f A u d (e1 - epsilon • Pi.single j 1) ∧
      u k < Lb A u d (e1 - epsilon • Pi.single j 1) k ∧
      let e2 := e1 - epsilon • Pi.single j 1
      let dd := (1 / f A u d e2) • d
      out = lamTilde A u dd e2 Lam k + Pi.single k 1)

/-- Procedure 3, with its ordered tests and return values. -/
noncomputable def Proc3 (A : Matrix (Fin n) (Fin m) ℝ)
    (u d ell : Fin m → ℝ) (Lam : Matrix (Fin m) (Fin m) ℝ)
    (j : Fin m) (o : Outcome n m) : Prop :=
  let e1 := ell1 A u d ell j
  (IsFeasible A u (y A u d e1) ∧ o = .solution (y A u d e1)) ∨
  (¬ IsFeasible A u (y A u d e1) ∧ f A u d e1 ≤ 0 ∧
    ∃ lam, Proc2 A u d e1 Lam lam ∧ o = .certificate lam) ∨
  (¬ IsFeasible A u (y A u d e1) ∧ 0 < f A u d e1 ∧
    o = .next ⟨d3 A u d ell j, ell2 A u d ell j, Lam⟩)

/-- A full pass through Algorithm 4, with every choice left open. -/
noncomputable def OEAIter (A : Matrix (Fin n) (Fin m) ℝ)
    (u : Fin m → ℝ) (s : State m) (o : Outcome n m) : Prop :=
  (IsFeasible A u (y A u s.d s.ell) ∧ o = .solution (y A u s.d s.ell)) ∨
  (¬ IsFeasible A u (y A u s.d s.ell) ∧ f A u s.d s.ell ≤ 0 ∧
    ∃ lam, Proc2 A u s.d s.ell s.Lam lam ∧ o = .certificate lam) ∨
  (¬ IsFeasible A u (y A u s.d s.ell) ∧ 0 < f A u s.d s.ell ∧
    let dd := (1 / f A u s.d s.ell) • s.d
    ∃ j : Fin m,
      (∀ i : Fin m, col A i ⬝ᵥ y A u dd s.ell - u i ≤
        col A j ⬝ᵥ y A u dd s.ell - u j) ∧
      let Lj := Lb A u dd s.ell j
      let Lam' := if s.ell j < Lj then
        replaceColumn s.Lam j (lamTilde A u dd s.ell s.Lam j) else s.Lam
      (u j < Lj ∧ o = .certificate (Lam'.col j + Pi.single j 1)) ∨
      (Lj ≤ u j ∧ Proc3 A u dd s.ell Lam' j o))

/-- States after k completed, nonterminal passes of Algorithm 4. -/
inductive Reach (A : Matrix (Fin n) (Fin m) ℝ) (u : Fin m → ℝ)
    (s0 : State m) : ℕ → State m → Prop
  | zero : Reach A u s0 0 s0
  | succ {k : ℕ} {s s' : State m} :
      Reach A u s0 k s → OEAIter A u s (.next s') → Reach A u s0 (k + 1) s'

end OblivEllipsoid.Infeas


