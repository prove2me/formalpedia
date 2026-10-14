-- Prove2me | Definitions.Def_AdaptDRO_LiftedLDR_Model
-- name    : AdaptDRO_LiftedLDR_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T18:47:45.254229+00:00
-- url     : https://prove2.me/theorems/11e1df7e-3083-45f6-b9cc-86501fc8f27d
-- title:
--   Affine recourse data, SOC ambiguity sets, lifted support, decision rules, and values
-- statement:
--   The paper's two-stage model has affine first-stage constraint data $A(z)=A^0+\sum_i A^i z_i$ and $b(z)=b^0+\sum_i b^i z_i$, a fixed free-variable recourse LP with matrix $B$ and cost $d$, and a support set $W\subseteq\mathbb R^{I_1}$. For a first-stage vector $x$, $Q(x,z)$ is the minimum recourse cost subject to $A(z)x+By\ge b(z)$.
--
--   An **SOC ambiguity set** $F$ consists of probability laws $P$ supported on $W$ with $\mathbb E_P[Gz]=\mu$ and $\mathbb E_P[g_i(z)]\le\sigma_i$. The support $W$ and each epigraph of $g_i$ are representable as projections of affine inverse images of Cartesian products of second-order cones. Each $g_i$ is measurable and bounded on compact sets. The **lifted support** and ambiguity set are
--
--   $$
--   \bar W=\{(z,u):z\in W,\ g(z)\le u\},\qquad
--   \mathcal G=\{P:P(\bar W)=1,\ \mathbb E_P[Gz]=\mu,\ \mathbb E_P[u]\le\sigma\}.
--   $$
--
--   Assumption 1 requires a conic representation of this same $\bar W$ and a Slater point $(z^\dagger,u^\dagger,v^\dagger)$ satisfying $Gz^\dagger=\mu$, $u^\dagger<\sigma$, and strict cone membership. A regular affine rule is $y(z)=y^0+Y^1z$; an extended rule is $y(z,u)=y^0+Y^1z+Y^2u$. Both are feasible only when their recourse constraints hold at every point of their respective supports. The four values $\beta(x)$, $\beta_L(x)$, $\beta_E(x)$, and the robust program (9) are respectively a worst-case expectation, two infima over feasible rule classes, and an infimum over feasible robust certificates.
--
--   **Formalization Note** Every law in $F$ has integrable primary coordinates and integrable $g_i$; every law in $\mathcal G$ has integrable primary and auxiliary coordinates. The paper does not state all these finite-moment conditions explicitly. Lean uses extended-real suprema and infima for the four optimization values, so an empty feasible rule class has value $+\infty$. The recourse value itself is real only in the theorems under their feasibility hypotheses. Finite vectors use zero-based `Fin` indices for the paper's one-based indices.
-- source:
--   Bertsimas, Sim, Zhang, Adaptive distributionally robust optimization, Management Science 65(2) (2019), pp. 606–609, Eqs. (1), (2), (4), (6)–(9), (12), (15), Definitions 1–3, Assumption 1

import Mathlib
import Definitions.Def_AdaptDRO_LiftedLDR_RecourseLP

namespace AdaptDRO.LiftedLDR

open MeasureTheory

/-- A Cartesian product of Lorentz cones, allowing one-coordinate nonnegative rays. -/
def IsSOCProduct {L : ℕ} (K : Set (Fin L → ℝ)) : Prop :=
  ∃ (J : ℕ) (block : Fin L → Fin J) (head : Fin J → Fin L),
    (∀ j, block (head j) = j) ∧
    K = {w | ∀ j : Fin J,
      Real.sqrt (∑ i ∈ Finset.univ.filter (fun i => block i = j ∧ i ≠ head j),
        (w i) ^ 2) ≤ w (head j)}

/-- Projection of an affine inverse image of a product of second-order cones. -/
def IsSOCRepresentable {n : ℕ} (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (k L : ℕ) (C : Matrix (Fin L) (Fin n) ℝ)
    (E : Matrix (Fin L) (Fin k) ℝ) (h : Fin L → ℝ)
    (K : Set (Fin L → ℝ)),
    IsSOCProduct K ∧
    S = {z | ∃ v : Fin k → ℝ, h - (C.mulVec z + E.mulVec v) ∈ K}

/-- SOC representation of the epigraph of a scalar function. -/
def IsSOCEpigraph {n : ℕ} (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (k L : ℕ) (C : Matrix (Fin L) (Fin n) ℝ)
    (D : Matrix (Fin L) (Fin 1) ℝ)
    (E : Matrix (Fin L) (Fin k) ℝ) (h : Fin L → ℝ)
    (K : Set (Fin L → ℝ)),
    IsSOCProduct K ∧
    {zu : (Fin n → ℝ) × ℝ | g zu.1 ≤ zu.2} =
      {zu | ∃ v : Fin k → ℝ,
        h - (C.mulVec zu.1 + D.mulVec (fun _ => zu.2) + E.mulVec v) ∈ K}

/-- The affine two-stage data and Definition 3's moment and support data. -/
structure Model (I1 I2 L1 M N1 N2 : ℕ) where
  A0 : Matrix (Fin M) (Fin N1) ℝ
  A : Fin I1 → Matrix (Fin M) (Fin N1) ℝ
  b0 : Fin M → ℝ
  b : Fin I1 → Fin M → ℝ
  recourse : RecourseLP M N2
  G : Matrix (Fin L1) (Fin I1) ℝ
  mu : Fin L1 → ℝ
  sigma : Fin I2 → ℝ
  W : Set (Fin I1 → ℝ)
  g : Fin I2 → (Fin I1 → ℝ) → ℝ

variable {I1 I2 L1 M N1 N2 : ℕ}

noncomputable def Model.Amat (m : Model I1 I2 L1 M N1 N2)
    (z : Fin I1 → ℝ) : Matrix (Fin M) (Fin N1) ℝ :=
  m.A0 + ∑ i, z i • m.A i

noncomputable def Model.bvec (m : Model I1 I2 L1 M N1 N2)
    (z : Fin I1 → ℝ) : Fin M → ℝ :=
  m.b0 + ∑ i, z i • m.b i

noncomputable def Model.rhs (m : Model I1 I2 L1 M N1 N2)
    (x : Fin N1 → ℝ) (z : Fin I1 → ℝ) : Fin M → ℝ :=
  m.bvec z - (m.Amat z).mulVec x

noncomputable def Model.Q (m : Model I1 I2 L1 M N1 N2)
    (x : Fin N1 → ℝ) (z : Fin I1 → ℝ) : ℝ :=
  m.recourse.value (m.rhs x z)

/-- Definition 3's standing SOC and regularity assumptions. -/
def Model.SOCData (m : Model I1 I2 L1 M N1 N2) : Prop :=
  IsSOCRepresentable m.W ∧
  ∀ i : Fin I2,
    Measurable (m.g i) ∧
    (∀ S : Set (Fin I1 → ℝ), IsCompact S → Bornology.IsBounded ((m.g i) '' S)) ∧
    IsSOCEpigraph (m.g i)

def Model.RelativelyComplete (m : Model I1 I2 L1 M N1 N2)
    (X : Set (Fin N1 → ℝ)) : Prop :=
  ∀ x ∈ X, ∀ z ∈ m.W, m.recourse.Feasible (m.rhs x z)

def Model.gvec (m : Model I1 I2 L1 M N1 N2)
    (z : Fin I1 → ℝ) : Fin I2 → ℝ := fun i => m.g i z

/-- The lifted support (7), derived from `W` and `g`. -/
def Model.liftedSupport (m : Model I1 I2 L1 M N1 N2) :
    Set ((Fin I1 → ℝ) × (Fin I2 → ℝ)) :=
  {zu | zu.1 ∈ m.W ∧ m.gvec zu.1 ≤ zu.2}

/-- The SOC ambiguity set (4), with all coordinates and `gᵢ` integrable. -/
def Model.ambF (m : Model I1 I2 L1 M N1 N2) :
    Set (Measure (Fin I1 → ℝ)) :=
  {P | IsProbabilityMeasure P ∧
    (∀ i : Fin I1, Integrable (fun z : Fin I1 → ℝ => z i) P) ∧
    (∀ l : Fin L1, (∫ z, (m.G.mulVec z) l ∂P) = m.mu l) ∧
    (∀ i : Fin I2, Integrable (m.g i) P ∧ (∫ z, m.g i z ∂P) ≤ m.sigma i) ∧
    (∀ᵐ z ∂P, z ∈ m.W)}

/-- The lifted ambiguity set (6), with integrable primary and auxiliary coordinates. -/
def Model.liftedAmb (m : Model I1 I2 L1 M N1 N2) :
    Set (Measure ((Fin I1 → ℝ) × (Fin I2 → ℝ))) :=
  {P | IsProbabilityMeasure P ∧
    (∀ i : Fin I1, Integrable (fun zu : (Fin I1 → ℝ) × (Fin I2 → ℝ) => zu.1 i) P) ∧
    (∀ i : Fin I2, Integrable (fun zu : (Fin I1 → ℝ) × (Fin I2 → ℝ) => zu.2 i) P) ∧
    (∀ l : Fin L1, (∫ zu, (m.G.mulVec zu.1) l ∂P) = m.mu l) ∧
    (∀ i : Fin I2, (∫ zu, zu.2 i ∂P) ≤ m.sigma i) ∧
    (∀ᵐ zu ∂P, zu ∈ m.liftedSupport)}

/-- Assumption 1: (8) represents the actual lifted support, with a strict Slater point. -/
def Model.Assumption1 (m : Model I1 I2 L1 M N1 N2)
    {I3 L2 : ℕ} (C : Matrix (Fin L2) (Fin I1) ℝ)
    (D : Matrix (Fin L2) (Fin I2) ℝ)
    (E : Matrix (Fin L2) (Fin I3) ℝ)
    (h : Fin L2 → ℝ) (K : Set (Fin L2 → ℝ)) : Prop :=
  IsSOCProduct K ∧
  m.liftedSupport =
    {zu | ∃ v : Fin I3 → ℝ,
      h - (C.mulVec zu.1 + D.mulVec zu.2 + E.mulVec v) ∈ K} ∧
  ∃ (z : Fin I1 → ℝ) (u : Fin I2 → ℝ) (v : Fin I3 → ℝ),
    m.G.mulVec z = m.mu ∧ (∀ i : Fin I2, u i < m.sigma i) ∧
    h - (C.mulVec z + D.mulVec u + E.mulVec v) ∈ interior K

structure ClassicalRule (I1 N : ℕ) where
  y0 : Fin N → ℝ
  Y1 : Matrix (Fin N) (Fin I1) ℝ

def ClassicalRule.eval {I1 N : ℕ} (y : ClassicalRule I1 N)
    (z : Fin I1 → ℝ) : Fin N → ℝ := y.y0 + y.Y1.mulVec z

structure ExtendedRule (I1 I2 N : ℕ) where
  y0 : Fin N → ℝ
  Y1 : Matrix (Fin N) (Fin I1) ℝ
  Y2 : Matrix (Fin N) (Fin I2) ℝ

def ExtendedRule.eval {I1 I2 N : ℕ} (y : ExtendedRule I1 I2 N)
    (z : Fin I1 → ℝ) (u : Fin I2 → ℝ) : Fin N → ℝ :=
  y.y0 + y.Y1.mulVec z + y.Y2.mulVec u

def Model.ClassicalFeasible (m : Model I1 I2 L1 M N1 N2)
    (x : Fin N1 → ℝ) (y : ClassicalRule I1 N2) : Prop :=
  ∀ z ∈ m.W, m.bvec z ≤ (m.Amat z).mulVec x + m.recourse.B.mulVec (y.eval z)

def Model.ExtendedFeasible (m : Model I1 I2 L1 M N1 N2)
    (x : Fin N1 → ℝ) (y : ExtendedRule I1 I2 N2) : Prop :=
  ∀ zu ∈ m.liftedSupport,
    m.bvec zu.1 ≤ (m.Amat zu.1).mulVec x + m.recourse.B.mulVec (y.eval zu.1 zu.2)

/-- The worst-case expected recourse cost (2), as an extended-real supremum. -/
noncomputable def Model.beta (m : Model I1 I2 L1 M N1 N2)
    (x : Fin N1 → ℝ) : EReal :=
  ⨆ P : {P : Measure (Fin I1 → ℝ) // P ∈ m.ambF},
    ((∫ z, m.Q x z ∂P.1 : ℝ) : EReal)

/-- The regular LDR problem (12), as extended-real infimum and supremum. -/
noncomputable def Model.betaL (m : Model I1 I2 L1 M N1 N2)
    (x : Fin N1 → ℝ) : EReal :=
  ⨅ y : {y : ClassicalRule I1 N2 // m.ClassicalFeasible x y},
    ⨆ P : {P : Measure (Fin I1 → ℝ) // P ∈ m.ambF},
      ((∫ z, dotProduct m.recourse.d (y.1.eval z) ∂P.1 : ℝ) : EReal)

/-- The extended LDR problem (15), as extended-real infimum and supremum. -/
noncomputable def Model.betaE (m : Model I1 I2 L1 M N1 N2)
    (x : Fin N1 → ℝ) : EReal :=
  ⨅ y : {y : ExtendedRule I1 I2 N2 // m.ExtendedFeasible x y},
    ⨆ P : {P : Measure ((Fin I1 → ℝ) × (Fin I2 → ℝ)) // P ∈ m.liftedAmb},
      ((∫ zu, dotProduct m.recourse.d (y.1.eval zu.1 zu.2) ∂P.1 : ℝ) : EReal)

/-- Robust program (9), with an extended-real infimum over feasible triples. -/
noncomputable def Model.robustValue9 (m : Model I1 I2 L1 M N1 N2)
    (x : Fin N1 → ℝ) : EReal :=
  ⨅ a : {a : ℝ × (Fin L1 → ℝ) × (Fin I2 → ℝ) //
      0 ≤ a.2.2 ∧ ∀ zu ∈ m.liftedSupport,
        m.Q x zu.1 ≤ a.1 + dotProduct a.2.1 (m.G.mulVec zu.1) + dotProduct a.2.2 zu.2},
    ((a.1.1 + dotProduct a.1.2.1 m.mu + dotProduct a.1.2.2 m.sigma : ℝ) : EReal)

end AdaptDRO.LiftedLDR


