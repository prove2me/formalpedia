-- Prove2me | Definitions.Def_GibbsTransition_SizeCopies_Supplement_Field
-- name    : GibbsTransition_SizeCopies_Supplement_Field
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T05:33:36.215501+00:00
-- url     : https://prove2.me/theorems/a550af9d-57ea-4132-8eb5-546667d71426
-- title:
--   General field-coupled lattice model and ground/Gibbs densities
-- statement:
--   Let $q\ge1$ be the public local dimension. A cube has sites $\{0,\ldots,L-1\}^3$ and configurations assigning one of $q$ basis labels to each site. The public data comprise a positive contraction $P$, rational bounds $J>0,J_b\ge0$, rational $0\le a<b\le1$, and a common, uniformly effectively encoded algebraic boundary operator of norm at most $J_bL^2$. Unknown algebraic Hermitian on-site and directed edge terms have norms at most $J$. Their Hamiltonian is
--   $$H_{u,L}(\phi)=K_{u,L}-\phi\sum_xP_x+B_L.$$
--   The ground state is the normalized projector onto the entire least eigenspace; the finite-temperature state is the normalized matrix exponential. The class requires the limiting ground-state order parameter at every real field away from a transition $\theta_u\in[1/4,3/4]$, with values in $[0,a]$ on the left and $[b,1]$ on the right. Neither convergence of energies nor a finite-size estimate is assumed. The definitions also give the specialization data for the published class and the product family (57).
--
--   These objects extend the published lattice geometry without redeclaring the published class. A boundary's effective algebraic description is represented by a recursive Cauchy table; algebraicity and Hermiticity are separately required.
--
--   The public boundary representation admits any uniformly computably approximable algebraic boundary, which can be broader than a uniform exact algebraic encoding. Every source encoding supplies the required Cauchy table. This harmless extension is declared in each theorem quantified over the general public data.
-- source:
--   Yuhao Cai, Zhenzhang Li, STOC 2027 submission #1168 (October 2026), Section 2.1–2.2, (2)–(7), (57), printed pp. 3–4,16 (PDF pp. 5–6,18); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1168.pdf

import Mathlib
import Definitions.Def_GibbsTransition_SizeCopies_Physics
open scoped Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

noncomputable section

namespace GibbsTransition.SizeCopies.Supplement
attribute [local instance] Classical.propDecidable

abbrev Config (q L : ℕ) := Site L → Fin q
abbrev Local (q : ℕ) := Matrix (Fin q) (Fin q) ℂ
abbrev Pair (q : ℕ) := Matrix (Fin q × Fin q) (Fin q × Fin q) ℂ
abbrev Cube (q L : ℕ) := Matrix (Config q L) (Config q L) ℂ

def embedSite {q L : ℕ} (A : Local q) (x : Site L) : Cube q L :=
  fun s t => if ∀ y, y ≠ x → s y = t y then A (s x) (t x) else 0

def embedEdge {q L : ℕ} (A : Pair q) (x y : Site L) : Cube q L :=
  fun s t => if ∀ z, z ≠ x → z ≠ y → s z = t z
    then A (s x, s y) (t x, t y) else 0

/-- Public data only; no unknown interaction or transition is supplied here. -/
structure FieldData (q : ℕ) where
  P : Local q
  J : ℚ
  Jb : ℚ
  a : ℚ
  b : ℚ
  boundary : (L : ℕ) → Cube q L

/-- Explicit lexicographic base-q coordinate for uniform boundary descriptions. -/
def configCode {q L : ℕ} (s : Config q L) : ℕ :=
  ∑ x : Site L, (s x).val * q ^ ((x 0).val + L * (x 1).val + L^2 * (x 2).val)

def rationalComplex (z : ℚ × ℚ) : ℂ := (z.1 : ℂ) + (z.2 : ℂ) * Complex.I

/-- A total recursive Cauchy description of all boundary entries, uniform in L.
Algebraicity is checked separately. Inputs encode (L,row,column,precision). -/
def EffectiveBoundary {q : ℕ} (p : FieldData q) : Prop :=
  ∃ f : ℕ → ℕ, Computable f ∧ ∀ (L : ℕ) (s t : Config q L) (m : ℕ), 1 ≤ L →
    ∃ z : ℚ × ℚ,
      Encodable.decode (f (Encodable.encode (L, configCode s, configCode t, m))) = some z ∧
      ‖rationalComplex z - p.boundary L s t‖ ≤ (2 : ℝ)^(-(m : ℤ))

def ValidField {q : ℕ} (p : FieldData q) : Prop :=
  0 < q ∧ 0 < p.J ∧ 0 ≤ p.Jb ∧ 0 ≤ p.a ∧ p.a < p.b ∧ p.b ≤ 1 ∧
  p.P.IsHermitian ∧ p.P.PosSemidef ∧ (1 - p.P).PosSemidef ∧
  (∀ s t, IsAlgebraic ℚ (p.P s t)) ∧
  (∀ L, 1 ≤ L → (p.boundary L).IsHermitian ∧
    (∀ s t, IsAlgebraic ℚ (p.boundary L s t)) ∧
    ‖p.boundary L‖ ≤ (p.Jb : ℝ) * (L : ℝ)^2) ∧ EffectiveBoundary p

structure FieldInteraction (q : ℕ) where
  onsite : Local q
  edge : Fin 3 → Pair q

def FieldAdmissible {q : ℕ} (p : FieldData q) (u : FieldInteraction q) : Prop :=
  u.onsite.IsHermitian ∧ (∀ i, (u.edge i).IsHermitian) ∧
  (∀ s t, IsAlgebraic ℚ (u.onsite s t)) ∧
  (∀ i s t, IsAlgebraic ℚ (u.edge i s t)) ∧
  ‖u.onsite‖ ≤ (p.J : ℝ) ∧ ∀ i, ‖u.edge i‖ ≤ (p.J : ℝ)

def fieldBulk {q : ℕ} (u : FieldInteraction q) (L : ℕ) : Cube q L :=
  (∑ x : Site L, embedSite u.onsite x) +
  ∑ i : Fin 3, ∑ xy ∈ internalEdges L i, embedEdge (u.edge i) xy.1 xy.2

def fieldMagnetization {q : ℕ} (p : FieldData q) (L : ℕ) : Cube q L :=
  ∑ x : Site L, embedSite p.P x

def fieldHamiltonian {q : ℕ} (p : FieldData q) (u : FieldInteraction q)
    (L : ℕ) (phi : ℝ) : Cube q L :=
  fieldBulk u L - phi • fieldMagnetization p L + p.boundary L

def matrixGround {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) : Matrix n n ℂ :=
  let E := sInf (spectrum ℝ A)
  let Q := cfc (fun x : ℝ => if x = E then 1 else 0) A
  (Matrix.trace Q)⁻¹ • Q

def matrixGibbs {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (beta : ℝ) : Matrix n n ℂ :=
  let W := cfc (fun x : ℝ => Real.exp (-beta*x)) A
  (Matrix.trace W)⁻¹ • W

def fieldGround {q : ℕ} (p : FieldData q) (u : FieldInteraction q)
    (L : ℕ) (phi : ℝ) : Cube q L := matrixGround (fieldHamiltonian p u L phi)

def fieldGibbs {q : ℕ} (p : FieldData q) (u : FieldInteraction q)
    (L : ℕ) (phi beta : ℝ) : Cube q L := matrixGibbs (fieldHamiltonian p u L phi) beta

def fieldOrder {q : ℕ} (p : FieldData q) (u : FieldInteraction q)
    (L : ℕ) (phi : ℝ) : ℝ :=
  (Matrix.trace (fieldGround p u L phi * fieldMagnetization p L)).re / (L : ℝ)^3

def fieldEnergy {q : ℕ} (p : FieldData q) (u : FieldInteraction q)
    (L : ℕ) (phi : ℝ) : ℝ := sInf (spectrum ℝ (fieldHamiltonian p u L phi)) / (L : ℝ)^3

def FieldPhase {q : ℕ} (p : FieldData q) (u : FieldInteraction q) (theta : ℝ) : Prop :=
  theta ∈ Set.Icc (1/4 : ℝ) (3/4) ∧
  ∀ phi ∈ Set.Icc (0 : ℝ) 1, phi ≠ theta → ∃ m : ℝ,
    Filter.Tendsto (fun n : ℕ => fieldOrder p u (n+1) phi) Filter.atTop (nhds m) ∧
    (phi < theta → m ∈ Set.Icc (0 : ℝ) p.a) ∧
    (theta < phi → m ∈ Set.Icc (p.b : ℝ) 1)

def InFieldClass {q : ℕ} (p : FieldData q) (u : FieldInteraction q) : Prop :=
  FieldAdmissible p u ∧ ∃ theta, FieldPhase p u theta

def fieldTheta {q : ℕ} (p : FieldData q) (u : FieldInteraction q) : ℝ :=
  if h : ∃ theta, FieldPhase p u theta then h.choose else 0

def fieldLimitEnergy {q : ℕ} (p : FieldData q) (u : FieldInteraction q) (phi : ℝ) : ℝ :=
  if h : ∃ e : ℝ, Filter.Tendsto (fun n : ℕ => fieldEnergy p u (n+1) phi)
    Filter.atTop (nhds e) then h.choose else 0

def gap {q : ℕ} (p : FieldData q) : ℚ := p.b - p.a

def surfaceC {q : ℕ} (p : FieldData q) : ℚ := max 1 (3*p.J + p.Jb)
def recoveryC {q : ℕ} (p : FieldData q) : ℚ := max 1 (12*p.J)

/-- Specialization data; equivalence with the published C* remains a theorem,
not an assumption of the general model. -/
def starData : FieldData 3 where
  P := publicP
  J := 1
  Jb := 3/8
  a := 1/4
  b := 3/4
  boundary := boundaryTerm

def starInteraction (u : Interaction) : FieldInteraction 3 := ⟨u.onsite, u.edge⟩

/-- The product family (57), before the common public field and boundary. -/
def productInteraction (theta : ℚ) : Interaction where
  onsite := Matrix.diagonal fun s => if s = 0 then 0 else
    if s = 1 then (theta : ℂ) else ((theta + 1/8 : ℚ) : ℂ)
  edge := fun _ => 0

end GibbsTransition.SizeCopies.Supplement


