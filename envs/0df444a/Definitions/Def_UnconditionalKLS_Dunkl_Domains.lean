-- Prove2me | Definitions.Def_UnconditionalKLS_Dunkl_Domains
-- name    : UnconditionalKLS_Dunkl_Domains
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T20:07:45.315327+00:00
-- url     : https://prove2.me/theorems/0c9d9e13-d21a-4486-ab9e-b374859e1f5e
-- title:
--   Canonical graph closure and closed Dunkl form
-- statement:
--   Let $S>0$ and let $W$ be an unconditional potential satisfying (2.4). Write $\eta$ for the normalized auxiliary law, $H=L^2(\eta)$, and $A_0$ for the paired Taylor expression on $C_c^\infty(\mathbb R^n)$. Define
--   $$G_A=\overline{\{(f,A_0f):f\in C_c^\infty\}}^{H\times H}.$$
--   The operator domain is the first projection of this graph. Its action chooses the graph value, whose uniqueness is a theorem, not a hypothesis. The form graph is likewise the closure of
--   $$\left(f,(\partial_jf)_j,(\sqrt{c_j}D_jf)_j\right),\qquad D_jf=\frac{f-f\circ r_j}{2x_j},$$
--   in the corresponding finite product of $L^2$ spaces. Its first projection defines the form domain. The completed form is the sum of the component inner products and $\mathcal E(f)=\mathcal E(f,f)$. Its Rayleigh gap is the extended nonnegative infimum
--   $$\lambda=\inf_{f\in D(\mathcal E),\,\operatorname{Var}_\eta f>0}\frac{\mathcal E(f)}{\operatorname{Var}_\eta f}.$$
--
--   Self-adjointness is stated as density and single-valuedness of the graph and equality with the adjoint graph. Discreteness is expressed by a compact resolvent at $-1$, which is equivalent in the nonnegative self-adjoint setting here. These are output predicates, never assumed model fields. The weighted test domain requires actual weak differentiability on the open orthants and integrability of $c_i(g^2+|\nabla g|^2)$. It includes the noncompact quotient functions occurring in Appendix A.4.
--
--   The two Bochner predicates are exactly equations (3.10) and (3.11); separate integrability predicates prevent a nonintegrable real integral from silently becoming zero. These definitions supply a reusable realization of the paper's operator and form while leaving their analytic properties to the theorem items.
--
--   **Formalization Note** $L^2$ is a space of almost-everywhere equivalence classes. Raw function representatives are admitted only with `MemLp`. Canonical choices return zero outside their domains; every use is guarded by a domain hypothesis or a conclusion establishing membership.
-- source:
--   Pierre Bizeul, Dan Mikulincer, Ilias Zadik, STOC 2027 submission #1161 (October 2026), pp. 15–16, 20, 32–38; (3.3), (3.6), (3.10)–(3.11), Appendix A. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1161.pdf

import Definitions.Def_UnconditionalKLS_Dunkl_Model

open MeasureTheory Filter
open scoped BigOperators ENNReal ContDiff
noncomputable section

namespace UnconditionalKLS.Dunkl
variable {n : ℕ}
abbrev Hilbert (μ : Measure (Space n)) := Lp ℝ 2 μ
open Classical in
def l2 (μ : Measure (Space n)) (f : Fn n) : Hilbert μ :=
  if h : MemLp f 2 μ then h.toLp f else 0
/-- Initial graph on actual compactly supported smooth functions, in L² × L². -/
def initialGraph (S : ℝ) (W : Fn n) : Set (Hilbert (eta S W) × Hilbert (eta S W)) :=
  {p | ∃ f : Fn n, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
    MemLp f 2 (eta S W) ∧ MemLp (expression S W f) 2 (eta S W) ∧
    p = (l2 (eta S W) f, l2 (eta S W) (expression S W f))}
/-- The genuine product-topology graph closure, not a supplied operator. -/
def operatorGraph (S : ℝ) (W : Fn n) := closure (initialGraph S W)
def OperatorDomain (S : ℝ) (W : Fn n) (f : Fn n) : Prop :=
  MemLp f 2 (eta S W) ∧ ∃ v, (l2 (eta S W) f, v) ∈ operatorGraph S W
open Classical in
def action (S : ℝ) (W : Fn n) (f : Fn n) : Hilbert (eta S W) :=
  if h : ∃ v, (l2 (eta S W) f, v) ∈ operatorGraph S W then h.choose else 0
/-- The two components are the gradient and the weighted differences, in finite products of L². -/
abbrev Jet (μ : Measure (Space n)) := (Fin n → Hilbert μ) × (Fin n → Hilbert μ)
def initialJets (S : ℝ) (W : Fn n) : Set (Hilbert (eta S W) × Jet (eta S W)) :=
  {p | ∃ f : Fn n, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
    MemLp f 2 (eta S W) ∧ (∀ j, MemLp (d f j) 2 (eta S W)) ∧
    (∀ j, MemLp (fun x => Real.sqrt (cj S j x) * difference f j x) 2 (eta S W)) ∧
    p = (l2 (eta S W) f, (fun j => l2 (eta S W) (d f j),
      fun j => l2 (eta S W) (fun x => Real.sqrt (cj S j x) * difference f j x)))}
def formGraph (S : ℝ) (W : Fn n) := closure (initialJets S W)
def FormDomain (S : ℝ) (W : Fn n) (f : Fn n) : Prop :=
  MemLp f 2 (eta S W) ∧ ∃ v, (l2 (eta S W) f, v) ∈ formGraph S W
open Classical in
def formJet (S : ℝ) (W : Fn n) (f : Fn n) : Jet (eta S W) :=
  if h : ∃ v, (l2 (eta S W) f, v) ∈ formGraph S W then h.choose else 0
/-- Closed form by completion of the initial gradient/difference graph. -/
def form (S : ℝ) (W f g : Fn n) : ℝ :=
  ∑ j, inner ℝ ((formJet S W f).1 j) ((formJet S W g).1 j) +
    ∑ j, inner ℝ ((formJet S W f).2 j) ((formJet S W g).2 j)
def energy (S : ℝ) (W f : Fn n) : ℝ := form S W f f
def variance (μ : Measure (Space n)) (f : Fn n) : ℝ := ∫ x, (f x - ∫ y, f y ∂μ)^2 ∂μ
/-- The extended nonnegative infimum of the actual form Rayleigh quotients. -/
def gap (S : ℝ) (W : Fn n) : ℝ≥0∞ :=
  ⨅ f : {f : Fn n // FormDomain S W f ∧ 0 < variance (eta S W) f},
    ENNReal.ofReal (energy S W f.1 / variance (eta S W) f.1)
def Even (μ : Measure (Space n)) (f : Fn n) : Prop :=
  ∀ j, (fun x => f (reflect j x)) =ᵐ[μ] f
def OneOdd (μ : Measure (Space n)) (f : Fn n) (i : Fin n) : Prop :=
  (fun x => f (reflect i x)) =ᵐ[μ] (fun x => -f x) ∧
    ∀ j, j ≠ i → (fun x => f (reflect j x)) =ᵐ[μ] f
/-- Single-valuedness is a conclusion, as are density and equality with the adjoint graph. -/
def SelfAdjointGraph (S : ℝ) (W : Fn n) : Prop :=
  (∀ u v w, (u,v) ∈ operatorGraph S W → (u,w) ∈ operatorGraph S W → v = w) ∧
  Dense {u | ∃ v, (u,v) ∈ operatorGraph S W} ∧
  operatorGraph S W = {p | ∀ u v, (u,v) ∈ operatorGraph S W → inner ℝ p.2 u = inner ℝ p.1 v}
/-- Compact resolvent at -1 is the discrete-spectrum convention for a nonnegative self-adjoint operator. -/
def CompactResolvent (S : ℝ) (W : Fn n) : Prop :=
  ∃ R : Hilbert (eta S W) →L[ℝ] Hilbert (eta S W), IsCompactOperator R ∧
    ∀ u v, (u,v) ∈ operatorGraph S W ↔ R (v+u) = u
/-- The weighted test domain used for Lemma 3.4, including the Appendix A.4 quotients. -/
def WeightedTest (S : ℝ) (W f : Fn n) (i : Fin n) : Prop :=
  AEStronglyMeasurable f (eta S W) ∧ WeaklyDifferentiable f ∧
  Integrable (fun x => cj S i x * (f x ^ 2 + ‖weakGrad f x‖^2)) (eta S W)
def weightedEstimate (S : ℝ) (W f : Fn n) (i : Fin n) : Prop :=
  ((gap S W).toReal - 3 / (2*S^2)) *
    ((∫ x, cj S i x * f x ^ 2 ∂eta S W) -
      (∫ x, cj S i x * f x ∂eta S W)^2 / (∫ x, cj S i x ∂eta S W)) ≤
    ∫ x, cj S i x * ‖weakGrad f x‖^2 ∂eta S W
/-- The complete (3.10) identity, meaningful on the operator domain by A.4. -/
def evenBochner (S : ℝ) (W f : Fn n) : Prop :=
  ‖action S W f‖^2 =
    (∑ j, energy S W (weakPartial f j)) +
    (∫ x, hess W x (weakGrad f x) (weakGrad f x) ∂eta S W) +
    ∑ j, ∫ x, -dc S j x / x j * (weakPartial f j x)^2 ∂eta S W
/-- The complete (3.11) identity, with all six kinds of terms. -/
def oddBochner (S : ℝ) (W f : Fn n) (i : Fin n) : Prop :=
  let g := quotient f i
  ‖action S W f‖^2 =
    (∑ j, energy S W (weakPartial f j)) +
    (∫ x, hess W x (weakGrad f x) (weakGrad f x) ∂eta S W) +
    (∑ j ∈ Finset.univ.erase i, ∫ x, -dc S j x / x j * (weakPartial f j x)^2 ∂eta S W) +
    (∫ x, cj S i x * ‖weakGrad g x‖^2 ∂eta S W) +
    (∫ x, (2*cj S i x - x i * dc S i x) * (weakPartial g i x)^2 ∂eta S W) +
    ∫ x, cj S i x * (d W i x / x i) * g x ^ 2 ∂eta S W
/-- Integrability of every term, recorded separately from the identities to avoid default-zero integrals. -/
def BochnerIntegrable (S : ℝ) (W f : Fn n) : Prop :=
  Integrable (fun x => hess W x (weakGrad f x) (weakGrad f x)) (eta S W) ∧
  ∀ j, Integrable (fun x => -dc S j x / x j * (weakPartial f j x)^2) (eta S W)
def OddIntegrable (S : ℝ) (W f : Fn n) (i : Fin n) : Prop :=
  let g := quotient f i
  Integrable (fun x => cj S i x * ‖weakGrad g x‖^2) (eta S W) ∧
  Integrable (fun x => (2*cj S i x - x i * dc S i x) * (weakPartial g i x)^2) (eta S W) ∧
  Integrable (fun x => cj S i x * (d W i x / x i) * g x ^ 2) (eta S W)
end UnconditionalKLS.Dunkl


