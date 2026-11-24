-- Prove2me | Definitions.Def_RegMT_Classif_Supplement_RKHS
-- name    : RegMT_Classif_Supplement_RKHS
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T05:26:07.834559+00:00
-- url     : https://prove2.me/theorems/4796e037-d584-485f-91ab-2ba17a97ab19
-- title:
--   RKHS data, kernel calmness, and original and lifted problems
-- statement:
--   Let $H$ be a real Hilbert space and $X$ a feature support. The published RKHS interface supplies a kernel $k$, feature map $\Phi$, and evaluations with
--   $$k(x,x')=\langle\Phi(x),\Phi(x')\rangle_H,\qquad h(x)=\langle h,\Phi(x)\rangle_H.$$
--   The closed linear span of $\Phi(X)$ is all of $H$, so the representation has no invisible directions. The additional data define the original and lifted learning objectives (29) and (30). The lifted regression product has its Hilbert 2-norm $\sqrt{\|u\|_H^2+y^2}$, while classification uses the published label metric. The regression output support $Y$ is retained; the lifted feature support is all of $H$, rather than only $\Phi(X)$.
--   Assumption 3.22 is a smooth, nonnegative, concave growth function on $[0,\infty)$ with $g(0)=0$, $g'\ge1$, and $\sqrt{k(x,x)-2k(x,x')+k(x',x')}\le g(\|x-x'\|_2)$. Its endpoint derivative is the derivative within the half-line. No finite-dimensional assumption is made on $H$.
-- source:
--   Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, Regularization via Mass Transportation, arXiv:1710.10016v3, pp.14–16, §3.3, Assumption 3.22 and (29)–(30)

import Mathlib
import Definitions.Def_FoundationsML_Stability_IsRKHSOf
import Definitions.Def_RegMT_Classif_Supplement_Transport

open scoped ENNReal

open MeasureTheory
noncomputable section

namespace RegMT.Classif.Supplement
attribute [local instance] Classical.propDecidable

/-- Hilbert product with its 2-norm, never the max norm on an ordinary product. -/
abbrev HP (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] := WithLp 2 (H × ℝ)

instance hpMeasurable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] :
    MeasurableSpace (HP H) := borel (HP H)
instance hpBorel (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] :
    BorelSpace (HP H) := ⟨rfl⟩

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Paper-specific data over the published RKHS interface; density rules out invisible directions. -/
structure RKHSData (X : Set V) (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  kernel : X → X → ℝ
  feature : X → H
  eval : H → X → ℝ
  rkhs : FoundationsML.Stability.IsRKHSOf kernel feature eval
  total : Dense (Submodule.span ℝ (Set.range feature) : Set H)

/-- Extend only to evaluate ambient measures; all laws are supported on X. -/
def featureOn {X : Set V} (R : RKHSData X H) (x : V) : H :=
  if hx : x ∈ X then R.feature ⟨x, hx⟩ else 0

/-- Assumption 3.22, including smoothness, concavity and the derivative at the endpoint. -/
def KernelCalm {X : Set V} (R : RKHSData X H) (g : ℝ → ℝ) : Prop :=
  g 0 = 0 ∧ (∀ t ≥ 0, 0 ≤ g t) ∧ ConcaveOn ℝ (Set.Ici 0) g ∧
  ContDiffOn ℝ ⊤ g (Set.Ici 0) ∧ (∀ t ≥ 0, 1 ≤ derivWithin g (Set.Ici 0) t) ∧
  ∀ x x' : X, Real.sqrt (R.kernel x x - 2 * R.kernel x x' + R.kernel x' x') ≤
    g ‖(x : V) - (x' : V)‖

def jointSupport (X : Set V) (Y : Set ℝ) : Set (HP V) :=
  {z | z.ofLp.1 ∈ X ∧ z.ofLp.2 ∈ Y}

def pairSample {N : ℕ} (x : Fin N → V) (y : Fin N → ℝ) : Fin N → HP V :=
  fun i => WithLp.toLp 2 (x i, y i)

variable [MeasurableSpace V] [MeasurableSpace H]

def originalReg {X : Set V} {N : ℕ} (R : RKHSData X H) (Y : Set ℝ)
    (x : Fin N → V) (y : Fin N → ℝ) (ell : ℝ → ℝ → ℝ) (ρ : ℝ) (h : H) : ℝ≥0∞ :=
  normRisk (jointSupport X Y) (pairSample x y) ρ
    (fun z => ell (inner ℝ h (featureOn R z.ofLp.1)) z.ofLp.2)

def liftedReg {N : ℕ} (u : Fin N → H) (y : Fin N → ℝ)
    (Y : Set ℝ) (ell : ℝ → ℝ → ℝ) (ρ : ℝ) (h : H) : ℝ≥0∞ :=
  normRisk (jointSupport Set.univ Y) (pairSample u y) ρ
    (fun z => ell (inner ℝ h z.ofLp.1) z.ofLp.2)

def originalClass {X : Set V} {N : ℕ} (R : RKHSData X H)
    (x : Fin N → V) (y : Fin N → Bool) (ell : ℝ → Bool → ℝ) (κ ρ : ℝ) (h : H) : ℝ≥0∞ :=
  classRisk X x y κ ρ (fun z => ell (inner ℝ h (featureOn R z.1)) z.2)

def liftedClass {N : ℕ} (u : Fin N → H) (y : Fin N → Bool)
    (ell : ℝ → Bool → ℝ) (κ ρ : ℝ) (h : H) : ℝ≥0∞ :=
  classRisk Set.univ u y κ ρ (fun z => ell (inner ℝ h z.1) z.2)

end RegMT.Classif.Supplement


