-- Prove2me | Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
-- name    : OAI_Geometry_DoublingHilbert_Derivatives
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T22:07:42.813073+00:00
-- url     : https://prove2.me/theorems/1bd03ba9-e33a-43a3-9073-e843bd483daf
-- title:
--   Sheets of a map on the strip set, their good points, and the closure of squared derivative norms
-- statement:
--   Let $S\subseteq\ell^2$ be the strip set, with points $z(p,w)$ indexed by a base point $p\in\mathbb{R}^2$ and a finitely supported tuple $w$, and with open sheet domains $\Omega_w=\{p:(p,w)\text{ admissible}\}$. Let $E$ be a finite-dimensional real normed space and $f:S\to E$ a map. For $g:\mathbb{R}^2\to E$ write $Dg(p)$ for its Fréchet derivative at $p$, with the convention $Dg(p)=0$ where $g$ is not differentiable.
--
--   1. **Derivative column on a domain.** For $g:\mathbb{R}^2\to E$, a set $\Omega\subseteq\mathbb{R}^2$ and a direction $v\in\mathbb{R}^2$, the column $c^{\Omega}_{g,v}(p)=\mathbf{1}_{\Omega}(p)\,Dg(p)v$ is the directional derivative extended by zero outside $\Omega$.
--
--   2. **Sheets.** For a tuple $w$, the sheet of $f$ is $F_w(p)=f(z(p,w))$ for $p\in\Omega_w$ and $F_w(p)=0$ otherwise. If $f$ is $D$-Lipschitz, then $F_w$ is $2D$-Lipschitz on $\Omega_w$ (proved here).
--
--   3. **Good points.** A point $p$ is good for the sheet $F_w$ if $p\in\Omega_w$, $F_w$ is differentiable at $p$, and $p$ is a mean-square Lebesgue point of both columns $c_x=c^{\Omega_w}_{F_w,(1,0)}$ and $c_y=c^{\Omega_w}_{F_w,(0,1)}$:
--   $$
--   \lim_{r\to0^+}\frac{1}{|\bar B(p,r)|}\int_{\bar B(p,r)}\bigl\|c_\bullet(q)-c_\bullet(p)\bigr\|^2\,dq=0\qquad(\bullet\in\{x,y\}),
--   $$
--   where $\bar B(p,r)=[p_1-r,p_1+r]\times[p_2-r,p_2+r]$ and $|\cdot|$ is Lebesgue measure.
--
--   4. **Derivative data and its closure.** The derivative pair of $F_w$ at $p$ is $\Phi_w(p)=\bigl(\|c_x(p)\|^2,\|c_y(p)\|^2\bigr)\in\mathbb{R}^2$. The derivative data of $f$ is the set $\mathcal{D}_f$ of all pairs $\Phi_w(p)$ over all tuples $w$ and all good points $p$ of $F_w$, and $K_f=\overline{\mathcal{D}_f}$ is its closure in $\mathbb{R}^2$.
--
--   5. **Lipschitz extension into finite dimensions** (a theorem stated with these definitions). If $X$ is a pseudometric space, $s\subseteq X$, and $g:X\to E$ is Lipschitz on $s$, then there are $L\ge0$ and an $L$-Lipschitz map $\tilde g:X\to E$ with $\tilde g=g$ on $s$.
--
--   The set $K_f$ gathers the derivative information of all sheets of $f$ at once. In the non-embedding argument one takes the largest first coordinate $A$ of $K_f$ and then the largest second coordinate $B$ among the pairs with first coordinate $A$; the extension theorem lets each sheet be replaced by a globally Lipschitz map that agrees with it on its open domain.
--
--   **Formalization Note** The definitions are `sheetColumn`, `embeddingSheet`, `goodSheetPoint`, `derivativePair`, `derivativeData` and `derivativeCompact`; derivatives are `fderiv`, the averages are Mathlib's set averages over `Metric.closedBall p r`, which for the product (maximum) metric on the plane is the closed square above, and the Lipschitz bound for sheets refers to that metric. The value $0$ of a sheet off its domain is an arbitrary convention. The extension theorem `exists_lipschitz_extension_finiteDimensional` gives no control of $L$. The private lemma `dite_eq_left` is a rewriting helper.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/Derivatives.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/Derivatives.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DoublingHilbert mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

/-! Derivative fields, good points, and the compact set of derivative norms. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology

open MeasureTheory Set Filter
open scoped Topology

noncomputable section
namespace DoublingHilbert

section BoundedFields
variable {E : Type*} [NormedAddCommGroup E]

end BoundedFields

section DerivativeFields
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Derivative column, extended by zero off the open sheet domain. -/
def sheetColumn (f : ℝ × ℝ → E) (Ω : Set (ℝ × ℝ)) (v : ℝ × ℝ) : ℝ × ℝ → E :=
  Ω.indicator (fun p => fderiv ℝ f p v)

end DerivativeFields
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
open scoped Topology

section Embedding
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- A sheet is the actual embedding on its domain; the arbitrary outside value is zero. -/
def embeddingSheet (f : constructedSet → E) (w : Tuple) (p : Base) : E := by
  classical
  exact if h : admissible p w then f ⟨point p w, point_mem p w h⟩ else 0

omit [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem embeddingSheet_eq (f : constructedSet → E) (w : Tuple) (p : Base)
    (hp : admissible p w) : embeddingSheet f w p = f ⟨point p w, point_mem p w hp⟩ := by
  simp only [embeddingSheet, dite_eq_left hp]

omit [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem embeddingSheet_lipschitz {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) :
    LipschitzOnWith (2 * D) (embeddingSheet f w) (sheetDomain w) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro p hp q hq
  rw [embeddingSheet_eq _ _ _ hp, embeddingSheet_eq _ _ _ hq]
  calc
    _ ≤ (D : ℝ) * dist (point p w) (point q w) :=
      hf.dist_le_mul ⟨point p w, point_mem p w hp⟩ ⟨point q w, point_mem q w hq⟩
    _ ≤ (D : ℝ) * (2 * dist p q) := mul_le_mul_of_nonneg_left (point_dist_sameTuple_le p q w) D.coe_nonneg
    _ = _ := by push_cast; ring

def goodSheetPoint (f : constructedSet → E) (w : Tuple) (p : Base) : Prop :=
  p ∈ sheetDomain w ∧ DifferentiableAt ℝ (embeddingSheet f w) p ∧
    Tendsto (fun r : ℝ => ⨍ q in Metric.closedBall p r,
      ‖sheetColumn (embeddingSheet f w) (sheetDomain w) (1, 0) q -
        sheetColumn (embeddingSheet f w) (sheetDomain w) (1, 0) p‖ ^ 2)
      (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun r : ℝ => ⨍ q in Metric.closedBall p r,
      ‖sheetColumn (embeddingSheet f w) (sheetDomain w) (0, 1) q -
        sheetColumn (embeddingSheet f w) (sheetDomain w) (0, 1) p‖ ^ 2)
      (𝓝[>] 0) (𝓝 0)

/-- Squared derivative columns, the pairs used in the one fixed compact set. -/
def derivativePair (f : constructedSet → E) (w : Tuple) (p : Base) : ℝ × ℝ :=
  (‖sheetColumn (embeddingSheet f w) (sheetDomain w) (1, 0) p‖ ^ 2,
   ‖sheetColumn (embeddingSheet f w) (sheetDomain w) (0, 1) p‖ ^ 2)

def derivativeData (f : constructedSet → E) : Set (ℝ × ℝ) :=
  {z | ∃ w p, goodSheetPoint f w p ∧ derivativePair f w p = z}

def derivativeCompact (f : constructedSet → E) : Set (ℝ × ℝ) := closure (derivativeData f)

end Embedding
end DoublingHilbert

open Set
noncomputable section
namespace DoublingHilbert

/-- Finite-dimensional Lipschitz sheet maps have some global Lipschitz extension.
Only agreement on the original open domain is used for sharp derivative estimates. -/
theorem exists_lipschitz_extension_finiteDimensional
    {X E : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : X → E} {s : Set X} {C : NNReal}
    (hf : LipschitzOnWith C f s) :
    ∃ g : X → E, ∃ L : NNReal, LipschitzWith L g ∧ EqOn f g s := by
  let e : E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) :=
    (Module.finBasis ℝ E).equivFun.toContinuousLinearEquiv
  obtain ⟨g, hg, heq⟩ := (e.lipschitz.comp_lipschitzOnWith hf).extend_pi
  refine ⟨e.symm ∘ g, _, e.symm.lipschitz.comp hg, ?_⟩
  intro x hx
  change f x = e.symm (g x)
  rw [← heq hx]
  exact (e.symm_apply_apply (f x)).symm

end DoublingHilbert

end
end

end OAI


