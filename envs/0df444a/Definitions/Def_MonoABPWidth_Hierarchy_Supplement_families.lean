-- Prove2me | Definitions.Def_MonoABPWidth_Hierarchy_Supplement_families
-- name    : MonoABPWidth_Hierarchy_Supplement_families
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:33:51.160695+00:00
-- url     : https://prove2.me/theorems/cd74a08e-206b-4a59-a95a-01620899faf2
-- title:
--   Real p-families and monotone formula and branching-program classes
-- statement:
--   A polynomial family $f=(f_t)_{t\in\mathbb N}$ supplies a finite number $m(t)$ of variables and a real polynomial $f_t$ in those variables. It is a p-family when $m(t)$ and $\deg f_t$ are polynomially bounded. A polynomial bound has the uniform form
--   $$s(t)\le C(t+1)^a\quad\text{for all }t\in\mathbb N,$$
--   with fixed natural $C,a$. Constants and exponents can depend on fixed theorem parameters, but not on $t$.
--
--   Membership in $\mathrm{mVF}$ means that actual monotone trees computing $f_t$ have polynomial total gate count. Membership in $\mathrm{mVF}_D$ additionally requires alternating trees of total depth at most $D$. Membership in $\mathrm{mVBP}_{W(t)}$ means that the published affine-label mABPs computing $f_t$ have width at most $W(t)$ and polynomial vertex count, where vertex count sums all layer sizes. All three classes include the p-family requirements. They are nonuniform: the definitions impose no algorithm for choosing the trees or programs.
--
--   The threshold for Theorem 6.4 is $\log_2 t/(\log_2\log_2 t)^2$. Its ordinary real-logarithm values at small indices have no effect on eventual little-o assertions. Renaming any finite variable set into $\mathrm{Fin}(m(t))$ preserves these classes.
-- source:
--   Julian Dörfler, Alexander Rogovskyy, STOC 2027 submission #927 (October 2026), §2.1–2.3, pp.4–5, PDF5–6; Theorem 6.4, p.16, PDF17

import Definitions.Def_MonoABPWidth_Hierarchy_Supplement_formulas
import Definitions.Def_MonoABPWidth_Hierarchy_branchingProgram

open scoped BigOperators ENNReal

namespace MonoABPWidth.Hierarchy.Supplement

/-- A uniform polynomial bound, with finite exceptions absorbed by C. -/
def PolynomiallyBounded (s : ℕ → ℕ) : Prop :=
  ∃ C a : ℕ, ∀ t : ℕ, s t ≤ C * (t + 1) ^ a

/-- Generic real polynomial families, before imposing resource or p-family bounds.
Every finite variable set can be renamed into Fin(nvars t). -/
structure PolynomialFamily where
  nvars : ℕ → ℕ
  poly : (t : ℕ) → MvPolynomial (Fin (nvars t)) ℝ

def PolynomialFamily.IsPFamily (f : PolynomialFamily) : Prop :=
  PolynomiallyBounded f.nvars ∧ PolynomiallyBounded (fun t => (f.poly t).totalDegree)

/-- Nonuniform polynomial gate count; no bound on depth. -/
def InMVF (f : PolynomialFamily) : Prop :=
  f.IsPFamily ∧ ∃ C a : ℕ, ∀ t : ℕ,
    ∃ F : Formula (Fin (f.nvars t)), F.eval = f.poly t ∧ F.size ≤ C * (t + 1) ^ a

/-- Bounded total depth, with the alternating convention of §2.3. -/
def InMVFDepth (D : ℕ) (f : PolynomialFamily) : Prop :=
  f.IsPFamily ∧ ∃ C a : ℕ, ∀ t : ℕ,
    ∃ F : Formula (Fin (f.nvars t)), F.eval = f.poly t ∧
      F.Alternating ∧ F.depth ≤ D ∧ F.size ≤ C * (t + 1) ^ a

/-- The source's vertex count, including both singleton endpoint layers. -/
def vertexCount {σ : Type} (A : MABP σ) : ℕ := ∑ i, A.layerSize i

/-- Full affine-label mABPs, polynomial vertex count and pointwise width bound. -/
def InMVBP (W : ℕ → ℕ) (f : PolynomialFamily) : Prop :=
  f.IsPFamily ∧ ∃ C a : ℕ, ∀ t : ℕ,
    ∃ A : MABP (Fin (f.nvars t)), A.output = f.poly t ∧
      A.width ≤ W t ∧ vertexCount A ≤ C * (t + 1) ^ a

/-- All logarithms in the width threshold of Theorem 6.4 are base two. -/
noncomputable def widthThreshold (t : ℕ) : ℝ :=
  Real.logb 2 (t : ℝ) / (Real.logb 2 (Real.logb 2 (t : ℝ))) ^ 2

end MonoABPWidth.Hierarchy.Supplement


