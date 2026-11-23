-- Prove2me | Definitions.Def_ProcureAssort_Hotelling_Supplement_CommonHotelling
-- name    : ProcureAssort_Hotelling_Supplement_CommonHotelling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T12:28:01.105945+00:00
-- url     : https://prove2.me/theorems/86b9332c-e477-4436-b737-7754b7f96fab
-- title:
--   Equidistant locations, independent price-difference rows and common virtual-cost range
-- statement:
--   Equidistant Hotelling suppliers are located at $\ell_i=(i-1)/(n-1)$, with $n\ge2$. The published Hotelling surplus, demand, virtual costs and mechanism definitions are reused.
--
--   For each nonlast active supplier $i$, the independent demand row is
--
--   $$p_{\mathrm{next}(i)}-p_i=v_{\mathrm{next}(i)}-v_i.$$
--
--   Its coefficient is $-1$ at $i$, $1$ at the next active supplier, and zero otherwise. These are the row coordinates used in Appendix L.3; the base path-matrix coefficients are different coordinates and are not reused for $a$. For a nonempty common support, its virtual-cost range is the value at the maximum minus the value at the minimum. There is no restriction to supports with at least three points.
-- source:
--   Saban & Weintraub, Procurement Mechanisms for Assortments of Differentiated Products, SSRN 3453144 (author version of 2020-03-03; Oper. Res. doi:10.1287/opre.2020.2053), Appendix H and Appendix L.3, pp. 60, 75–82

import Mathlib
import Definitions.Def_ProcureAssort_Hotelling_Supplement_Affine

namespace ProcureAssort.Hotelling.Supplement

/-- Endpoint-equidistant locations, paper supplier i+1 is Lean i. -/
noncomputable def equiLoc (n : ℕ) (i : Fin n) : ℝ := (i.val : ℝ) / (n - 1 : ℕ)

/-- The independent price-difference rows used in Appendix L.3, p. 78.
For each nonlast active i the row is p_next - p_i, not a row of pathA. -/
noncomputable def differenceA {n : ℕ} (Q : Finset (Fin n)) (i j : Fin n) : ℝ :=
  if h : (Q.filter (i < ·)).Nonempty then
    (if j = (Q.filter (i < ·)).min' h then 1 else 0) - (if j = i then 1 else 0)
  else 0

/-- Full virtual-cost range of the common support. Defaults off the nonempty domain
are immaterial: every H or L theorem binds nonempty S through ValidTypes. -/
noncomputable def commonRange {n : ℕ} (S : Finset ℝ) (f : ℝ → ℝ) (i : Fin n) : ℝ :=
  if h : S.Nonempty then
    virtualCost (fun _ : Fin n => S) (fun _ => f) i (S.max' h) -
      virtualCost (fun _ : Fin n => S) (fun _ => f) i (S.min' h)
  else 0

end ProcureAssort.Hotelling.Supplement


