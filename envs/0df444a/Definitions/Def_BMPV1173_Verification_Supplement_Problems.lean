-- Prove2me | Definitions.Def_BMPV1173_Verification_Supplement_Problems
-- name    : BMPV1173_Verification_Supplement_Problems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T05:51:21.274328+00:00
-- url     : https://prove2.me/theorems/4d985fac-aa7a-4d3e-b70f-c2ed6c0a16fc
-- title:
--   Distance-two graph predicates, self-product test and promised OV
-- statement:
--   For an adjacency matrix of a simple undirected graph, vertices $u,v$ are within distance two exactly when $u=v$, they are adjacent, or they have a common neighbor. Diameter at most two requires this for every pair; radius at most two requires one vertex for which it holds for every vertex. Their query complexities use the published symmetric, zero-diagonal input domain, including disconnected graphs.
--
--   The self-product test accepts a single Boolean matrix $X$ exactly when $X\mathbin\bullet X^{\mathsf T}=J_n$. Its only unknown input is $X$; the transpose and all-ones target are computed with the existing published bit map.
--
--   For fixed positive $c_{\rm low},c_{\rm high}$ and $n\ge2$, the promised OV domain requires, at every pair of distinct row positions, an intersection size at most $c_{\rm low}\log n$ or at least $c_{\rm high}n/\log n$. The empty and singleton lists have no distinct positions and are handled as unrestricted domains before evaluating a logarithmic threshold. These predicates add no preprocessing event or resource guarantee.
-- source:
--   Amin Shiraz Gilani, François Le Gall, Xingyu Zhou, STOC 2027 submission #1173 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1173.pdf, §2.1, printed pp.13–14 = PDF pp.13–14; self-product restriction p.3 and p.20; Problem (PromOV_n), printed p.21 = PDF p.21.

import Definitions.Def_BMPV1173_Verification_Reductions

/-! Only the additional domains and predicates from §§2.1 and 4.1.
Input bits, Boolean products and graph validity are the published objects. -/
namespace BMPV1173.Verification.Supplement

def WithinTwo {n : ℕ} (x : MatrixIndex n → Bool) (u v : Fin n) : Prop :=
  u = v ∨ x (u, v) = true ∨
    ∃ w : Fin n, x (u, w) = true ∧ x (w, v) = true

noncomputable def diamTwo {n : ℕ} (x : MatrixIndex n → Bool) : Bool := by
  classical
  exact decide (∀ u v : Fin n, WithinTwo x u v)

noncomputable def radTwo {n : ℕ} (x : MatrixIndex n → Bool) : Bool := by
  classical
  exact decide (∃ u : Fin n, ∀ v : Fin n, WithinTwo x u v)

noncomputable def qDiamTwo (n : ℕ) : ENat :=
  queryComplexity {x | SimpleGraphInput x} (@diamTwo n)

noncomputable def qRadTwo (n : ℕ) : ENat :=
  queryComplexity {x | SimpleGraphInput x} (@radTwo n)

/-- X is the only unknown oracle; B = Xᵀ and C = J are computed. -/
noncomputable def selfProduct {n : ℕ} (x : VectorInput n) : Bool :=
  bmpv (evalMap (orthogonalVerificationMap n) x)

noncomputable def qSelfProduct (n : ℕ) : ENat :=
  queryComplexity Set.univ (@selfProduct n)

noncomputable def commonOnes {n : ℕ} (x : VectorInput n) (i j : Fin n) : ℕ := by
  classical
  exact (Finset.univ.filter (fun k : Fin n =>
    x (i, k) = true ∧ x (j, k) = true)).card

/-- The domain is used for n ≥ 2; neither a relation between the positive
constants nor a preprocessing success event is a promise. -/
def PromisedOV (cLow cHigh : ℝ) (n : ℕ) : Set (VectorInput n) :=
  if n < 2 then Set.univ else {x | ∀ i j : Fin n, i ≠ j →
    (commonOnes x i j : ℝ) ≤ cLow * Real.log (n : ℝ) ∨
    cHigh * (n : ℝ) / Real.log (n : ℝ) ≤ (commonOnes x i j : ℝ)}

end BMPV1173.Verification.Supplement


