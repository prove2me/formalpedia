-- Prove2me | Definitions.Def_PosIndexNash_PPADS_PositiveIndexLCP
-- name    : PosIndexNash_PPADS_PositiveIndexLCP
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T02:50:21.406168+00:00
-- url     : https://prove2.me/theorems/de4857da-30f1-4a2c-b677-907aa681b6be
-- title:
--   Promise search problem of a positive LCP solution of an anchored normal form
-- statement:
--   **Positive-Index LCP** is the exact complementarity intermediate problem for §§5–6. A valid instance is the binary code of an anchored normal form $(A,U,V,b)$ whose map $\Phi(\lambda)=V^\top x(\lambda)$ has only regular, circuit-strict fixed points. For $M=A-UV^\top$, an answer is a rational vector $x\in\mathbb Q^m$ satisfying
--   $$x\ge0,\qquad Mx-b\ge0,\qquad x_i(Mx-b)_i=0\quad(i\in[m]),$$
--   and, on the active support $I=\{i:x_i>0\}$,
--   $$\operatorname{sign}\det M_{I,I}=+1.$$
--   By Lemma 5.5, $\operatorname{sign}\det M_{I,I}=\operatorname{sign}\det(I_d-D\Phi(V^\top x))=\operatorname{ind}_{\Phi}(V^\top x)$. Lemma 5.5, 6.5 and Theorem 6.8 use precisely this common sign.
-- source:
--   Kontogiannis, Panageas, Pollatos, Yan, Finding a Positive Index Nash Equilibrium is PPADS-Complete, arXiv:2609.23879, pp. 35–39, §5 and Lemmas 5.3–5.6; p. 43, Lemma 6.5

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_CardinalMatching_encRatMatrix
import Definitions.Def_QuasiStrictNE_supp
import Definitions.Def_PosIndexNash_PPADS_NormalForm
import Definitions.Def_PosIndexNash_PPADS_NormalForm_enc
import Definitions.Def_PosIndexNash_PPADS_LCP
import Definitions.Def_PosIndexNash_PPADS_FixedPointIndex

namespace PosIndexNash.PPADS

open Matrix

/-- The normal-form promise used in Sections 5 and 6: anchored output gates, strictness at every
fixed point, and regularity of every fixed point. -/
def NormalFormValid (F : NormalForm) : Prop :=
  F.Anchored ∧ F.StrictAtFixedPoints ∧
    ∀ lam ∈ F.Fix, IsRegularFixedPoint F.Phi lam

/-- Positive exact LCP solutions. The sign is taken on the active principal block indexed by
`supp(x)`, as in Lemma 5.5; it is the fixed-point index of the corresponding fixed point. -/
def PositiveIndexLCP : TetrisHard.Rows.SearchProblem where
  valid s := ∃ F : NormalForm, NormalFormValid F ∧ s = F.enc
  answer s t := ∃ (F : NormalForm) (x : Fin F.m → ℚ),
    NormalFormValid F ∧ s = F.enc ∧
    t = CardinalMatching.encRatVec F.m x ∧
    (fun i => (x i : ℝ)) ∈
      LCPSol (F.M.map ((↑) : ℚ → ℝ)) (-(fun i => (F.b i : ℝ))) ∧
    ((SignType.sign ((F.M.map ((↑) : ℚ → ℝ)).submatrix
      (Subtype.val : {i // i ∈ QuasiStrictNE.supp (fun i => (x i : ℝ))} → Fin F.m)
      Subtype.val).det : SignType) : ℤ) = 1

end PosIndexNash.PPADS


