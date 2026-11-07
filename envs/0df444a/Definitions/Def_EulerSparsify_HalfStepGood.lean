-- Prove2me | Definitions.Def_EulerSparsify_HalfStepGood
-- name    : EulerSparsify_HalfStepGood
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:34:34.166357+00:00
-- url     : https://prove2.me/theorems/2ec87dd6-210e-4e45-981d-9a6f370245fa
-- title:
--   The output guarantee of one half-sparsification step (Lemma 5.10)
-- statement:
--   Let $\vec G=(V,E,w)$ be a weighted directed graph, $G=\mathrm{und}(\vec G)$, $n=|V|$, and let $c_{\mathrm{ner}}$, $C_{\mathrm{ESO}}$, $c_{\mathrm{tight}}$, $\rho$ be reals. New weights $w'$ satisfy the guarantee if $w'=w\circ(\mathbf 1_E+x')$ for some $x'\in[-1,1]^E$ that vanishes outside $\mathrm{supp}(w)$ (lines 6–7, or $x'=0$ in line 9), and
--
--   1. $B^\top w'=B^\top w$ (degrees are preserved);
--   2. $\mathrm{nnz}(w')\le\max\bigl((1-c_{\mathrm{tight}})\,\mathrm{nnz}(w),\ \max\{64,2c_{\mathrm{ner}}\}\,n\bigr)$;
--   3. the spectral error is small:
--   $$\bigl\|L_G^{\dagger/2}\,B^\top(W'-W)H\,L_G^{\dagger/2}\bigr\|_{\mathrm{op}}\le C_{\mathrm{ESO}}\,\rho^{1/2}.$$
--
--   **Formalization Note** $\rho^{1/2}$ is the real square root; $W'-W=\mathrm{diag}(w'-w)$.
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), Lemma 5.10, pp.21–22 (PDF pp.23–24); Algorithm 5.1, lines 6–9

import Mathlib
import Definitions.Def_EulerSparsify_DiGraph_lap
import Definitions.Def_EulerSparsify_sqrtPinv
import Definitions.Def_LiqPremiaEq_opNorm
import Definitions.Def_EulerSparsify_nnz

namespace EulerSparsify

/-- **The output guarantee of one half-sparsification step** (Lemma 5.10, pp.21–22, PDF pp.23–24;
Algorithm 5.1, lines 6–7 and 9).
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), Lemma 5.10: "it returns ⃗G′ = (V, E, w′) satisfying the following properties … 1. Bᵀ_⃗G w′ =
Bᵀ_⃗G w. 2. nnz(w′) ≤ max((1 − c_tight)nnz(w), max{64, 2c_ner}n). 3. ‖L_G^{†/2} Bᵀ_⃗G (W′ − W) H_⃗G
L_G^{†/2}‖_op ≤ C_ESO ρ^{1/2}."

`HalfStepGood c C_ESO c_tight ρ ⃗G w'` says that `w' = w ∘ (1_E + x')` for some `x' ∈ [−1,1]^E` that
vanishes outside `supp(w)` (lines 6–7 or 9), and that items 1–3 hold, with `c = c_ner`,
`n = |V|`, `G = und(⃗G)` and `L_G = G.lap`.

**Formalization Note.** `ρ^{1/2}` is `Real.sqrt ρ`. `W' − W = diag(w' − w)`. -/
def HalfStepGood {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (c Cs ct ρ : ℝ) (G : DiGraph V E) (w' : E → ℝ) : Prop :=
  (∃ x : E → ℝ, (∀ e, -1 ≤ x e ∧ x e ≤ 1) ∧ (∀ e, G.w e = 0 → x e = 0) ∧
      ∀ e, w' e = G.w e * (1 + x e)) ∧
  G.incMat.transpose.mulVec w' = G.incMat.transpose.mulVec G.w ∧
  (nnz w' : ℝ) ≤ max ((1 - ct) * nnz G.w) (max 64 (2 * c) * Fintype.card V) ∧
  LiqPremiaEq.opNorm (sqrtPinv G.lap *
      (G.incMat.transpose * (Matrix.diagonal w' - Matrix.diagonal G.w) * G.Hmat) *
      sqrtPinv G.lap) ≤ Cs * Real.sqrt ρ

end EulerSparsify


