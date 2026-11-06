-- Prove2me | Definitions.Def_SpatialSorting_act
-- name    : SpatialSorting_act
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:46:20.105562+00:00
-- url     : https://prove2.me/theorems/baa091fb-9548-4b06-87fb-4fa689d6e88f
-- title:
--   The auxiliary activity at recursion level $n$
-- statement:
--   The auxiliary activities are defined by induction on the filled volume (Eqs. (58)–(60)). This definition unrolls the induction by levels: $a_0\equiv0$, and
--
--   $$a_{n+1,j}(\gamma;\mathbf h)=e^{G_j(\gamma;\mathbf h)+R^{(n)}_j(\gamma;\mathbf h)}\,\chi\bigl(R^{(n)}_j(\gamma;\mathbf h)-\kappa_\beta s_\gamma\bigr),$$
--
--   $$R^{(n)}_j(\gamma;\mathbf h)=\sum_{I\in\mathcal I(\gamma)}\bigl[\log\widehat Z^{(n)}_{i(I)}(I;\mathbf h)-\log\widehat Z^{(n)}_j(I;\mathbf h)\bigr],\qquad \widehat Z^{(n)}_k(V;\mathbf h)=e^{h_k|V|}\sum_{\Gamma\in\mathcal P_k(V)}\prod_{\gamma'\in\Gamma}a_{n,k}(\gamma';\mathbf h),$$
--
--   with $\kappa_\beta=\beta A_{\min}/8$ and $s_\gamma=|\overline\gamma|$.
--
--   **Formalization Note** Every contour admissible in an interior $I\in\mathcal I(\gamma)$ has smaller filled volume than $\gamma$ (Lemma C.1), so $a_{n,j}(\gamma)$ does not change once $n\ge v_\gamma$; at level $v_\gamma$ it is the paper's $\widehat w_j(\gamma;\mathbf h)$ (see `what`). The recursion is structural on $n$; the logarithms are of positive numbers, since the empty family contributes $1$ and activities are nonnegative.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Eqs. (58)–(60), p. 57 (PDF p. 58)

import Mathlib
import Definitions.Def_SpatialSorting_amin
import Definitions.Def_SpatialSorting_Contour
import Definitions.Def_SpatialSorting_boundedComps
import Definitions.Def_SpatialSorting_compLabel
import Definitions.Def_SpatialSorting_G
import Definitions.Def_SpatialSorting_polymers
open Classical Filter Topology

namespace SpatialSorting

/-- The level-`n` approximation of the recursion (58)–(60): level 0 is 0, and level `n+1` evaluates (59) with the interior partition functions (60) built from level `n`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Eqs. (58)–(60), p. 57 (PDF p. 58). -/
noncomputable def act {q : ℕ} [NeZero q] (A : Matrix (Fin q) (Fin q) ℝ) (χ : ℝ → ℝ) (β : ℝ) :
    ℕ → Fin q → Contour q → (Fin q → ℝ) → ℝ
  | 0, _, _, _ => 0
  | n + 1, j, γ, h =>
    let Zl : Fin q → Finset (ℤ × ℤ) → ℝ := fun k V =>
      Real.exp (h k * (V.card : ℝ)) * ∑ Γ ∈ polymers k V, ∏ γ' ∈ Γ, act A χ β n k γ' h
    let Rv : ℝ := ∑ J ∈ boundedComps γ, (Real.log (Zl (compLabel γ J) J) - Real.log (Zl j J))
    Real.exp (G A β h j γ + Rv) * χ (Rv - β * amin A / 8 * (γ.support.card : ℝ))

end SpatialSorting


