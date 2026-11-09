-- Prove2me | Definitions.Def_WalkTreeCluster_LocalVariationConst
-- name    : WalkTreeCluster_LocalVariationConst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:52:37.90106+00:00
-- url     : https://prove2.me/theorems/1c5b32a1-df7b-421b-8a49-8bbb85f40d51
-- title:
--   The conclusion of Lemma 8.3 with a constant $c_{\rm loc}$
-- statement:
--   A real $c>0$ has the *local-variation property* if for every graph and family of clusters in the parameter range ($d\ge1$, undirected, no parallel edges, $0<\phi\le1$, $\epsilon>0$, $a\le10^{-4}$) and every cluster $C$:
--   1. $\displaystyle\sum_{i\ge1}\alpha^{2i}\sum_{u\in C}\|F_i(\mathbb 1_u-u_C)\|_{F,w}^4\le 2c\,a^{66}|C|$;
--   2. there are numbers $e_i(u)\ge0$ ($i\ge1$, $u\in V$) with
--   $$\alpha^{2i}\big\|\mathbb E[X_{u,i}^{\otimes2}]\big\|_{F,w}^2\le128\frac{\alpha^i}{|C|}+e_i(u)\quad(i\ge1,\ \alpha^i\le|C|),\qquad\sum_{i\ge1}\sum_{u\in C}e_i(u)\le c\,a^{62}|C| .$$
--
--   Lemma 8.3 asserts that such a $c=c_{\rm loc}$ exists; Table 1 defines $c_0$ from it, and Lemmas 8.1, 8.7, 9.1, 9.4, 9.6, 9.7 take it as a parameter.
--
--   **Formalization Note.** The constant comes before every graph ("absolute", "does not depend on $V\setminus C$"); both infinite sums are in $[0,\infty]$.
-- source:
--   Kapralov–Kochetkova, Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise, STOC 2027 submission (manuscript sha256 638eeef1…), Lemma 8.3, p.48; Table 1, p.18

import Mathlib
import Definitions.Def_WalkTreeCluster_Filter

namespace WalkTreeCluster

/-!
# The conclusion of Lemma 8.3 with a given constant `c_loc`

Kapralov–Kochetkova, *Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise*, STOC 2027
submission (manuscript sha256 638eeef1…), Lemma 8.3, p.48; Table 1 ("c_loc — absolute constant in
Lemma 8.3"), p.18.

`LocalVariationConst c` says: `c > 0`, and for every graph and family of clusters in the parameter
range of Lemma 8.3 (`d ≥ 1`, undirected, no parallel edges, `0 < ϕ ≤ 1`, `ϵ > 0`, `a ≤ 10⁻⁴`) and
every cluster `C`,
1. (local variation) `Σ_{i ≥ 1} α^{2i} Σ_{u ∈ C} ‖F_i(1_u − u_C)‖⁴_{F,w} ≤ 2 c a^{66} |C|`;
2. (collision-moment profile) there are numbers `e_i(u) ≥ 0` (`i ≥ 1`, `u ∈ V`) with
   `α^{2i} ‖E[X_{u,i}^{⊗2}]‖²_{F,w} ≤ 128 α^i/|C| + e_i(u)` whenever `i ≥ 1` and `α^i ≤ |C|`, and
   `Σ_{i ≥ 1} Σ_{u ∈ C} e_i(u) ≤ c a^{62} |C|`.
Lemma 8.3 asserts that some `c` has this property; Table 1 defines `c₀` from such a `c`, and the
later lemmas use it.

**Formalization Note.** The constant comes before every graph ("absolute", "does not depend on
`V ∖ C`"). Both infinite sums have nonnegative terms and are summed in `ℝ≥0∞`. The sequence
`e_i(u)` is indexed by `i + 1` for `i : ℕ`. The parameter range is that of Table 1 without the
condition `ϵ ≤ c₀ϕ²`, since `c₀` is defined from `c_loc`; `a ≤ 10⁻⁴` is the Table 1 bound on `a`.
-/

/-- The conclusion of Lemma 8.3 holds with the constant `c`. -/
def LocalVariationConst (c : ℝ) : Prop :=
  0 < c ∧
  ∀ (n d : ℕ) (nbr : Fin n → Fin d → Fin n) (ϵ ϕ : ℝ) (𝒞 : Finset (Finset (Fin n))),
    1 ≤ d → IsUndirected nbr → NoParallel nbr →
    0 < ϕ → ϕ ≤ 1 → 0 < ϵ → aParam ϵ ϕ ≤ 1 / 10 ^ 4 →
    IsClusterFamily nbr ϵ ϕ 𝒞 →
    ∀ C ∈ 𝒞,
      (∑' i : ℕ, ENNReal.ofReal (alphaParam ϵ ϕ ^ (2 * (i + 1)) *
          ∑ u ∈ C, (wNormSq (aParam ϵ ϕ)
            (filter nbr ϵ ϕ (i + 1) (coord u - clusterMean C))) ^ 2)) ≤
        ENNReal.ofReal (2 * c * aParam ϵ ϕ ^ 66 * C.card) ∧
      ∃ e : ℕ → Fin n → ℝ, (∀ i u, 0 ≤ e i u) ∧
        (∀ (i : ℕ) (u : Fin n), alphaParam ϵ ϕ ^ (i + 1) ≤ C.card →
          alphaParam ϵ ϕ ^ (2 * (i + 1)) *
              secondMomentNormSq (aParam ϵ ϕ) (walkLaw nbr ϵ ϕ (i + 1) u) ≤
            128 * alphaParam ϵ ϕ ^ (i + 1) / C.card + e i u) ∧
        (∑' i : ℕ, ENNReal.ofReal (∑ u ∈ C, e i u)) ≤
          ENNReal.ofReal (c * aParam ϵ ϕ ^ 62 * C.card)

end WalkTreeCluster


