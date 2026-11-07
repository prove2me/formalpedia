-- Prove2me | Definitions.Def_HWMaskLeak_maskSumDist
-- name    : HWMaskLeak_maskSumDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:30:45.785199+00:00
-- url     : https://prove2.me/theorems/4a94dcf3-c2b5-4047-9e70-1784e246598d
-- title:
--   Last-share-public distance $\Delta_m$, eqs. (2)–(3)
-- statement:
--   Let $X_1,\dots,X_m$ be independent and uniform over $G=\mathbb Z/N\mathbb Z$, put $\mathbf W=(\mathrm{wt}(X_1),\dots,\mathrm{wt}(X_m))$ and $T=X_1+\cdots+X_m\in G$, and let $U$ be uniform over $G$ and independent of $\mathbf W$. Then
--   $$
--   \Pr[\mathbf W=w,\,T=x]=\frac{\#\{X\in G^m:\ \mathrm{wt}(X_j)=w_j\ \forall j,\ X_1+\cdots+X_m=x\}}{N^m},\qquad
--   \Pr[\mathbf W=w,\,U=x]=\frac{\#\{X\in G^m:\ \mathrm{wt}(X_j)=w_j\ \forall j\}}{N^{m+1}},
--   $$
--   and
--   $$
--   \Delta_m:=\|D(\mathbf W,T)-D(\mathbf W,U)\|_{\mathrm{TV}}=\frac12\sum_{w\in W^m}\sum_{x\in G}\bigl|\Pr[\mathbf W=w,T=x]-\Pr[\mathbf W=w,U=x]\bigr|.
--   $$
--   The paper's $\Delta_{k-1}$ (eq. (3) and Lemma 3.1) is $\Delta_m$ with $m=k-1$: it measures what the weights of the first $k-1$ shares reveal about their exact sum, equivalently about the last share of a sharing when that share is public.
--
--   **Formalization Note** $T$ is the exact sum in $G$, not its weight. Distributions are normalized counts; the sum over $W^m\times G$ contains both supports.
-- source:
--   Biswas, Hwang, Maji, Shkredov, Ye, When Masks Leak Their Weight: From Additive Sharing to Learning with Physical Rounding, preprint (version of October 31, 2026, sha256 ab686360…), §1.1.1, p.6, eqs. (2)–(3); Lemma 3.1, p.18

import Mathlib
import Definitions.Def_HWMaskLeak_wt

namespace HWMaskLeak

/-- **The law of `(W, T)`, eq. (2)** (Biswas, Hwang, Maji, Shkredov, Ye, *When Masks Leak Their
Weight: From Additive Sharing to Learning with Physical Rounding*, preprint (version of October 31,
2026, sha256 ab686360…), §1.1.1, p.6): for `X₁, …, X_m` independent and uniform over `G = ℤ/Nℤ`,
`W = (wt(X₁), …, wt(X_m))` and `T = X₁ + ⋯ + X_m`. The mass of `(W, T)` at `(w, x)` is
`#{X ∈ G^m : wt(X_j) = w_j ∀ j, X₁ + ⋯ + X_m = x} / N^m`. -/
noncomputable def sumLaw (N : ℕ) [NeZero N] (m : ℕ) (w : Fin m → ℕ) (x : ZMod N) : ℝ :=
  ((Finset.univ.filter (fun X : Fin m → ZMod N =>
      (∀ j, wt N (X j) = w j) ∧ ∑ j, X j = x)).card : ℝ) / (N : ℝ) ^ m

/-- **The law of `(W, U)`** (same preprint, §1.1.1, p.6, after (3)): `U` is uniform over `G` and
independent of `W`, so the mass at `(w, x)` is `#{X ∈ G^m : wt(X_j) = w_j ∀ j} / N^{m+1}`. -/
noncomputable def sumLawUnif (N : ℕ) [NeZero N] (m : ℕ) (w : Fin m → ℕ) (_x : ZMod N) : ℝ :=
  ((Finset.univ.filter (fun X : Fin m → ZMod N => ∀ j, wt N (X j) = w j)).card : ℝ) /
    (N : ℝ) ^ (m + 1)

/-- **The last-share-public distance `Δ_m`, eq. (3)** (same preprint, §1.1.1, p.6; also Lemma 3.1,
p.18): `Δ_m := ‖D(W, T) − D(W, U)‖_TV = ½ Σ_{w ∈ W^m} Σ_{x ∈ G} |P_{W,T}(w, x) − P_{W,U}(w, x)|`, with
`W = wt(G)`. The paper's `Δ_{k−1}` is `maskSumDist N (k − 1)`.

**Formalization Note** Distributions are normalized counts on finite sets; the TV sum runs over
`W^m × G`, which contains both supports. `T` is the exact sum in `G`, not its weight. -/
noncomputable def maskSumDist (N : ℕ) [NeZero N] (m : ℕ) : ℝ :=
  (1 / 2) * ∑ w ∈ Fintype.piFinset (fun _ : Fin m => weights N),
    ∑ x : ZMod N, |sumLaw N m w x - sumLawUnif N m w x|

end HWMaskLeak


