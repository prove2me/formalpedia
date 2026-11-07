-- Prove2me | Definitions.Def_SoftmaxAttnFD_perturbedFamily
-- name    : SoftmaxAttnFD_perturbedFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:02:29.194695+00:00
-- url     : https://prove2.me/theorems/6516d784-2157-4af1-aa23-f308842f24ba
-- title:
--   The concrete perturbed family of Definition 6.4 and §A.7
-- statement:
--   Fix $\delta=2^{-c\lambda}$. An index $h$ has perturbation $(\delta h,(\delta h)^2,\dots,(\delta h)^d)$. With $U_Y=U_u=U$, Definition A.6 sets
--   $$a_{\rm cap}=d^2(U+2),\quad Z_{\rm top}=d(U+2)(U+1),\quad Z_{\rm cap}=Z_{\rm top}+1+(d-1)a_{\rm cap}U.$$
--   The directions are the unit vectors $e_h$ of $\mathbb R^{d-1}$ for $h<d$ and $e_d=-(1,\dots,1)$, and the unperturbed caps are $c_h=(-a_{\rm cap}e_h,Z_{\rm cap})$.
--
--   The family has caps perturbed with index $h\in[d]$, and sources $y_s$ perturbed with index $d+s$, as in "Index the caps by $h\in[d]$ and the sources by $d+s$, and apply Lemma A.5 once to all these points".
--
--   **Formalization Note** The page applies Lemma A.5 with a uniform $O_d(\lambda)$ bit bound, so its $c_{\rm pert}O_d(\lambda)$ is $c\lambda$ with a constant $c$ depending only on $d$. `ratBits` is the encoding length of a rational in lowest terms.
-- source:
--   Huang, Chen, Softmax Attention with Any Temperature in Fixed Dimension, arXiv:2611.06055 (sha256 a60f7609…), Lemma A.5, Definition A.6, pp.43; §A.7, p.44

import Definitions.Def_SoftmaxAttnFD_Envelope

namespace SoftmaxAttnFD

/-- The encoding length of a rational in lowest terms. -/
def ratBits (x : ℚ) : ℕ := max x.num.natAbs.size x.den.size

/-- All coordinates of a source point have encoding length at most `l`. -/
def SrcBits {d : ℕ} (y : Src d) (l : ℕ) : Prop :=
  (∀ i, ratBits (y.1 i) ≤ l) ∧ ratBits y.2 ≤ l

/-- The perturbation `(δh, (δh)², …, (δh)^d)` of index `h` (arXiv:2611.06055, sha256 a60f7609…,
Lemma A.5, p.43). -/
def ptb {d : ℕ} (δ : ℚ) (h : ℕ) : Src d :=
  (fun i => (δ * h) ^ (i.val + 1), (δ * h) ^ d)

/-- The direction `e_h` of Definition A.6, p.43: the `h`-th unit vector of `ℝ^{d−1}` for `h < d`, and
`e_d = −(1, …, 1)`. Here `h` is 0-based, so the last value is `d − 1`. -/
def capDir (d : ℕ) (h : Fin d) (i : Fin (d - 1)) : ℚ :=
  if h.val = d - 1 then -1 else if i.val = h.val then 1 else 0

/-- `a_cap = d²(U + 2)` (Definition A.6 with `U_Y = U_u = U`, as §A.7 sets them). -/
def aCap (d U : ℕ) : ℕ := d ^ 2 * (U + 2)

/-- `Z_top = d(U + 2)(U + 1)` (Definition A.6). -/
def zTop (d U : ℕ) : ℕ := d * (U + 2) * (U + 1)

/-- `Z_cap = Z_top + 1 + (d − 1) a_cap U` (Definition A.6). -/
def zCap (d U : ℕ) : ℕ := zTop d U + 1 + (d - 1) * aCap d U * U

/-- The unperturbed cap point `c_h = (−a_cap e_h, Z_cap)`, identity permutation (Definition A.6). -/
def capPoint (d U : ℕ) (h : Fin d) : Src d :=
  (fun i => -(aCap d U : ℚ) * capDir d h i, (zCap d U : ℚ))

/-- The concrete perturbed family of Definition 6.4 and §A.7, p.44 ("Index the caps by h ∈ [d] and the
sources by d + s, and apply Lemma A.5 once to all these points"), with `δ_pert = 2^{−cλ}`.

**Formalization Note** `h` is 0-based, so cap `h` has the page's index `h + 1`; a source keeps the
page's index `d + s`. The page applies Lemma A.5 with "a uniform `O_d(λ)` bit bound", so the page's
`c_pert·O_d(λ)` is `c·λ` with a constant `c` depending only on `d`. -/
def perturbedFamily {d : ℕ} (c lam U : ℕ) (y : ℕ → Src d) : Family d where
  src s := y s + ptb ((1 / 2 : ℚ) ^ (c * lam)) (d + s)
  cap h := capPoint d U h + ptb ((1 / 2 : ℚ) ^ (c * lam)) (h.val + 1)

end SoftmaxAttnFD


