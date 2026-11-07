-- Prove2me | Definitions.Def_GeoQAC_avgSens
-- name    : GeoQAC_avgSens
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:29:14.158201+00:00
-- url     : https://prove2.me/theorems/c4680be0-0aa6-4216-a3e9-f7752cc3d649
-- title:
--   Sensitivity $s_f(x)$ and average sensitivity $\mathrm{as}(f)$
-- statement:
--   Let $f:\{0,1\}^n\to\{0,1\}$ and let $e_j$ be the string with a single one in coordinate $j$. The **sensitivity** of $f$ at $x$ is
--   $$
--   s_f(x)=\big|\{j\in[n] : f(x)\neq f(x\oplus e_j)\}\big|,
--   $$
--   and its **average sensitivity** (total influence) is $\mathrm{as}(f)=\mathbb E_x\, s_f(x)$, the expectation over uniform $x\in\{0,1\}^n$. The second moment $\mathbb E_x[s_f(x)^2]$ appears in the sensitivity–variance identity.
--
--   **Formalization Note** Boolean functions are maps $(\mathrm{Fin}\,n\to\mathrm{Bool})\to\mathrm{Bool}$; expectations are sums divided by $2^n$.
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), §2.1, p.9; Lemma 3.15, p.25

import Mathlib

namespace GeoQAC

/-!
# Sensitivity and average sensitivity

Dong, Ou, Yao, arXiv:2604.07178 (version of 2026-11-03), §2.1, p.9: "The sensitivity of f at x is
s_f(x) = |{j ∈ [n] : f(x) ≠ f(x ⊕ e_j)}|. Its average sensitivity, also called total influence, is
as(f) = E_x s_f(x)." Expectations over `x ∈ {0,1}^n` are uniform (p.9).

**Formalization Note.** A Boolean function is `f : (Fin n → Bool) → Bool`; `x ⊕ e_j` flips bit `j`.
`sensSqMean f` is `E_x[s_f(x)²]` (Lemma 3.15, p.25).
-/

/-- The sensitivity `s_f(x)`: the number of coordinates whose flip changes `f(x)` (p.9). -/
def sens {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun j => f x ≠ f (Function.update x j (!x j))).card

/-- The average sensitivity `as(f) = E_x s_f(x)`, uniform over `{0,1}^n` (p.9). -/
noncomputable def avgSens {n : ℕ} (f : (Fin n → Bool) → Bool) : ℝ :=
  (∑ x, (sens f x : ℝ)) / 2 ^ n

/-- The second moment `E_x[s_f(x)²]` (Lemma 3.15, p.25). -/
noncomputable def sensSqMean {n : ℕ} (f : (Fin n → Bool) → Bool) : ℝ :=
  (∑ x, (sens f x : ℝ) ^ 2) / 2 ^ n

end GeoQAC


