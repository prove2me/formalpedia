-- Prove2me | Definitions.Def_SampleRemoval_sInt
-- name    : SampleRemoval_sInt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:13:44.755646+00:00
-- url     : https://prove2.me/theorems/516bbb1c-07d7-4b42-b884-a8087cfffd49
-- title:
--   Integral stability $s_{\mathrm{int}}=\min\{n-|S|:\mathbf 1_S\in\mathcal W\}$
-- statement:
--   Given observations and a pair $(e,\theta)$ with feasible set $\mathcal W$, the **integral stability** is
--
--   $$
--   s_{\mathrm{int}}=\min\{\,n-|S|:\ \mathbf 1_S\in\mathcal W\,\},
--   $$
--
--   the fewest observations whose removal makes the fit satisfy $\langle e,\beta\rangle\le\theta$. A small $s_{\mathrm{int}}$ means the conclusion drawn from $\langle e,\beta([n])\rangle>\theta$ is fragile.
--
--   **Formalization Note** Encoded as the infimum in $\mathbb N$ of $\{n-|S|:\mathbf 1_S\in\mathcal W\}$, which is attained, hence the paper's minimum, whenever some $\mathbf 1_S$ lies in $\mathcal W$. On an empty set Lean's infimum is the junk value $0$; every statement of the mission about $s_{\mathrm{int}}$ asserts or assumes that some $\mathbf 1_S$ is feasible. The difference $n-|S|$ never truncates since $|S|\le n$.
-- source:
--   Xu, Gao, Hu, Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares, STOC 2027 submission (manuscript sha256 dcd33acebc1ccdc626c7ee41bfabc29795abe2e1cd9267d8cbd66d98f81c4b26), Definition 2.1, p.3 (PDF p.5)

import Mathlib
import Definitions.Def_SampleRemoval_ind
import Definitions.Def_SampleRemoval_feasible

set_option autoImplicit false

namespace SampleRemoval

/-- The integral stability `s_int = min{n − |S| : 1_S ∈ 𝒲}` (Xu, Gao, Hu, *Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares*, STOC 2027 submission (manuscript sha256 dcd33ace…), Definition 2.1, p.3): the
fewest observations whose removal makes the audit succeed.

**Formalization Note** Encoded as the `sInf` in `ℕ` of `{n − |S| : 1_S ∈ 𝒲}`. On a nonempty
subset of `ℕ` the infimum is attained, so it is the paper's minimum; on the empty set Lean's
`sInf` is `0`, a junk value. The paper's `min` presupposes that some `1_S` lies in `𝒲`, and
every statement of the mission about `sInt` asserts or assumes this nonemptiness
(`∃ S, ind S ∈ feasible x y e θ`). `n − |S|` never truncates since `|S| ≤ n`. -/
noncomputable def sInt {n d : ℕ} (x : Fin n → Fin d → ℝ) (y : Fin n → ℝ) (e : Fin d → ℝ)
    (θ : ℝ) : ℕ :=
  sInf {k : ℕ | ∃ S : Finset (Fin n), ind S ∈ feasible x y e θ ∧ k = n - S.card}

end SampleRemoval


