-- Prove2me | Definitions.Def_PRUPermLayer_distSub
-- name    : PRUPermLayer_distSub
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:25:50.260035+00:00
-- url     : https://prove2.me/theorems/3c86b632-3195-4916-bcd6-30eaec7edec4
-- title:
--   Distinct subspace $\mathrm{Dist}_{N,t}$
-- statement:
--   The **distinct subspace** $\mathrm{Dist}_{N,t} \subseteq (\mathbb C^N)^{\otimes t}$ is spanned by the basis states $|x_1, \dots, x_t\rangle$ with pairwise different $x_i$.
--
--   It contains the states on which a random permutation and a Haar-random unitary act alike (no two registers share a label).
--
--   **Formalization Note** $(\mathbb C^N)^{\otimes t}$ has basis labels $x = (x_1, \dots, x_t)$; "pairwise different" is injectivity of $i \mapsto x_i$. For $t \le 1$ it is the whole space.
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Definition 2.1, p.10 (PDF p.12)

import Mathlib

namespace PRUPermLayer

/-- The distinct subspace `Dist_{N,t} ⊆ (ℂ^N)^{⊗t}`, spanned by the basis states
`|x₁, …, x_t⟩` with pairwise different `xᵢ` (Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Definition 2.1, p.10 (PDF p.12)).

**Formalization Note** `(ℂ^N)^{⊗t}` is `EuclideanSpace ℂ (Fin t → Fin N)`, register `i : Fin t`
being the source's register `i + 1`; "pairwise different" is injectivity of `x`. For `t ≤ 1` it is
the whole space. -/
noncomputable def distSub (N t : ℕ) : Submodule ℂ (EuclideanSpace ℂ (Fin t → Fin N)) :=
  Submodule.span ℂ (Set.range fun x : {x : Fin t → Fin N // Function.Injective x} =>
    EuclideanSpace.single x.1 (1 : ℂ))

end PRUPermLayer


