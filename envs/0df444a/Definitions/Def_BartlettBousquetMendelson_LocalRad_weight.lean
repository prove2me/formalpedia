-- Prove2me | Definitions.Def_BartlettBousquetMendelson_LocalRad_weight
-- name    : BartlettBousquetMendelson_LocalRad_weight
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:58:51.37927+00:00
-- url     : https://prove2.me/theorems/19527676-79e8-474f-999a-7ead5876adfb
-- title:
--   Weight $w(f)=\min\{r\lambda^k:k\in\mathbb N,\ r\lambda^k\ge T(f)\}$
-- statement:
--   Given a functional $T$, $\lambda>1$ and $r>0$, the **weight** of a function $f$ is
--
--   $$
--   w(f)=\min\{r\lambda^k:k\in\mathbb N,\ r\lambda^k\ge T(f)\},
--   $$
--
--   with $k=0$ allowed; in particular $w(f)=r$ when $T(f)\le r$.
--
--   **Formalization Note** The least $k$ is an infimum over $\mathbb N$; for $\lambda>1$, $r>0$ it exists. Outside that case the value is a junk value that no statement uses.
-- source:
--   Bartlett, Bousquet, Mendelson, Local Rademacher Complexities, Ann. Statist. 33(4) (2005), §3.2, p. 14 (IMS electronic reprint, arXiv:math/0508275v1)

import Mathlib

namespace BartlettBousquetMendelson.LocalRad

/-- **The weight `w(f) = min{r λᵏ : k ∈ ℕ, r λᵏ ≥ T(f)}`.**
Bartlett, Bousquet, Mendelson, *Local Rademacher Complexities*, Ann. Statist. 33(4) (2005) (IMS electronic reprint, arXiv:math/0508275v1), §3.2, p. 14: "Given a class F, λ > 1 and r > 0, let w(f) = min{rλ^k : k ∈ N, rλ^k ≥ T(f)}";
p. 15: "When T(f) ≤ r, w(f) = r."

`weight T r lam f = r * lam ^ k` for the least `k ∈ ℕ` (including `k = 0`) with
`T f ≤ r * lam ^ k`.

**Formalization Note.** `ℕ` contains `0`, as on p. 15. The least `k` is `sInf` of the set of
admissible `k`; for `lam > 1` and `r > 0` (the only case the paper and the mission use) the set
is nonempty and the infimum is attained. Outside that case the set may be empty, `sInf ∅ = 0`, and
the value `r` is a junk value never used. -/
noncomputable def weight {X : Type*} (T : (X → ℝ) → ℝ) (r lam : ℝ) (f : X → ℝ) : ℝ :=
  r * lam ^ sInf {k : ℕ | T f ≤ r * lam ^ k}

end BartlettBousquetMendelson.LocalRad


