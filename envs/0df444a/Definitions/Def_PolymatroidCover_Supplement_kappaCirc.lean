-- Prove2me | Definitions.Def_PolymatroidCover_Supplement_kappaCirc
-- name    : PolymatroidCover_Supplement_kappaCirc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:50:15.046253+00:00
-- url     : https://prove2.me/theorems/e3e5f664-25f8-425b-acca-22be8054950c
-- title:
--   Packing upper bound $\kappa^\circ(f)$ of eq. (2)
-- statement:
--   Let $f$ be a polymatroid on $E$ with $f(E) > 0$, and write $f(e \mid T) := f(T \cup \{e\}) - f(T)$. Following Călinescu, Chekuri and Vondrák, the paper defines
--
--   $$
--   \kappa^\circ(f) := \min\left\{ \left\lfloor \frac{\sum_{e\in E} f(e \mid T)}{f(E) - f(T)} \right\rfloor : T \subseteq E,\ f(T) < f(E) \right\}.
--   $$
--
--   If $B$ is a generator then $\sum_{e\in B} f(e\mid T) \ge f(E) - f(T)$ by submodularity, so $k$ pairwise disjoint generators force $\sum_{e\in E} f(e\mid T) \ge k\,(f(E)-f(T))$ for every $T$; hence $\kappa(f) \le \kappa^\circ(f)$. Theorem 1.3 shows that for $d$-polymatroids $\kappa(f) \ge \lfloor \kappa^\circ(f)/d \rfloor$.
--
--   **Formalization Note** The floor is part of the definition. The minimum ranges over the subsets $T$ with $f(T) < f(E)$, a set that is nonempty exactly when $f(E) > 0$ (take $T=\emptyset$); on the empty set the definition returns $0$, and every statement using it assumes $f(E) > 0$. The numerator is computed in $\mathbb Z$, the ratio in $\mathbb Q$, and the floor is the natural floor, which agrees with the floor because the numerator is nonnegative for a monotone $f$.
-- source:
--   Bérczi, Chandrasekaran, Chekuri, Liu, Ravi, Approximate Covering and Packing in Polymatroids, STOC 2027 submission (manuscript sha256 47f38a6f…), §1.1, p.4 (PDF p.6), eq. (2), "κ◦(f)"

import Mathlib
import Definitions.Def_PolymatroidCover_marg

namespace PolymatroidCover.Supplement

open PolymatroidCover

/-- The packing upper bound `κ°(f)` of eq. (2) of Călinescu–Chekuri–Vondrák, as recalled in
Bérczi–Chandrasekaran–Chekuri–Liu–Ravi, *Approximate Covering and Packing in Polymatroids*, STOC 2027 submission (manuscript sha256 47f38a6f…), §1.1, printed p.4 = PDF p.6:
```
κ°(f) := min { ⌊ ∑_{e∈E} f(e | T) / (f(E) − f(T)) ⌋ : T ⊆ E, f(T) < f(E) }.
```

**Formalization Note** The floor is part of the definition (it is visible on the rendered page).
The minimum is a `Finset.inf'` over the subsets `T` with `f T < f univ` of the natural floor
`⌊·⌋₊` of the rational ratio; `f(e | T)` is the published `marg f {e} T = f({e} ∪ T) − f(T)`
(in `ℤ`). For a monotone `f` the numerator is nonnegative and the denominator positive, so
`⌊·⌋₊` is the floor of eq. (2). The index set is nonempty exactly when `0 < f univ` (take
`T = ∅`); on the empty index set eq. (2) is undefined and this definition returns `0`, so every
statement using `kappaCirc` assumes `0 < f univ`. -/
noncomputable def kappaCirc {n : ℕ} (f : Finset (Fin n) → ℕ) : ℕ :=
  if h : (Finset.univ.filter (fun T : Finset (Fin n) => f T < f Finset.univ)).Nonempty then
    (Finset.univ.filter (fun T : Finset (Fin n) => f T < f Finset.univ)).inf' h
      (fun T => ⌊(((∑ e : Fin n, marg f {e} T : ℤ) : ℚ) /
        ((f Finset.univ : ℚ) - (f T : ℚ)))⌋₊)
  else 0

end PolymatroidCover.Supplement


