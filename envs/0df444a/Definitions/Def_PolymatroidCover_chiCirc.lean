-- Prove2me | Definitions.Def_PolymatroidCover_chiCirc
-- name    : PolymatroidCover_chiCirc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:19:09.842343+00:00
-- url     : https://prove2.me/theorems/3b22e00c-451c-42e4-b3e2-1f85b2eea44f
-- title:
--   Covering lower bound $\chi^\circ(f)$ of eq. (1)
-- statement:
--   For a polymatroid $f$ on $E$, the paper's lower bound on the covering number is
--
--   $$
--   \chi^\circ(f) := \max\left\{ \left\lceil \frac{\sum_{e \in E} \big(f(e) - f(e \mid T)\big)}{f(T)} \right\rceil : T \subseteq E,\ f(T) > 0 \right\}.
--   $$
--
--   If $E$ can be partitioned into $q$ independent sets then $\sum_{e\in E}(f(e) - f(e \mid T)) \le q\, f(T)$ for every $T$, so $\chi^\circ(f) \le \chi(f)$, the covering number. For matroid rank functions $\chi^\circ$ equals the covering number by Edmonds' matroid partition theorem.
--
--   **Formalization Note** The maximum is a `Finset.sup` over the subsets $T$ with $f(T) > 0$ of the natural ceiling of the rational ratio (the numerator is computed in `ℤ`; for a polymatroid it is nonnegative). The index set is nonempty exactly when $f(E) > 0$; on the empty set the sup is $0$, a value (1) does not define, so every statement using $\chi^\circ$ assumes $f(E) > 0$ or a hypothesis implying it.
-- source:
--   Bérczi, Chandrasekaran, Chekuri, Liu, Ravi, Approximate Covering and Packing in Polymatroids, STOC 2027 submission (manuscript sha256 47f38a6f…), §1.1, p.3 (PDF p.5), eq. (1)

import Mathlib
import Definitions.Def_PolymatroidCover_marg

namespace PolymatroidCover

/-- The covering lower bound `χ°(f)` of eq. (1) (Bérczi–Chandrasekaran–Chekuri–Liu–Ravi, *Approximate Covering and Packing in Polymatroids*, STOC 2027 submission (manuscript sha256 47f38a6f…), §1.1, printed p.3 = PDF p.5):
```
χ°(f) := max { ⌈ ∑_{e∈E} (f(e) − f(e | T)) / f(T) ⌉ : T ⊆ E, f(T) > 0 }.
```

**Formalization Note** The maximum is a `Finset.sup` over the subsets `T` with `0 < f T`
of the natural ceiling `⌈·⌉₊` of the rational ratio; the numerator is computed in `ℤ`.
For a polymatroid the numerator is nonnegative (`f(e | T) ≤ f(e)` by submodularity), so the
natural ceiling is the ceiling of eq. (1). The set over which the maximum is taken is nonempty
exactly when `0 < f univ`; on the empty set `Finset.sup` returns `0`, a value eq. (1) does not
define, so every statement using `chiCirc` assumes `0 < f univ` or a hypothesis implying it. -/
def chiCirc {n : ℕ} (f : Finset (Fin n) → ℕ) : ℕ :=
  (Finset.univ.filter (fun T : Finset (Fin n) => 0 < f T)).sup
    (fun T => ⌈(((∑ e : Fin n, ((f {e} : ℤ) - marg f {e} T) : ℤ) : ℚ) / (f T : ℚ))⌉₊)

end PolymatroidCover


