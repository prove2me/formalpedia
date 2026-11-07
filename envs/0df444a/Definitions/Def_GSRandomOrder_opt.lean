-- Prove2me | Definitions.Def_GSRandomOrder_opt
-- name    : GSRandomOrder_opt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:59:45.945234+00:00
-- url     : https://prove2.me/theorems/5f9b5395-e482-4e85-8d92-7265537b1a78
-- title:
--   $\mathrm{OPT}(v)=\max_{S\subseteq N}v(S)$
-- statement:
--   For a valuation $v$ on $N$,
--   $$
--   \mathrm{OPT}(v)=\max_{S\subseteq N}v(S).
--   $$
--   It is the benchmark of the GS secretary problem: the best value an offline algorithm that knows $v$ could select.
--
--   **Formalization Note** The maximum is `Finset.sup` over all subsets in `WithBot ℝ`; for a valuation it is at least $v(\emptyset)=0$, hence a real number, which `unbotD 0` returns.
-- source:
--   Paes Leme, Pál, Patel, Gross Substitutes Welfare in Random Order, STOC 2027 submission (manuscript sha256 69787f50…), §1, p.2, eq. (1)

import Mathlib

set_option autoImplicit false

namespace GSRandomOrder

/-- **`OPT(v) = max_{S ⊆ N} v(S)`** (Paes Leme, Pál, Patel, *Gross Substitutes Welfare in Random
Order*, STOC 2027 submission, manuscript sha256 69787f50…, §1, p.2, eq. (1)).

**Formalization Note.** The maximum over all `S ⊆ Fin n` is `Finset.univ.sup v` in `WithBot ℝ`.
For a valuation (`v ∅ = 0`) it is at least `0`, hence a real number, and `unbotD 0` returns it;
the fallback `0` is never used for a valuation. -/
noncomputable def opt {n : ℕ} (v : Finset (Fin n) → WithBot ℝ) : ℝ :=
  ((Finset.univ : Finset (Finset (Fin n))).sup v).unbotD 0

end GSRandomOrder


