-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_energy
-- name    : KawasakiSOS_Threshold_energy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:58:57.528202+00:00
-- url     : https://prove2.me/theorems/7e705634-1366-4b5e-9ab2-e95a09d09ab9
-- title:
--   The energy $M(h)$
-- statement:
--   For a height vector $h:\mathbb Z_k\to\mathbb Z_{\ge0}$, the energy of $h$ is
--
--   $$M(h)=\sum_{i\in\mathbb Z_k}\min\bigl(h(i),h(i+1)\bigr).$$
--
--   For $h\in\Omega_{n,k}$ it satisfies $p(h)=2n-2M(h)$, so for $\lambda>1$ a configuration has large stationary weight exactly when its energy is small.
--
--   **Formalization Note** The energy is defined on every height vector, since the paper also evaluates it at vectors of total mass $n-1$.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), (1), p. 5 (PDF p. 6)

import Mathlib

namespace KawasakiSOS.Threshold

/-- The energy `M(h) = ∑_{i ∈ ℤ_k} min(h(i), h(i+1))` of (1). Formalization Note: defined on all height vectors, because Lemma 2.2 evaluates it at `z − e_i`, which is not in `Ω`.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), (1), p. 5 (PDF p. 6). -/
def energy {k : ℕ} [NeZero k] (h : ZMod k → ℕ) : ℕ :=
  ∑ i, min (h i) (h (i + 1))

end KawasakiSOS.Threshold


