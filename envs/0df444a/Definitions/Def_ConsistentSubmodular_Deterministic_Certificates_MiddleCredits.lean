-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_MiddleCredits
-- name    : ConsistentSubmodular_Deterministic_Certificates_MiddleCredits
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:06:30.051385+00:00
-- url     : https://prove2.me/theorems/3b168743-56b6-4840-85c0-3b4ad64e30b4
-- title:
--   Middle-parameter rollback scalars: $\mathrm{cap}$, $I$, $U$, $T$
-- statement:
--   Middle-parameter rollback in the selector for the $3/4$-certificate construction uses four real-valued scalar expressions in the parent parameter $k$ and the residual data $d_0, d, p$ of the parent.
--
--   - `middleCap k d₀` is $2 - \dfrac3k + \dfrac{3(4-k)\,d_0}{k}$, the credit ceiling.
--   - `middleI k d₀ d p` is $(3-k)\,p - k\,d - 2(4-k)\,d_0$.
--   - `middleU k d₀ d p` is $d - 2\,\mathrm{cap}(k,d_0) + 3p - (3-k)\,\dfrac{p + kd + (4-k)\,d_0}{4-k}$.
--   - `middleT k d₀ d p` is
--   $$\bigl(13 - (k-2)^2\bigr)p + \bigl(16 + 5(k-2)^2\bigr)d - (4-k)(27 - k - 2k^2)\,d_0 - 2k(4-k)(k-1).$$
--
--   The file also proves the positivity of the first and third scalar credits for $4/3 \le k \le 2$ from precisely the parent and child source rows.
--
--   These scalars give the sign conditions that exclude middle-parameter rollback in the selector, one case of the proof that every window instance admits a $(3/4, m+3)$-certificate (Theorem 7).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/MiddleCredits.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib

noncomputable section

namespace ConsistentSubmodular

def middleCap (k d₀ : ℝ) : ℝ := 2 - 3 / k + 3 * (4 - k) * d₀ / k

def middleI (k d₀ d p : ℝ) : ℝ := (3 - k) * p - k * d - 2 * (4 - k) * d₀

def middleU (k d₀ d p : ℝ) : ℝ := d - 2 * middleCap k d₀ + 3 * p -
  (3 - k) * ((p + k * d + (4 - k) * d₀) / (4 - k))

def middleT (k d₀ d p : ℝ) : ℝ :=
  (13 - (k - 2) ^ 2) * p + (16 + 5 * (k - 2) ^ 2) * d -
    (4 - k) * (27 - k - 2 * k ^ 2) * d₀ - 2 * k * (4 - k) * (k - 1)

end ConsistentSubmodular

end


