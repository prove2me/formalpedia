-- Prove2me | Definitions.Def_MaxCutSample2027_Coreset_Supplement_rSigned
-- name    : MaxCutSample2027_Coreset_Supplement_rSigned
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T10:00:00.126495+00:00
-- url     : https://prove2.me/theorems/a8be82b3-2938-4d3d-8061-62afeb6f9b17
-- title:
--   r-way sample box and independent signed maximum
-- statement:
--   Let $p$ be a positive probability vector, let $x,y$ be independent samples of size $k\ge1$, and write $P_x,P_y$ for their empirical laws. Define
--   $$B^{(r)}_{x,y}=\{c:\sum_j|c^j_v|\le p_v+P_x(v)+P_y(v)\text{ for every }v\}.$$
--   For independent uniform signs $\sigma_{ij}$ with $i\in[k]$ and $0\le j\le r$, set
--   $$R(x,y,\sigma)=\max_{c\in B^{(r)}_{x,y}}\left|\frac1k\sum_i\sum_{j=1}^r(\sigma_{i0}+\sigma_{ij})(Kc^j)_{x_i}\right|.$$
--   The expected signed maximum is the nested finite average over $x,y\sim p^k$ and all $k(r+1)$ signs. The extra sign is shared across parts for a fixed sample position; each part also has its own sign. This is the exact quantity in both Lemmas 5.7 and 5.8. The feasible box bounds the sum of absolute part masses, and its continuous objective attains its maximum.
-- source:
--   Itamar Bender, Robert Krauthgamer, STOC 2027 submission #147 (October 2026), §5.4, eqs. (5.18), (5.19), (5.23), p. 29–31. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/147.pdf (PDF SHA-256 54bb82836bdc80e7729d444c36f7299cb7d50838d4ee557decb3495e61236fa7; printed page = PDF page).

import Definitions.Def_MaxCutSample2027_Coreset_Supplement_recovery
import Definitions.Def_MaxCutSample2027_Coreset_Supplement_rFractional
open scoped BigOperators
noncomputable section

namespace MaxCutSample2027.Coreset.Supplement

/-- Equation (5.18): an l1 bound across parts at each vertex. -/
def boxR {V : Type*} [DecidableEq V] {k : ℕ} (r : ℕ)
    (p : V → ℝ) (x y : Fin k → V) : Set (Fin r → V → ℝ) :=
  {c | ∀ v, ∑ j, |c j v| ≤ p v + empirical x v + empirical y v}

/-- Coordinate 0 is shared, coordinates j.succ are the r individual signs. -/
def signedMaximumR {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} (r : ℕ)
    (L : V → V → ℝ) (p : V → ℝ) (x y : Fin k → V)
    (σ : Fin k → Fin (r + 1) → Bool) : ℝ :=
  sSup ((fun c => |(∑ i, ∑ j : Fin r,
    (signValue (σ i 0) + signValue (σ i j.succ)) * matVec L (c j) (x i)) / (k : ℝ)|)
    '' boxR r p x y)

def expectedSignedR {V : Type*} [Fintype V] [DecidableEq V]
    (r k : ℕ) (L : V → V → ℝ) (p : V → ℝ) : ℝ :=
  sampleAverage p k (fun x => sampleAverage p k (fun y =>
    matrixSignAverage k (r + 1) (signedMaximumR r L p x y)))

end MaxCutSample2027.Coreset.Supplement


