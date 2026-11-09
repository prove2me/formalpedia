-- Prove2me | Definitions.Def_MaxCutSample2027_Coreset_signed
-- name    : MaxCutSample2027_Coreset_signed
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:48:00.436717+00:00
-- url     : https://prove2.me/theorems/b1393368-80a3-4639-9101-dc269461dfce
-- title:
--   Sample-dependent boxes and signed maxima
-- statement:
--   Let $X,Y\in V^k$ be samples with empirical frequencies $P_X,P_Y$, and let $p$ be a positive probability vector. Define
--   $$B_{X,Y}=\{c\in\mathbb R^V:|c_v|\le p_v+P_X(v)+P_Y(v)\ \forall v\},$$
--   $$S_L(X,Y,\sigma)=\max_{c\in B_{X,Y}}\left|\frac1k\sum_{i=0}^{k-1}\varepsilon(\sigma_i)(Lc)_{X_i}\right|,\qquad (Lc)_u=\sum_v L_{uv}c_v.$$
--   For a nonempty compact $T\subseteq\mathbb R^k$ and a continuous scalar map $g$, the contraction maximum is
--   $$C_{T,g}(\sigma)=\max_{t\in T}\left|\frac1k\sum_{i=0}^{k-1}\varepsilon(\sigma_i)g(t_i)\right|.$$
--   Here $k\ge1$ in all theorem uses. These definitions specify exactly the extrema in Lemmas 2.7, 2.8, and A.1, with the same signs as the finite averaging module.
--
--   **Formalization Note** Real suprema encode these maxima. The sample box has finite positive coordinate radii and is compact and nonempty. The contraction theorem assumes compact nonempty $T$ and a Lipschitz $g$, which ensures continuity. All relevant extrema are therefore attained. An empty $T$ would give the default real supremum zero; Lemma A.1 excludes it.
-- source:
--   Itamar Bender, Robert Krauthgamer, STOC 2027 submission #147 (October 2026), Lemma 2.7, p. 11; Lemma 2.8, p. 12; Lemma A.1, p. 33. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/147.pdf (PDF SHA-256 54bb82836bdc80e7729d444c36f7299cb7d50838d4ee557decb3495e61236fa7).

import Definitions.Def_MaxCutSample2027_Coreset_fractional
open scoped BigOperators
noncomputable section

namespace MaxCutSample2027.Coreset

/-- The random symmetric compact box in Lemma 2.7. -/
def boxB {V : Type*} [DecidableEq V] {k : ℕ} (p : V → ℝ)
    (x y : Fin k → V) : Set (V → ℝ) :=
  {c | ∀ v, |c v| ≤ p v + empirical x v + empirical y v}

/-- The exact maximum in (2.15) and (2.18), with its 1/k factor. -/
def signedMaximum {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (L : V → V → ℝ) (p : V → ℝ) (x y : Fin k → V) (σ : Fin k → Bool) : ℝ :=
  sSup ((fun c : V → ℝ =>
    |(∑ i, signValue (σ i) * (∑ v, L (x i) v * c v)) / (k : ℝ)|) '' boxB p x y)

/-- Lemma A.1's maximum, for a nonempty compact T and k ≥ 1. -/
def contractionMaximum {k : ℕ} (T : Set (Fin k → ℝ)) (g : ℝ → ℝ)
    (σ : Fin k → Bool) : ℝ :=
  sSup ((fun t : Fin k → ℝ => |(∑ i, signValue (σ i) * g (t i)) / (k : ℝ)|) '' T)

end MaxCutSample2027.Coreset


