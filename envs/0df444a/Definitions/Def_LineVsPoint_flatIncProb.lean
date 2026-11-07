-- Prove2me | Definitions.Def_LineVsPoint_flatIncProb
-- name    : LineVsPoint_flatIncProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:03:48.637321+00:00
-- url     : https://prove2.me/theorems/eb0ea51b-9226-424d-bce7-0f214c42437d
-- title:
--   Point–flat incidence probability, densities $\mu$ and the mixing parameter $\lambda_{m,k}$
-- statement:
--   Let $\mathbb F$ be a finite field with $q$ elements, $X\subseteq\mathbb F^m$ a set of points and $\mathcal T$ a family of affine $k$-flats.
--
--   1. The **incidence probability** $\Pr_{W,\,x\in W}[x\in X,\ W\in\mathcal T]$ chooses a uniformly random $k$-flat $W$ and then a uniformly random point $x\in W$:
--   $$
--   \Pr_{W,\,x\in W}[x\in X,\ W\in\mathcal T]=\frac{1}{\#\{k\text{-flats}\}}\sum_{W\in\mathcal T}\frac{|X\cap W|}{|W|}.
--   $$
--   2. The **densities** are $\mu(X)=|X|/q^m$ and $\mu(\mathcal T)=|\mathcal T|/\#\{k\text{-flats}\}$.
--   3. The **mixing parameter** is the nonnegative number $\lambda_{m,k}$ with $\lambda_{m,k}^2=(q^{m-k}-1)/(q^m-1)$.
--
--   These are the quantities of the expander-mixing Lemma 2.1 and of Lemma 4.1 (ii).
-- source:
--   Dao, Kominers, Thaler, Zheng, Cube-Root Soundness Is Optimal for the Line–versus–Point Test (manuscript, sha256 328a8943…), §2.2 and Lemma 2.1, p.10; Lemma 4.1 (ii), p.17

import Definitions.Def_LineVsPoint_AffFlat

set_option autoImplicit false

namespace LineVsPoint

open Classical in
/-- **Point–flat incidence probability** `Pr_{W, x ∈ W}[x ∈ X, W ∈ T]`: choose a uniformly
random affine `k`-flat `W` of `F^m`, then a uniformly random point `x ∈ W`. Dao, Kominers,
Thaler, Zheng, *Cube-Root Soundness Is Optimal for the Line–versus–Point Test* (manuscript,
sha256 328a8943…), Lemma 2.1, p.10, and Lemma 4.1 (ii), p.17
(`Pr_{P ∈ P_{m,q}, x ∈ P}[P ∈ B, x ∈ X]`).

**Formalization Note.** Literally `(1/#flats) ∑_{W ∈ T} |X ∩ W| / |W|`. -/
noncomputable def flatIncProb {F : Type*} [Field F] [Fintype F] {m k : ℕ}
    (X : Finset (Fin m → F)) (T : Finset (AffFlat F m k)) : ℝ :=
  (∑ W ∈ T, ((X.filter fun x => x ∈ W.carrier).card : ℝ) /
      ((Finset.univ.filter fun x : Fin m → F => x ∈ W.carrier).card : ℝ)) /
    (Fintype.card (AffFlat F m k) : ℝ)

/-- The **density** `µ(X) = |X| / q^m` of a set of points of `F^m` (§2.2, p.10). -/
noncomputable def ptMeasure {F : Type*} [Fintype F] {m : ℕ} (X : Finset (Fin m → F)) : ℝ :=
  (X.card : ℝ) / (Fintype.card F : ℝ) ^ m

/-- The **density** `µ(T) = |T| / #flats` of a family of affine `k`-flats of `F^m`
(§2.2, p.10: "the measure of a set `S` with respect to its appropriate ambient set"). -/
noncomputable def flatMeasure {F : Type*} [Field F] [Fintype F] {m k : ℕ}
    (T : Finset (AffFlat F m k)) : ℝ :=
  (T.card : ℝ) / (Fintype.card (AffFlat F m k) : ℝ)

/-- The **mixing parameter** `λ_{m,k}` of Lemma 2.1 (p.10), the nonnegative number with
`λ²_{m,k} = (q^{m−k} − 1)/(q^m − 1)`. -/
noncomputable def lamMix (q m k : ℕ) : ℝ :=
  Real.sqrt (((q : ℝ) ^ (m - k) - 1) / ((q : ℝ) ^ m - 1))

end LineVsPoint


