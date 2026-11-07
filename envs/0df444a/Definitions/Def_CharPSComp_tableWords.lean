-- Prove2me | Definitions.Def_CharPSComp_tableWords
-- name    : CharPSComp_tableWords
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:09:44.443398+00:00
-- url     : https://prove2.me/theorems/57669425-4012-4014-932c-03ba210f2846
-- title:
--   Table 1 parameters $d,s$, $L_{\max}$, admissible transform data $(h,\rho)$ and its word table $\mathcal T$
-- statement:
--   The parameters and constants of the geometric transforms (Table 1, §3.3.1, Appendix B).
--
--   1. $d\triangleq\max\{4,\lceil\log_p(2N)\rceil\}$, $s\triangleq\lfloor d/2\rfloor$ and $L_{\max}\triangleq2\lceil N/s\rceil-1$.
--   2. A pair $(h,\rho)$ is **admissible transform data** for $N$ when $h\in\mathbb F_p[z]$ is monic irreducible of degree $d$ and $\rho\in\mathbb F=\mathbb F_p[z]/(h)$ has multiplicative order at least $L_{\max}$.
--   3. The **table** $\mathcal T$, as a list of machine words: $d$, $s$, the coefficients of $h$, then the coordinates (in $\{0,\dots,p-1\}$, basis $1,\bar z,\dots,\bar z^{d-1}$) of $\rho$, of $\rho^{i}$, $\rho^{-i}$, $\rho^{\binom i2}$, $\rho^{-\binom i2}$ for $0\le i<2L_{\max}$, and of $(1-\rho^j)^{-1}$ for $j\in[L_{\max}-1]$.
--   4. With $R$ of characteristic $p$, $h$ is carried into $R[z]$ and $\mathbb F$ embeds into $E=R[z]/(h)$ coefficientwise (`embedF`).
--
--   **Formalization Note** The page lists "the data for reduction modulo $h$" in $\mathcal T$ without fixing it; here it is $h$ itself, and any reciprocal needed by fast division is recomputed by the consumer within the cost of one reduction (Appendix B includes "preparation of the reciprocal used in division" in that cost). Inverses are `Ring.inverse`, the inverse of a unit.
-- source:
--   Zhu, Faster Power Series Composition in Fixed Positive Characteristic, STOC 2027 submission (manuscript sha256 e63e0527228218d0d0b04691cbfb8b92cc1c9c7abddec6972d71bbab231c6361), Table 1, p.5 (PDF p.6); §3.3.1, p.8 (PDF p.9); Appendix B, p.22 (PDF p.23)

import Mathlib
import Definitions.Def_CharPSComp_rep

namespace CharPSComp

open Polynomial

/-- Extension degree `d ≜ max{4, ⌈log_p(2N)⌉}` (Zhu, *Faster Power Series Composition in Fixed
Positive Characteristic*, STOC 2027 submission (manuscript sha256 e63e0527…), Table 1, p.5,
PDF p.6). -/
def dpar (p N : ℕ) : ℕ := max 4 (Nat.clog p (2 * N))

/-- Block width `s ≜ ⌊d/2⌋` (ibid., Table 1, p.5, PDF p.6). -/
def spar (p N : ℕ) : ℕ := dpar p N / 2

/-- `L_max ≜ 2⌈N/s⌉ − 1` (ibid., §3.3.1, p.8, PDF p.9). -/
def Lmax (p N : ℕ) : ℕ := 2 * ((N + spar p N - 1) / spar p N) - 1

/-- The `d` coordinates of `x ∈ F = F_p[z]/(h)` in the basis `1, z̄, …, z̄^{d−1}`, as integers in
`{0, …, p − 1}`. -/
noncomputable def coordsF {p : ℕ} (h : (ZMod p)[X]) (d : ℕ) (x : AdjoinRoot h) : List ℤ :=
  (List.range d).map fun i => (((rep h x).coeff i).val : ℤ)

/-- The transform table `T` of ibid., §3.3.1, p.8 (PDF p.9), written as a list of words: `d`, `s`,
the coefficients of `h` (degrees `0, …, d`), then the coordinates of `ρ`, of `ρ^i`, of `ρ^{−i}`,
of `ρ^{(i choose 2)}` and of `ρ^{−(i choose 2)}` for `0 ≤ i < 2L_max` (each family in increasing
`i`), and of `(1 − ρʲ)^{−1}` for `j ∈ [L_max − 1]`.

**Formalization Note** "The data for reduction modulo `h`" is taken to be `h` itself: the
reciprocal used by fast division is recomputed by the consumer within the cost of a reduction
(ibid., Appendix B, p.22: the stated coordinate cost includes "preparation of the reciprocal used
in division"). Inverses are `Ring.inverse`, the inverse of a unit. -/
noncomputable def tableWords (p N : ℕ) (h : (ZMod p)[X]) (ρ : AdjoinRoot h) : List ℤ :=
  let d := dpar p N
  let L := Lmax p N
  [(d : ℤ), (spar p N : ℤ)] ++ (List.range (d + 1)).map (fun i => ((h.coeff i).val : ℤ))
    ++ coordsF h d ρ
    ++ (List.range (2 * L)).flatMap (fun i => coordsF h d (ρ ^ i))
    ++ (List.range (2 * L)).flatMap (fun i => coordsF h d (Ring.inverse (ρ ^ i)))
    ++ (List.range (2 * L)).flatMap (fun i => coordsF h d (ρ ^ (i.choose 2)))
    ++ (List.range (2 * L)).flatMap (fun i => coordsF h d (Ring.inverse (ρ ^ (i.choose 2))))
    ++ (List.range (L - 1)).flatMap (fun j => coordsF h d (Ring.inverse (1 - ρ ^ (j + 1))))

/-- `(h, ρ)` is admissible transform data for `N` (ibid., §3.3.1 and Lemma 3, p.8, PDF p.9): `h`
is a monic irreducible polynomial of degree `d` over `F_p`, and `ρ ∈ F = F_p[z]/(h)` has order at
least `L_max`. -/
def IsTransformPair (p N : ℕ) (h : (ZMod p)[X]) (ρ : AdjoinRoot h) : Prop :=
  h.Monic ∧ Irreducible h ∧ h.natDegree = dpar p N ∧ Lmax p N ≤ orderOf ρ

/-- The modulus `h` with coefficients carried into a ring `R` of characteristic `p`, so that
`E = R[z]/(h)`. -/
noncomputable def liftH {p : ℕ} (R : Type*) [CommRing R] [CharP R p] (h : (ZMod p)[X]) : R[X] :=
  h.map (ZMod.castHom (dvd_refl p) R)

/-- The embedding `F ↪ E` of ibid., Appendix B, p.22 (PDF p.23): the inclusion `F_p ↪ R` applied to
the coefficients of the degree-`< d` representative. -/
noncomputable def embedF {p : ℕ} (R : Type*) [CommRing R] [CharP R p] (h : (ZMod p)[X])
    (x : AdjoinRoot h) : AdjoinRoot (liftH R h) :=
  AdjoinRoot.mk (liftH R h) ((rep h x).map (ZMod.castHom (dvd_refl p) R))

end CharPSComp


