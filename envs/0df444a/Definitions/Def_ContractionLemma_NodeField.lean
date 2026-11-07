-- Prove2me | Definitions.Def_ContractionLemma_NodeField
-- name    : ContractionLemma_NodeField
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:56:24.470742+00:00
-- url     : https://prove2.me/theorems/1d1353ff-7000-4522-b527-23fdff062f02
-- title:
--   The node ring $\mathcal O=\mathbb Z_{(2)}[U]/(f)$, congruence, binary nodes
-- statement:
--   Let $f\in\mathbb Z[U]$ be monic with $f$ mod $2$ irreducible, and let $\mathbb Z_{(2)}$ be the rationals with odd denominators. The ring of the interpolation nodes is $\mathcal O=\mathbb Z_{(2)}[U]/(f)$, and $x\equiv y\pmod{2^p}$ means $x-y\in 2^p\mathcal O$. The nodes are the elements $\sum_k b_kU^k$ with $b_k\in\{0,1\}$.
--
--   **Formalization Note** $\mathcal O$ is represented inside $\mathbb Q[U]/(f)$: an element lies in $\mathcal O$ when all its coordinates on the power basis have odd denominators. Fractions of $\mathcal O$ are thus available for the weights $\Omega_{t,j}$.
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), App. A.9.3, p.96 ("The ring")

import Mathlib

set_option autoImplicit false

namespace ContractionLemma

open Polynomial

/-- **The node ring** — Gajulapalli, *The Contraction Lemma Beyond ETH* (manuscript, sha256
049caea1…), App. A.9.3, p.96 ("The ring").

For `f ∈ ℤ[U]` monic with `f mod 2` irreducible, the paper's ring is `O = ℤ_{(2)}[U]/(f)`, with
`ℤ_{(2)}` the rationals with odd denominators. It is computed inside
`NodeField f = ℚ[U]/(f)`: an element of `O` is an element of `NodeField f` whose coordinates
(the coefficients of its reduction modulo `f`, of degree `< deg f`) are rationals with odd
denominators (`IsInO`).

**Formalization Note.** Since `f` is monic, `O` embeds in `ℚ[U]/(f)` and the coordinates are
those of the power basis `1, U, …, U^{deg f − 1}`. -/
abbrev NodeField (f : ℤ[X]) := AdjoinRoot (f.map (Int.castRingHom ℚ))

/-- The admissible moduli: `f` monic of degree `d` with `f mod 2` irreducible (p.96). -/
def IsNodePoly (f : ℤ[X]) (d : ℕ) : Prop :=
  f.Monic ∧ f.natDegree = d ∧ Irreducible (f.map (Int.castRingHom (ZMod 2)))

/-- The coordinates of `x ∈ ℚ[U]/(f)`: its representative polynomial reduced modulo `f`
(the unique representative of degree `< deg f` when `f` is monic). -/
noncomputable def coords (f : ℤ[X]) (x : NodeField f) : ℚ[X] :=
  Function.surjInv (AdjoinRoot.mk_surjective (g := f.map (Int.castRingHom ℚ))) x %ₘ
    f.map (Int.castRingHom ℚ)

/-- `x ∈ O`: every coordinate of `x` is a rational with odd denominator. -/
def IsInO (f : ℤ[X]) (x : NodeField f) : Prop := ∀ k, ¬ 2 ∣ ((coords f x).coeff k).den

/-- Congruence modulo `2^p` in `O` (p.64, p.96): `x − y ∈ 2^p O`. -/
def CongrO (f : ℤ[X]) (p : ℕ) (x y : NodeField f) : Prop :=
  IsInO f (((2 : ℚ) ^ p)⁻¹ • (x - y))

/-- The binary node `∑_k b_k U^k` with `b_k ∈ {0, 1}` (p.96). -/
noncomputable def binNode (f : ℤ[X]) (b : Fin f.natDegree → Bool) : NodeField f :=
  ∑ k, if b k then AdjoinRoot.root (f.map (Int.castRingHom ℚ)) ^ (k : ℕ) else 0

end ContractionLemma


