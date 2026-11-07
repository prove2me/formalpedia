-- Prove2me | Definitions.Def_BorderD4_SPSP
-- name    : BorderD4_SPSP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:58:14.493196+00:00
-- url     : https://prove2.me/theorems/8b6c4b79-9727-4dd5-a5bf-6614cfddcd5e
-- title:
--   $\Sigma^{[k]}\Pi\Sigma\Pi^{[\delta]}$ circuits and their size
-- statement:
--   A $\Sigma^{[k]}\Pi\Sigma\Pi^{[\delta]}$ circuit over a ring $R$ has, from the top: one addition gate of fan-in at most $k$; product gates; addition gates; and product gates of fan-in at most $\delta$. The middle two layers have unrestricted fan-in, and scalars on wires are free. Such a circuit computes
--   $$\sum_{i=1}^{t}T_i,\qquad T_i=c_i\prod_{m}q_m^{e_{i,m}},\qquad q_m=\sum_b a_{m,b}\,x^{\beta_b},\quad \deg x^{\beta_b}\le\delta,\quad t\le k.$$
--   The size is the number of gates plus the number of wires.
--
--   The numbers of factors in the product gates, their multiplicities and the orders of poles in coefficients are all unrestricted. This object is the circuit model of the whole mission; `map` extends coefficients along a ring homomorphism.
--
--   **Formalization Note** A bottom gate is its monomial, whose degree is its fan-in; degree $0$ is the constant $1$. A wire of multiplicity $e_{i,m}>0$ counts once, and input nodes are not counted, so `size` is at most the page's size, and a lower bound on it implies the same bound for any counting of multi-wires and inputs.
-- source:
--   A. Dey, P. Dutta, Z. Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Definition 2.11, p.33; size convention, p.32

import Mathlib
set_option autoImplicit false

open MvPolynomial
open scoped PowerSeries

namespace BorderD4

/-- A `Σ^[k]ΠΣΠ^[δ]` circuit over `R` in the variables `σ`.
Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Definition 2.11, p.33, and the size convention, p.32.

The layers, from the top: one addition gate; `t ≤ k` product gates; the addition gates `Mid`; the product
gates `Bot` of fan-in at most `δ`.
* `mono b` is the monomial computed by bottom gate `b`; its fan-in is its degree, and degree `0` is the
  constant `1`, so constants are available (p.4: "a sum of monomials of degree at most `δ`");
* `coef m b` is the scalar on the wire `b → m`, with `0` meaning no wire;
* `exp i m` is the multiplicity of the wire `m → i`, with `0` meaning no wire;
* `topc i` is the scalar on the wire from product gate `i` to the output.

**Formalization Note** `Bot` and `Mid` are finite types in `Type`, which loses nothing since each is
equivalent to a `Fin`. Fan-in and fan-out in the middle layers, the number of factors of a product gate
and its repetitions are unrestricted (p.49). -/
structure SPSP (R : Type*) (σ : Type*) [CommRing R] (k δ : ℕ) where
  /-- The bottom product gates. -/
  Bot : Type
  [fBot : Fintype Bot]
  /-- The addition gates of the third layer. -/
  Mid : Type
  [fMid : Fintype Mid]
  /-- The number of product gates in the second layer, which is the top fan-in. -/
  t : ℕ
  ht : t ≤ k
  /-- The monomial computed by a bottom gate. -/
  mono : Bot → σ →₀ ℕ
  hmono : ∀ b, (mono b).degree ≤ δ
  /-- The scalar on the wire from a bottom gate to an addition gate. -/
  coef : Mid → Bot → R
  /-- The scalar on the wire from a product gate to the output. -/
  topc : Fin t → R
  /-- The multiplicity of the wire from an addition gate to a product gate. -/
  exp : Fin t → Mid → ℕ

attribute [instance] SPSP.fBot SPSP.fMid

namespace SPSP

variable {R R' σ : Type*} [CommRing R] [CommRing R'] {k δ : ℕ}

/-- The polynomial `q_m = ∑_b coef m b · x^{mono b}` computed by an addition gate of the third layer. -/
noncomputable def bottomPoly (C : SPSP R σ k δ) (m : C.Mid) : MvPolynomial σ R :=
  ∑ b, MvPolynomial.C (C.coef m b) * monomial (C.mono b) 1

/-- The polynomial `T_i = topc i · ∏_m q_m ^ exp i m` of a product gate, with its output scalar. -/
noncomputable def gate (C : SPSP R σ k δ) (i : Fin C.t) : MvPolynomial σ R :=
  MvPolynomial.C (C.topc i) * ∏ m, C.bottomPoly m ^ C.exp i m

/-- The polynomial `∑_i T_i` computed by the circuit. -/
noncomputable def eval (C : SPSP R σ k δ) : MvPolynomial σ R := ∑ i, C.gate i

open Classical in
/-- The size of the circuit, the number of gates plus the number of wires (p.32).

**Formalization Note** Gates: the output, `t` product gates, `Mid`, `Bot`. Wires: a bottom gate contributes
its degree; an addition gate one wire per nonzero scalar; a product gate one wire per addition gate with
positive multiplicity, however large that multiplicity is; the output one wire per nonzero top scalar.
Input nodes are not counted. Each choice can only make `size` smaller than a count of all multi-wires and
inputs, so a lower bound on this `size` implies one on every such count. -/
noncomputable def size (C : SPSP R σ k δ) : ℕ :=
  1 + C.t + Fintype.card C.Mid + Fintype.card C.Bot + ∑ b, (C.mono b).degree
    + (Finset.univ.filter fun p : C.Mid × C.Bot => C.coef p.1 p.2 ≠ 0).card
    + (Finset.univ.filter fun p : Fin C.t × C.Mid => C.exp p.1 p.2 ≠ 0).card
    + (Finset.univ.filter fun i : Fin C.t => C.topc i ≠ 0).card

/-- Extending coefficients along a ring homomorphism: the same circuit with its scalars mapped. -/
def map (φ : R →+* R') (C : SPSP R σ k δ) : SPSP R' σ k δ where
  Bot := C.Bot
  Mid := C.Mid
  t := C.t
  ht := C.ht
  mono := C.mono
  hmono := C.hmono
  coef m b := φ (C.coef m b)
  topc i := φ (C.topc i)
  exp := C.exp

end SPSP

end BorderD4


