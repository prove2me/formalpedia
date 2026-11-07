-- Prove2me | Definitions.Def_ContractionLemma_Splitting_modeSet
-- name    : ContractionLemma_Splitting_modeSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:01:09.188183+00:00
-- url     : https://prove2.me/theorems/2aa63808-d65c-4c4a-a857-aa51d73780fd
-- title:
--   Tiles, modes $\xi_{P,y_0,b}$, weights, coefficients $c_{x,\xi}$, and $\omega_x$
-- statement:
--   Fix a level $i$, a precision $p'$, and $T=t+\alpha z$ for a node $z$. A slot is written $y=y_0+2^{i+1}j$ with $0\le y_0<2^{i+1}$, and a **tile** is the set of slots with a given $y_0$. The **mode** $\xi_{P,y_0,b}$, for a packet $P$, a tile $y_0$ and $b+1<p'$, is the moment
--
--   $$
--   \xi_{P,y_0,b}(X)=\sum_j j^b X_{y_0+2^{i+1}j},
--   $$
--
--   summed over the nonempty slots of the tile, with $0^0=1$; its **weight** is $b+1$. A row bit at slot $x$ whose level-$i$ group differs from that of the tile's columns crosses into the tile, with coefficients
--
--   $$
--   c_{x,y_0,b}=\frac{C(T)}{C'(0)\,A}\Big(\frac{2^{i+1}}{A}\Big)^{b},\qquad A=T-(y_0-x).
--   $$
--
--   $\omega_x$ is the part of $(W(T)X)_x$ coming from the column bits of $x$'s own group in $x$'s packet. The wiring factor of $x$ is $\chi_{Y_x}(\omega_x+\sum_\xi c_{x,\xi}\xi)$, a polynomial in the modes as formal variables. The **surviving** exponent vectors are those $\beta$ with $\sum_\xi w_\xi\beta_\xi<p'$.
--
--   **Formalization Note** Only tiles that some row bit crosses into are kept, so every kept mode is received by exactly one group. Any other tile of the paper's list has coefficient $0$ for every row bit, so an exponent vector using it gives a zero term in the paper. The count of modes only decreases. $1/A$ is `Ring.inverse`; $A$ is a unit at the points of the lemmas.
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), proof of Lemma A.12.1, pp.88–89

import Mathlib
import Definitions.Def_ContractionLemma_BipNet
import Definitions.Def_ContractionLemma_BipNet_Phi
import Definitions.Def_ContractionLemma_kernel
import Definitions.Def_ContractionLemma_Placement
import Definitions.Def_ContractionLemma_Packing
import Definitions.Def_ContractionLemma_NodeField

set_option autoImplicit false

namespace ContractionLemma

open Polynomial

namespace Packing

variable {U W E : Type*} {a : ℕ}

/-- The `k`-th symbol of a row vertex, for a coordinate `k : ℕ` (the level of an easy point);
only coordinates `k < a` occur, and the value `0` for `k ≥ a` is never used. -/
def rowSym (pk : Packing U W E a) (u : U) (k : ℕ) : Fin 64 :=
  if h : k < a then pk.rowLabel u ⟨k, h⟩ else 0

/-- The `k`-th symbol of a column vertex (see `rowSym`). -/
def colSym (pk : Packing U W E a) (w : W) (k : ℕ) : Fin 64 :=
  if h : k < a then pk.colLabel w ⟨k, h⟩ else 0

end Packing

namespace Splitting

variable {U W E : Type*} {f : ℤ[X]} {a : ℕ}

/-- The evaluation point `T = t + α z` with `α = 2^{a+1}` and a node `z` (App. A.5.2, p.63). -/
noncomputable def evalPt (a : ℕ) (t : ℤ) (z : NodeField f) : NodeField f :=
  (t : NodeField f) + 2 ^ (a + 1) * z

/-- The entry `W_{e,e′}(T)` of the shift curve at `T = t + αz`, in `ℚ[U]/(f)`. -/
noncomputable def wEntry (pk : Packing U W E a) (t : ℤ) (z : NodeField f) (e e' : E) :
    NodeField f :=
  if pk.packet e = pk.packet e' then
    Polynomial.aeval (evalPt a t z) (kernel a ((pk.slot e' : ℤ) - (pk.slot e : ℤ)))
  else 0

/-- The tile `y₀ = y mod 2^{i+1}` of the slot `y` of an edge, at level `i` (p.89). -/
def tileOf (pk : Packing U W E a) (i : ℕ) (e : E) : ℕ := (pk.slot e : ℕ) % 2 ^ (i + 1)

/-- The index `j` with `y = y₀ + 2^{i+1} j` (p.89). -/
def jOf (pk : Packing U W E a) (i : ℕ) (e : E) : ℕ := (pk.slot e : ℕ) / 2 ^ (i + 1)

/-- The edge `e` sits in tile `y₀` of packet `P` (its column bit is a column of that tile). -/
def InTile (pk : Packing U W E a) (i : ℕ) (P : Fin pk.np) (y₀ : ℕ) (e : E) : Prop :=
  pk.packet e = P ∧ tileOf pk i e = y₀

/-- The row bit `e` crosses into tile `y₀` of packet `P` (p.89): `e` is in `P`, and the tile has
a column whose level-`i` group differs from that of the row vertex of `e`. -/
def Hears {R : Type*} (G : BipNet U W E R) (pk : Packing U W E a) (i : ℕ) (e : E)
    (P : Fin pk.np) (y₀ : ℕ) : Prop :=
  pk.packet e = P ∧ ∃ e', InTile pk i P y₀ e' ∧ pk.colSym (G.colOf e') i ≠ pk.rowSym (G.rowOf e) i

/-- **The modes at level `i` and precision `p′`** — Gajulapalli, *The Contraction Lemma Beyond
ETH* (manuscript, sha256 049caea1…), proof of Lemma A.12.1, p.89 (PDF p.92): one mode
`ξ_{P,y₀,b}` for each packet `P`, tile `y₀ < 2^{i+1}` and `b` with `b + 1 < p′`, of weight
`b + 1`.

**Formalization Note.** Only tiles that some row bit crosses into are kept (such a tile has a
column). The moment of any other tile is either identically `0` or heard by no row bit; with
such modes included, the β-term of an exponent vector using one of them would not split as
Lemma A.12.2 says. The count of Lemma A.12(a) is unaffected. -/
noncomputable def modeSet [Fintype E] {R : Type*} (G : BipNet U W E R) (pk : Packing U W E a)
    (i p' : ℕ) : Finset (Fin pk.np × Fin (2 ^ (i + 1)) × Fin p') := by
  classical
  exact Finset.univ.filter fun ξ => ξ.2.2.1 + 1 < p' ∧ ∃ e, Hears G pk i e ξ.1 ξ.2.1

/-- The type of modes. -/
abbrev Mode [Fintype E] {R : Type*} (G : BipNet U W E R) (pk : Packing U W E a) (i p' : ℕ) :=
  {ξ // ξ ∈ modeSet G pk i p'}

/-- The weight `w_ξ = b + 1` of the mode `ξ_{P,y₀,b}`. -/
def weight [Fintype E] {R : Type*} {G : BipNet U W E R} {pk : Packing U W E a} {i p' : ℕ}
    (ξ : Mode G pk i p') : ℕ :=
  ξ.1.2.2.1 + 1

/-- The value of the mode `ξ_{P,y₀,b}(X) = ∑_j j^b X_{y₀ + 2^{i+1} j}`, summed over the nonempty
slots of the tile, with `0⁰ = 1` (p.89). -/
noncomputable def modeVal [Fintype E] {R : Type*} (G : BipNet U W E R) (pk : Packing U W E a)
    (i p' : ℕ) (ξ : Mode G pk i p') (X : E → Bool) : NodeField f := by
  classical
  exact ∑ e', if InTile pk i ξ.1.1 ξ.1.2.1 e' ∧ X e' then
    ((jOf pk i e' : ℕ) : NodeField f) ^ (ξ.1.2.2 : ℕ) else 0

/-- The coefficient `c_{x,ξ}` of the mode `ξ = ξ_{P,y₀,b}` heard by the row bit `x = e`
(p.89): `c_{x,y₀,b} = (C(T)/(C′(0) A)) (2^{i+1}/A)^b` with `A = T − (y₀ − x)`, and `0` when `e`
does not cross into the tile of `ξ`.

**Formalization Note.** `1/A` is `Ring.inverse A`; at the points of the lemmas `A` is a unit
(`v₂(A) ≤ i`, p.89). -/
noncomputable def coef [Fintype E] (G : BipNet U W E (NodeField f)) (pk : Packing U W E a)
    (t : ℤ) (i : ℕ) (z : NodeField f) (p' : ℕ) (e : E) (ξ : Mode G pk i p') : NodeField f := by
  classical
  exact if Hears G pk i e ξ.1.1 ξ.1.2.1 then
    Polynomial.aeval (evalPt a t z) (Cpoly a) *
      Ring.inverse (algebraMap ℚ (NodeField f) (Cder0 a) *
        (evalPt a t z - (((ξ.1.2.1 : ℕ) : ℤ) - (pk.slot e : ℤ) : ℤ))) *
      ((2 : NodeField f) ^ (i + 1) *
        Ring.inverse (evalPt a t z - (((ξ.1.2.1 : ℕ) : ℤ) - (pk.slot e : ℤ) : ℤ))) ^
        (ξ.1.2.2 : ℕ)
  else 0

/-- `ω_x` (Lemma A.12.1(b), p.67): the part of `(W(T)X)_x` coming from the column bits of `x`'s
own level-`i` group in `x`'s packet. -/
noncomputable def omega [Fintype E] (G : BipNet U W E (NodeField f)) (pk : Packing U W E a)
    (t : ℤ) (i : ℕ) (z : NodeField f) (e : E) (X : E → Bool) : NodeField f := by
  classical
  exact ∑ e', if pk.packet e' = pk.packet e ∧ pk.colSym (G.colOf e') i = pk.rowSym (G.rowOf e) i ∧
    X e' then wEntry pk t z e e' else 0

/-- The wiring factor `χ_{Y_x}(ω_x + ∑_ξ c_{x,ξ} ξ)` of the row bit `x = e`, a polynomial in the
modes treated as formal variables (proof of Lemma A.12.2, p.90). -/
noncomputable def wireFactor [Fintype E] (G : BipNet U W E (NodeField f)) (pk : Packing U W E a)
    (t : ℤ) (i : ℕ) (z : NodeField f) (p' : ℕ) (e : E) (Y X : E → Bool) :
    MvPolynomial (Mode G pk i p') (NodeField f) :=
  chi (Y e) (MvPolynomial.C (omega G pk t i z e X) +
    ∑ ξ, MvPolynomial.C (coef G pk t i z p' e ξ) * MvPolynomial.X ξ)

/-- The surviving exponent vectors: `β` with total weight `∑_ξ w_ξ β_ξ < p′`. -/
noncomputable def survivors [Fintype E] {R : Type*} (G : BipNet U W E R) (pk : Packing U W E a)
    (i p' : ℕ) : Finset (Mode G pk i p' → ℕ) := by
  classical
  exact (Fintype.piFinset fun _ => Finset.range p').filter fun β => ∑ ξ, weight ξ * β ξ < p'

end Splitting

end ContractionLemma


