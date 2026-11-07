-- Prove2me | Definitions.Def_ContractionLemma_BipNet_Phi
-- name    : ContractionLemma_BipNet_Phi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:58:49.565943+00:00
-- url     : https://prove2.me/theorems/3b81150e-08e4-476a-9e4b-902a4fb561ee
-- title:
--   $\Phi(W)$, eq. (5): the contraction as a polynomial in a wiring
-- statement:
--   Let $G$ be a bipartite network with edge set $E$. Give each edge a row bit $Y_e$ and a column bit $X_e$, let $A(Y)$ be the product of the row tables and $B(X)$ the product of the column tables, and put $\chi_1(\nu)=\nu$, $\chi_0(\nu)=1-\nu$. For an $E\times E$ matrix $W$, a **wiring**,
--
--   $$
--   \Phi(W)=\sum_{Y,X\in\{0,1\}^E}A(Y)\,B(X)\prod_{e\in E}\chi_{Y_e}\big((WX)_e\big),\qquad (WX)_e=\sum_f W_{e,f}X_f .
--   $$
--
--   The module also defines block diagonal wirings for a partition of the vertices into groups, and the factors $\Phi_g(W_g)$ of a group.
--
--   **Formalization Note** $\Phi$ is an element of `MvPolynomial (E × E) R`, and `PhiAt` evaluates it at a wiring with entries in any commutative $R$-algebra. Group names form an arbitrary type.
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), Definition A.4, eq. (5), p.54; Lemma A.5(b), p.54

import Mathlib
import Definitions.Def_ContractionLemma_BipNet

set_option autoImplicit false

namespace ContractionLemma

/-- The wiring factor `χ`: `χ₁(ν) = ν` and `χ₀(ν) = 1 − ν` (p.54), so `χ_Y(X) = [Y = X]` on
bits. -/
def chi {S : Type*} [CommRing S] (b : Bool) (ν : S) : S := if b then ν else 1 - ν

namespace BipNet

variable {U W E R : Type*}

/-- `A(Y)`: the product of the row tables at the row bits `Y` (p.52). -/
def rowProd [Fintype U] [CommRing R] (G : BipNet U W E R) (Y : E → Bool) : R :=
  ∏ u, G.rowTable u (fun e => Y e.1)

/-- `B(X)`: the product of the column tables at the column bits `X` (p.52). -/
def colProd [Fintype W] [CommRing R] (G : BipNet U W E R) (X : E → Bool) : R :=
  ∏ w, G.colTable w (fun e => X e.1)

/-- **`Φ` (Definition A.4, eq. (5))** — Gajulapalli, *The Contraction Lemma Beyond ETH*
(manuscript, sha256 049caea1…), p.54 (PDF p.57):
`Φ(W) = ∑_{Y,X ∈ {0,1}^E} A(Y) B(X) ∏_{e ∈ E} χ_{Y_e}((WX)_e)`, `(WX)_e = ∑_f W_{e,f} X_f`,
as a polynomial in the `M²` entries `W_{e,f}` of the wiring (the variable `X (e, f)`).

**Formalization Note.** Rows and columns of a wiring are both indexed by the edges `E` (row
bit `e`, column bit `f`). -/
noncomputable def Phi [Fintype U] [Fintype W] [Fintype E] [DecidableEq E] [CommRing R]
    (G : BipNet U W E R) : MvPolynomial (E × E) R :=
  ∑ Y : E → Bool, ∑ X : E → Bool, MvPolynomial.C (G.rowProd Y * G.colProd X) *
    ∏ e, chi (Y e) (∑ f, if X f then MvPolynomial.X (e, f) else 0)

/-- `Φ(W)` for a wiring `W` with entries in a commutative `R`-algebra `S`. -/
noncomputable def PhiAt [Fintype U] [Fintype W] [Fintype E] [DecidableEq E] [CommRing R]
    {S : Type*} [CommRing S] [Algebra R S] (G : BipNet U W E R) (Wm : Matrix E E S) : S :=
  MvPolynomial.aeval (fun p : E × E => Wm p.1 p.2) G.Phi

/-- A wiring is **block diagonal** for a partition of the vertices into groups (row vertex `u`
in group `rowGrp u`, column vertex `w` in group `colGrp w`) when `W_{e,f} = 0` whenever row
bit `e` and column bit `f` lie in different groups (p.54); a row bit belongs to the group of
its row vertex and a column bit to the group of its column vertex. -/
def IsBlockDiag {Γ S : Type*} [Zero S] (G : BipNet U W E R) (rowGrp : U → Γ) (colGrp : W → Γ)
    (Wm : Matrix E E S) : Prop :=
  ∀ e f, rowGrp (G.rowOf e) ≠ colGrp (G.colOf f) → Wm e f = 0

/-- `Φ_g(W_g)` (Lemma A.5(b), p.54): the sum over the row bits `Y_g` and column bits `X_g` of
group `g` of `A_g(Y_g) B_g(X_g) ∏_{e ∈ g} χ_{Y_e}((W_g X_g)_e)`, where `A_g`, `B_g` are the
products of the row and column tables of group `g` and `W_g` is the block of `W` on the row and
column bits of `g`. -/
noncomputable def PhiGroup [Fintype U] [Fintype W] [Fintype E] [DecidableEq E] [CommRing R]
    {Γ S : Type*} [DecidableEq Γ] [CommRing S] [Algebra R S] (G : BipNet U W E R)
    (rowGrp : U → Γ) (colGrp : W → Γ) (g : Γ) (Wm : Matrix E E S) : S :=
  ∑ Y : {e : E // rowGrp (G.rowOf e) = g} → Bool, ∑ X : {f : E // colGrp (G.colOf f) = g} → Bool,
    algebraMap R S
      ((∏ u : {u : U // rowGrp u = g},
          G.rowTable u.1 (fun e => Y ⟨e.1, (congrArg rowGrp e.2).trans u.2⟩)) *
        ∏ w : {w : W // colGrp w = g},
          G.colTable w.1 (fun f => X ⟨f.1, (congrArg colGrp f.2).trans w.2⟩)) *
    ∏ e : {e : E // rowGrp (G.rowOf e) = g},
      chi (Y e) (∑ f : {f : E // colGrp (G.colOf f) = g}, if X f then Wm e.1 f.1 else 0)

end BipNet

end ContractionLemma


