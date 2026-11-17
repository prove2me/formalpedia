-- Prove2me | Definitions.Def_GroupIsoPoly_Supplement_homAct
-- name    : GroupIsoPoly_Supplement_homAct
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:28:38.573148+00:00
-- url     : https://prove2.me/theorems/3304aa32-1ca1-4bb2-90ac-abd032a0945b
-- title:
--   The matrix modules $B=\bigoplus_j\mathrm{Hom}_{L_j}(X_j,Y_j)$ of Theorem C.9
-- statement:
--   Let $D$ be a product of classical groups. A **C.9 module** over a field $L$ is either the trivial line ($\rho(g)=1$ on $L^1$) or a realization over $L$, after restriction of scalars, of the natural module, the dual module, or a Frobenius twist of the natural module of one factor of $D$.
--
--   Given C.9 modules $X_j,Y_j$ over finite fields $L_j$ ($j<s$), with matrices $\rho_{X_j},\rho_{Y_j}$, the module
--
--   $$B=\bigoplus_{j<s}\mathrm{Hom}_{L_j}(X_j,Y_j)\cong\bigoplus_{j<s}\mathrm{Mat}(\dim Y_j\times\dim X_j,L_j),\qquad g\cdot(A_j)_j=\big(\rho_{Y_j}(g)\,A_j\,\rho_{X_j}(g)^{-1}\big)_j ,$$
--
--   is a direct sum of full spaces of linear maps, as in Definition 14.
--
--   Theorem C.9 asserts that $H^1(D,B)=0$ and $H^1(D,B/C)=0$ for every $\mathbb F_p$-subspace $C$ of the fixed points, in odd characteristic.
--
--   **Formalization Note** $\rho_{X_j}(g)^{-1}$ is written $\rho_{X_j}(g^{-1})$; they agree for the representations allowed here.
-- source:
--   Qiao, Zhang, Testing isomorphism of finite groups in time polynomial in the group order, preprint, Nov. 3, 2026 (held version sha256 eb9a3355…), Definition 14, p.46 (PDF p.50); Theorem C.9, p.146 (PDF p.150)

import Mathlib
import Definitions.Def_GroupIsoPoly_Supplement_factorMat

set_option autoImplicit false

namespace GroupIsoPoly

namespace Supplement

/-- **A natural, dual, Frobenius-twisted natural or trivial module of the product `D`, over a field
`L`, as in Theorem C.9.** `IsC9Module dat ρ` says that the matrices `ρ g ∈ Mat(a, L)` realize
either the trivial line (`a = 1`, every `ρ g = 1`), or, after restriction of scalars to `L`
(`IsRestrictionOf`), the natural module, the dual module, or a Frobenius twist of the natural module
of one factor of `D` (a twisted module is never dual).

Qiao, Zhang, *Testing isomorphism of finite groups in time polynomial in the group order*, preprint,
Nov. 3, 2026 (held version sha256 eb9a3355…), Theorem C.9, p.146 (PDF p.150): "full spaces of linear
maps between natural, dual, Frobenius-twisted natural, and trivial modules, viewed over Fp by
restriction of scalars"; Definition 14, p.46 (PDF p.50). -/
def IsC9Module {t : ℕ} {K : Fin t → Type} [∀ i, Field (K i)] {n : Fin t → ℕ}
    (dat : (i : Fin t) → ClassicalDatum (K i) (n i)) {L : Type} [Field L] {a : ℕ}
    (ρ : ClProd dat → Matrix (Fin a) (Fin a) L) : Prop :=
  (a = 1 ∧ ∀ g, ρ g = 1) ∨
    ∃ (i : Fin t) (κ : ModKind), (κ.dual = true → κ.twist = 0) ∧ IsRestrictionOf dat i κ ρ

/-- **The matrix module `B = ⊕_j Hom_{L_j}(X_j, Y_j)` (Definition 14, Theorem C.9).**

Qiao, Zhang, preprint, Nov. 3, 2026 (held version sha256 eb9a3355…), Definition 14, p.46
(PDF p.50): "B = ⊕_{j=1}^s Bj, Bj = Hom_Kj(Xj, Yj) ≅ Mat(aj × bj, Kj) … Writing ρXj, ρYj for their
actions, the action on Bj is g · A = ρYj(g) A ρXj(g)^{−1}."

An element of `B` is a family of matrices `A_j ∈ Mat(dim Y_j × dim X_j, L_j)` and
`homAct ρX ρY g A = (ρY_j(g) A_j ρX_j(g⁻¹))_j`.

**Formalization Note.** `ρX_j(g⁻¹)` is written for `ρX_j(g)⁻¹`; the two agree for the
representations of `IsC9Module`. -/
def homAct {G : Type} [Group G] {s : ℕ} {L : Fin s → Type} [∀ j, Field (L j)]
    {aX aY : Fin s → ℕ} (ρX : (j : Fin s) → G → Matrix (Fin (aX j)) (Fin (aX j)) (L j))
    (ρY : (j : Fin s) → G → Matrix (Fin (aY j)) (Fin (aY j)) (L j)) (g : G)
    (A : (j : Fin s) → Matrix (Fin (aY j)) (Fin (aX j)) (L j)) :
    (j : Fin s) → Matrix (Fin (aY j)) (Fin (aX j)) (L j) :=
  fun j => ρY j g * A j * ρX j g⁻¹

end Supplement

end GroupIsoPoly


