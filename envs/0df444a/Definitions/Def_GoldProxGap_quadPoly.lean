-- Prove2me | Definitions.Def_GoldProxGap_quadPoly
-- name    : GoldProxGap_quadPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:23:53.757695+00:00
-- url     : https://prove2.me/theorems/c8b4e96a-0965-41cc-a20f-198632459c7c
-- title:
--   Quadratic Boolean functions $\psi$, their polynomials $Q$, the polynomial $J$, the constant $\varepsilon_A$, polar forms and polar radicals
-- statement:
--   Fix a coordinate basis $\varphi_1,\dots,\varphi_d$ of the linear functions on a binary additive domain $D\subseteq\mathbb B$, with coordinates $x_i=\varphi_i(x)$, polynomials $\ell_i=\ell_{\varphi_i}$ and labels $\omega_i$. For an alternating binary matrix $A$ and a linear function $\varphi$ with label $\omega$, put
--   $$
--   \psi(x)=\sum_{i<j}A_{ij}x_ix_j+\varphi(x),\qquad
--   Q=\sum_{i<j}A_{ij}\bigl(\ell_i\ell_j+\omega_i\omega_j\Lambda\bigr)+\ell_\varphi,
--   $$
--   $$
--   J=\sum_{i<j}A_{ij}\bigl(\omega_i^2\ell_j+\omega_j^2\ell_i\bigr),\qquad \varepsilon_A=\sum_{i<j}A_{ij}\omega_i\omega_j .
--   $$
--   For a Boolean function $\psi$ on a finite additive group $U$, the **polar form** is $B_\psi(x,y)=\psi(x+y)+\psi(x)+\psi(y)+\psi(0)$ and the **polar radical** is $\{u\in U: B_\psi(x,u)=0\ \text{for all }x\}$.
--
--   Every quadratic Boolean function on $D$ vanishing at $0$ has this form, and $Q$ is the polynomial that represents it on $D$; the polar radical of $\psi$ is where the level sets of $\psi$ become unions of cosets.
--
--   **Formalization Note** $\psi_A$ (the case $\omega=0$) is `psi φs A 0`. Indices are $0$-based; entries $A_{ij}$ enter $\mathbb B$ as $0$ or $1$.
-- source:
--   Dao, Kominers, Thaler, Zheng, Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields, STOC 2027 submission manuscript (2 November 2026, sha256 6c2d9cedf047e9f98d174f41e6742e827f7c6f0e1dd00939b3975e7fe66f4e4d), Definition 3.15, p.24; display (5.2) and the definitions of $J$, $\varepsilon_A$, p.38

import Mathlib
import Definitions.Def_GoldProxGap_label
import Definitions.Def_GoldProxGap_goldMoment

open Polynomial

open scoped Classical

namespace GoldProxGap

/-!
# Quadratic Boolean functions, their polynomials, and polar radicals

Dao, Kominers, Thaler, Zheng, *Counterexamples to Beyond-Johnson Proximity Gaps over Binary
Fields*, STOC 2027 submission manuscript (2 November 2026, sha256 6c2d9ced…), Definition 3.15
(p.24) and "Quadratic functions", display (5.2), p.38:

"For an alternating binary d × d matrix A and a label ω ∈ D̂, define a function ψ : D → F₂ and a
polynomial Q ∈ B[X] by ψ(x) = Σ_{i<j} A_ij x_i x_j + ℓ_ω(x),
Q = Σ_{i<j} A_ij (ℓ_i ℓ_j + ω_i ω_j Λ) + ℓ_ω. … J = Σ_{i<j} A_ij (ω_i² ℓ_j + ω_j² ℓ_i),
ε_A = Σ_{i<j} A_ij ω_i ω_j."

**Formalization Note.**
* The basis `ω₁, …, ω_d` of the label space is given by a coordinate basis `φs` of linear
  functions (see `GoldProxGap.label`), with `x_i = φs i x`, `ℓ_i = ellPoly D (φs i)` and
  `ω_i = label D (φs i)`. The label `ω` of `ψ` is given by its linear function `φ`, with
  `ℓ_ω = ellPoly D φ`. Indices are `0`-based.
* `psi φs A φ` is `ψ`; `psi φs A 0` is `ψ_A`. `Qpoly`, `Jpoly`, `epsA` are `Q`, `J`, `ε_A`.
  Entries `A i j ∈ F₂` enter `B` as `0` or `1`.
* `polarForm ψ x y = ψ(x+y) + ψ(x) + ψ(y) + ψ(0)` and
  `polarRadical ψ = {u : ∀ x, B_ψ(x, u) = 0}` (Definition 3.15), for any finite additive group.
-/

variable {B : Type*} [Field B] [Fintype B] [CharP B 2] {d : ℕ}

/-- (5.2): the quadratic Boolean function `ψ(x) = Σ_{i<j} A_ij x_i x_j + φ(x)`. -/
def psi {D : AddSubgroup B} (φs : Fin d → (D →+ ZMod 2)) (A : Matrix (Fin d) (Fin d) (ZMod 2))
    (φ : D →+ ZMod 2) (x : D) : ZMod 2 :=
  (∑ i : Fin d, ∑ j ∈ Finset.Ioi i, A i j * φs i x * φs j x) + φ x

/-- (5.2): `Q = Σ_{i<j} A_ij (ℓ_i ℓ_j + ω_i ω_j Λ) + ℓ_ω`. -/
noncomputable def Qpoly (D : AddSubgroup B) (φs : Fin d → (D →+ ZMod 2))
    (A : Matrix (Fin d) (Fin d) (ZMod 2)) (φ : D →+ ZMod 2) : B[X] :=
  (∑ i : Fin d, ∑ j ∈ Finset.Ioi i, C ((A i j).val : B) *
      (ellPoly D (φs i) * ellPoly D (φs j) + C (label D (φs i) * label D (φs j)) * normLocator D))
    + ellPoly D φ

/-- `J = Σ_{i<j} A_ij (ω_i² ℓ_j + ω_j² ℓ_i)` (p.38). -/
noncomputable def Jpoly (D : AddSubgroup B) (φs : Fin d → (D →+ ZMod 2))
    (A : Matrix (Fin d) (Fin d) (ZMod 2)) : B[X] :=
  ∑ i : Fin d, ∑ j ∈ Finset.Ioi i, C ((A i j).val : B) *
    (C (label D (φs i) ^ 2) * ellPoly D (φs j) + C (label D (φs j) ^ 2) * ellPoly D (φs i))

/-- `ε_A = Σ_{i<j} A_ij ω_i ω_j` (p.38). -/
noncomputable def epsA (D : AddSubgroup B) (φs : Fin d → (D →+ ZMod 2))
    (A : Matrix (Fin d) (Fin d) (ZMod 2)) : B :=
  ∑ i : Fin d, ∑ j ∈ Finset.Ioi i, ((A i j).val : B) * (label D (φs i) * label D (φs j))

/-- Definition 3.15: the polar form `B_ψ(x, y) = ψ(x + y) + ψ(x) + ψ(y) + ψ(0)`. -/
def polarForm {U : Type*} [AddCommGroup U] (ψ : U → ZMod 2) (x y : U) : ZMod 2 :=
  ψ (x + y) + ψ x + ψ y + ψ 0

/-- Definition 3.15: the polar radical `rad(B_ψ) = {u ∈ U : B_ψ(x, u) = 0 for all x ∈ U}`. -/
noncomputable def polarRadical {U : Type*} [AddCommGroup U] [Fintype U] (ψ : U → ZMod 2) :
    Finset U :=
  Finset.univ.filter (fun u => ∀ x, polarForm ψ x u = 0)

end GoldProxGap


