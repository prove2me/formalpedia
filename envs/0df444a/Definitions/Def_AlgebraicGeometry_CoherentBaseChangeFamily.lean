-- Prove2me | Definitions.Def_AlgebraicGeometry_CoherentBaseChangeFamily
-- name    : AlgebraicGeometry_CoherentBaseChangeFamily
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/af95ee57-052d-5241-b85f-e9b2e47efe2f
-- title:
--   Families of fibre H0 ranks over a scheme
-- statement:
--   Fix a scheme $T$. The structure [`CoherentBaseChange.FibreH0Family T`](../def/AlgebraicGeometry_CoherentBaseChangeFamily.html#L14) packages the following data. First, for every open $U \subseteq T$ together with a proof that $U$ is affine, a two-term complex `G U hU` of modules over the ring of sections $\Gamma(T, U)$: by the definition of `TwoTermComplex`, this consists of two finite free $\Gamma(T,U)$-modules $C_0$, $C_1$ and a $\Gamma(T,U)$-linear map $d \colon C_0 \to C_1$. Second, a function $h^0 \colon T \to \mathbb{N}$ on the points of the underlying space. Third, a compatibility field: for every affine open $U$, every proof `hU` of its affineness and every point $t \in U$, the value $h^0(t)$ equals `(G U hU).fibreH0` evaluated at the prime of $\Gamma(T,U)$ corresponding to $t$ (Mathlib's `IsAffineOpen.primeIdealOf`). Here `fibreH0` of a two-term complex at a prime $\mathfrak{p}$ is, by definition, the dimension over the residue field $\kappa(\mathfrak{p})$ of the kernel of the base-changed map $d \otimes \kappa(\mathfrak{p})$.
--
--   So the structure is indexed by presentations — an affine open together with a chosen affineness proof — and the third field is a theorem carried as data: it asserts that the fibrewise kernel dimension computed from any one of these complexes agrees with the single global function $h^0$, hence in particular is independent of the affine open and of the complex chosen over it. The ambient module also provides, for a two-term complex, the fibre dimension `fibreH1` of the cokernel of $d \otimes \kappa(\mathfrak{p})$, the integer $\chi = \operatorname{rank} C_0 - \operatorname{rank} C_1$, the kernel `H0 A` of $d \otimes A$ for an $R$-algebra $A$, and the natural $A$-linear comparison map $A \otimes_R \ker d \to \ker(d \otimes A)$.
--
--   **Relation to Mathlib.** Mathlib has no notion of a two-term complex of finite free modules with its fibrewise kernel and cokernel dimensions, nor of such a family over a scheme; both are the project's own definitions, built on Mathlib's `LinearMap.baseChange`, `Ideal.ResidueField` and `IsAffineOpen.primeIdealOf`.
--
--   **Where it is used.** This structure isolates the data on which semicontinuity statements for fibre dimensions are formulated: a presentation of the sheaf-theoretic $H^0$ by finite free two-term complexes over affine charts, together with the resulting numerical function on points of the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_CoherentBaseChangeFamily.lean

import Definitions.Def_AlgebraicGeometry_CoherentBaseChange
import Mathlib.AlgebraicGeometry.AffineScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace CoherentBaseChange

structure FibreH0Family (T : Scheme.{u}) where

  G : ∀ (U : T.Opens), IsAffineOpen U → TwoTermComplex.{u, u} Γ(T, U)

  h0 : T → ℕ

  hglue : ∀ (U : T.Opens) (hU : IsAffineOpen U) (t : U),
    h0 t = (G U hU).fibreH0 (hU.primeIdealOf t)

end CoherentBaseChange


