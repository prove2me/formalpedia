-- Prove2me | Definitions.Def_ModularCurve_FppfKummerInterface
-- name    : ModularCurve_FppfKummerInterface
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/6b8469f8-66b9-59ac-a7c5-e4b60f9dad8d
-- title:
--   Abstract fppf Kummer data for modular Jacobians
-- statement:
--   Two bundles of data, in a fixed universe, axiomatising the cohomological input of a Kummer-theory argument over $S=\operatorname{Spec}\mathbb{Z}$ in purely group-theoretic terms: no site, scheme or cohomology theory occurs, only types, additive commutative group structures on them, homomorphisms, and propositions carried as fields, so that producing a term of either structure amounts to proving the asserted facts for the chosen model.
--
--   [`ModularCurve.FppfKummerData p`](../def/ModularCurve_FppfKummerInterface.html#L12), for a natural number $p$, consists of three types `H0Gm`, `H1mu`, `H1Z`, each equipped with an additive commutative group structure (the structures being instance-valued fields), a homomorphism `kummerDelta : H0Gm →+ H1mu`, and three propositions: `kummerDelta` is surjective; `H1Z` is a subsingleton, i.e. the trivial group; and `H1mu` is a subsingleton whenever $p$ is odd. The intended reading is $H^0(S,\mathbb{G}_m)$, $H^1(S,\mu_p)$, $H^1(S,\mathbb{Z}/p)$ with the Kummer boundary map; note that the vanishing of `H1Z` is unconditional while that of `H1mu` is asserted only under `Odd p`.
--
--   [`ModularCurve.JKummerRow p m M`](../def/ModularCurve_FppfKummerInterface.html#L31), for natural numbers $p,m$ and an additive commutative group $M$, consists of three types `M0`, `H1Jtors`, `H1J` with additive commutative group structures, a homomorphism `toM : M0 →+ M` which is injective and whose range is an additive subgroup of finite index, and homomorphisms `delta : M0 →+ H1Jtors`, `push : H1Jtors →+ H1J` subject to three conditions: the kernel of `delta` equals the range of multiplication by $p^m$ on `M0`, i.e. $p^m\,$`M0`; the pair `delta`, `push` is exact in the sense of `Function.Exact` (range of `delta` equals kernel of `push`); and the range of `push` equals the kernel of multiplication by $p^m$ on `H1J`, i.e. the $p^m$-torsion of `H1J`. Thus `delta` induces an injection of `M0`$/p^m$`M0` into `H1Jtors` and `push` maps `H1Jtors` onto `H1J`$[p^m]$.
--
--   **Relation to Mathlib.** Mathlib has no fppf cohomology; both structures are the project's own abstraction of the values such a theory would supply, expressed with Mathlib's `AddMonoidHom`, `AddSubgroup.FiniteIndex` and `Function.Exact`.
--
--   **Where it is used.** The data axiomatise the exact sequences used in Mazur's proof that the relevant Mordell–Weil and Shafarevich–Tate groups attached to a modular Jacobian are finite: the elementary coefficient computations over $\operatorname{Spec}\mathbb{Z}$ in the first structure, and the $p^m$-level Kummer sequence for the connected Néron model of the Jacobian, together with the finiteness of the index of its group of integral points, in the second.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_FppfKummerInterface.lean

import Mathlib.Algebra.Exact
import Mathlib.GroupTheory.Index

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve

universe u

structure FppfKummerData (p : ℕ) where

  H0Gm : Type u

  H1mu : Type u

  H1Z : Type u
  [instH0Gm : AddCommGroup H0Gm]
  [instH1mu : AddCommGroup H1mu]
  [instH1Z : AddCommGroup H1Z]

  kummerDelta : H0Gm →+ H1mu

  kummerDelta_surjective : Function.Surjective kummerDelta

  h1Z_subsingleton : Subsingleton H1Z

  h1mu_subsingleton : Odd p → Subsingleton H1mu

structure JKummerRow (p m : ℕ) (M : Type u) [AddCommGroup M] where

  M0 : Type u

  H1Jtors : Type u

  H1J : Type u
  [instM0 : AddCommGroup M0]
  [instH1Jtors : AddCommGroup H1Jtors]
  [instH1J : AddCommGroup H1J]

  toM : M0 →+ M

  toM_injective : Function.Injective toM

  toM_finiteIndex : toM.range.FiniteIndex

  delta : M0 →+ H1Jtors

  push : H1Jtors →+ H1J

  delta_ker :
    delta.ker = (((p ^ m : ℤ) • (AddMonoidHom.id M0 : M0 →+ M0)).range : AddSubgroup M0)

  exact_delta_push : Function.Exact delta push

  push_range : push.range = (AddMonoidHom.ker ((p ^ m : ℤ) • AddMonoidHom.id H1J) : AddSubgroup H1J)

end ModularCurve


