-- Prove2me | Definitions.Def_AlgebraicGeometry_ModulesRigidifyV2
-- name    : AlgebraicGeometry_ModulesRigidifyV2
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/1e575d1f-6253-533f-9dce-652aa6b886c3
-- title:
--   Rigidification of modules along a section of a scheme
-- statement:
--   Fix schemes $T$ and $P$. For a morphism $\sigma : T \to P$, a morphism $q : P \to T$ and a sheaf of modules $L$ on $P$ (an object of `P.Modules`), the rigidification is defined by
--   $$\operatorname{rigidify} \sigma\, q\, L \;=\; L \otimes q^{*}\bigl((\sigma^{*}L)^{\vee}\bigr),$$
--   where $\sigma^{*}$ and $q^{*}$ are the pullback functors `Scheme.Modules.pullback` on sheaves of modules, $\otimes$ is the monoidal product on `P.Modules`, and the dual is `Scheme.Modules.dual M = (ihom M).obj (𝟙_ X.Modules)`, the internal hom into the unit object for the monoidal closed structure on modules over a scheme. The defining equation is also recorded as a rewriting lemma. Functoriality on isomorphisms is provided: `dualMapIso` sends an isomorphism $e : L \cong L'$ of modules on $X$ to an isomorphism $L^{\vee} \cong L'^{\vee}$, obtained by applying the internal-hom functor to $e^{-1}$ in the contravariant variable and evaluating at the unit; and `rigidifyMapIso` combines $e$ with the image of $\sigma^{*}e$ under dualisation and $q^{*}$ to give $\operatorname{rigidify} \sigma\, q\, L \cong \operatorname{rigidify} \sigma\, q\, L'$. No naturality or coherence statements beyond these isomorphisms are asserted.
--
--   The ambient structure on which these constructions rest is the symmetric monoidal closed structure on `X.Modules` and on `X.PresheafOfModules`. For presheaves of modules over a presheaf of commutative rings $R$, the internal hom at $X$ is the $R(X)$-module of families $\varphi_f : F(Y) \to N(Y)$ of $R(Y)$-linear maps indexed by $f : X \to Y$, compatible with restriction; the resulting adjunction $F \otimes - \dashv \operatorname{ihom}(F,-)$ makes presheaves of modules monoidal closed. Sheafification is a monoidal localisation at the class of maps that become weak equivalences of presheaves of abelian groups, which transports the symmetric monoidal structure, its closedness, and the monoidality of the sheafification functor to sheaves of modules, hence to `X.Modules`.
--
--   **Relation to Mathlib.** Mathlib supplies `PresheafOfModules`, `SheafOfModules`, the sheafification adjunction and the pullback functors on modules over a scheme. The internal hom of presheaves of modules by natural families of linear maps, the resulting monoidal closed structure, its descent along sheafification to `SheafOfModules` and `X.Modules`, and the rigidification construction itself are the project's own.
--
--   **Where it is used.** The construction $L \otimes q^{*}((\sigma^{*}L)^{\vee})$ normalises a sheaf of modules on a scheme $P$ over $T$ so that its pullback along the section $\sigma$ becomes canonically trivial; this is the standard rigidification used when discussing line bundles on elliptic curves over a base, relative to the zero section, and hence in the moduli-theoretic input (modular curves and the sheaves on them whose sections are modular forms) to the modularity argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ModulesRigidifyV2.lean

import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesRigidify

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {T P : Scheme.{u}}

end AlgebraicGeometry.Scheme.Modules

end


