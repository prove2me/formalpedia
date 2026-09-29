-- Prove2me | Definitions.Def_RibetLevelLowering_ExchangeData
-- name    : RibetLevelLowering_ExchangeData
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/b708c759-cff1-5bce-968a-d2e8e3a73d23
-- title:
--   Exchange data for Ribet's level-lowering dimension count
-- statement:
--   The module defines, over a field $k$, a structure `ExchangeData k` packaging the numerical data of the exchange case of Ribet's level-lowering argument as a bundle of abstract finite-dimensional $k$-vector spaces. A term of `ExchangeData k` carries five types `Xp`, `Yq`, `Lp`, `Yp`, `Lq`, each equipped with an additive commutative group structure, a $k$-module structure and the assumption of being a finite $k$-module (these instance fields are registered as instances), together with two $k$-linear maps $f : \mathrm{Yq} \to \mathrm{Lp}$ and $g : \mathrm{Lp} \to \mathrm{Xp}$, a proof that $g$ is surjective, and a proof of the inclusion $\ker g \le \operatorname{range} f$ — that is, right exactness of $\mathrm{Yq} \to \mathrm{Lp} \to \mathrm{Xp} \to 0$ recorded as an inclusion of submodules rather than an equality. Finally it carries two natural numbers `lam` and `mu` and five numerical constraints on dimensions, $\operatorname{finrank}_k \mathrm{Yp} = 2\mu$, $\operatorname{finrank}_k \mathrm{Lp} = 2\lambda$, $\operatorname{finrank}_k \mathrm{Yq} \le \mu$, $\operatorname{finrank}_k \mathrm{Lq} \le \lambda$, $\operatorname{finrank}_k \mathrm{Xp} \le \mu$, and the positivity $0 < \lambda$. Thus the whole structure is a theorem-free data package: the geometric provenance of the five spaces (character groups of toric parts and Brandt-module analogues, reduced modulo a maximal ideal of a Hecke algebra) and of the maps is not part of the Lean type, which refers only to $k$.
--
--   The second declaration is the predicate `SeqIso` on `ExchangeData k`, defined to hold exactly when $\operatorname{finrank}_k \mathrm{Yp} = \operatorname{finrank}_k \mathrm{Lq}$. It is therefore an equality of dimensions, not the datum of a linear isomorphism between the two spaces.
--
--   **Relation to Mathlib.** Mathlib has no notion of this kind of exchange datum; the structure is the project's own, built from Mathlib's `Module.Finite`, `Module.finrank`, and linear maps with `LinearMap.ker` and `LinearMap.range`.
--
--   **Where it is used.** The data assembled here are the hypotheses of the dimension count in the exchange case of Ribet's level-lowering theorem: from the constraints together with `SeqIso` one derives incompatible inequalities between $\lambda$ and $\mu$, contradicting $0 < \lambda$. Level lowering in turn converts the modularity of the Frey curve attached to a putative Fermat solution into a modular form of level $2$, which does not exist.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_RibetLevelLowering_ExchangeData.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Module

namespace RibetEndgame

structure ExchangeData (k : Type) [Field k] : Type 1 where

  Xp : Type
  [acgXp : AddCommGroup Xp]
  [modXp : Module k Xp]
  [finXp : Module.Finite k Xp]

  Yq : Type
  [acgYq : AddCommGroup Yq]
  [modYq : Module k Yq]
  [finYq : Module.Finite k Yq]

  Lp : Type
  [acgLp : AddCommGroup Lp]
  [modLp : Module k Lp]
  [finLp : Module.Finite k Lp]

  Yp : Type
  [acgYp : AddCommGroup Yp]
  [modYp : Module k Yp]
  [finYp : Module.Finite k Yp]

  Lq : Type
  [acgLq : AddCommGroup Lq]
  [modLq : Module k Lq]
  [finLq : Module.Finite k Lq]

  f : Yq →ₗ[k] Lp

  g : Lp →ₗ[k] Xp

  surj_g : Function.Surjective g

  exact_fg : LinearMap.ker g ≤ LinearMap.range f

  lam : ℕ

  mu : ℕ

  finrank_Yp : finrank k Yp = 2 * mu

  finrank_Lp : finrank k Lp = 2 * lam

  finrank_Yq_le : finrank k Yq ≤ mu

  finrank_Lq_le : finrank k Lq ≤ lam

  finrank_Xp_le : finrank k Xp ≤ mu

  lam_pos : 0 < lam

attribute [instance] ExchangeData.acgXp ExchangeData.modXp ExchangeData.finXp
attribute [instance] ExchangeData.acgYq ExchangeData.modYq ExchangeData.finYq
attribute [instance] ExchangeData.acgLp ExchangeData.modLp ExchangeData.finLp
attribute [instance] ExchangeData.acgYp ExchangeData.modYp ExchangeData.finYp
attribute [instance] ExchangeData.acgLq ExchangeData.modLq ExchangeData.finLq

namespace ExchangeData

variable {k : Type} [Field k]

def SeqIso (d : ExchangeData k) : Prop :=
  finrank k d.Yp = finrank k d.Lq

end ExchangeData

end RibetEndgame


