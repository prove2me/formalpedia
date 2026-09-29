-- Prove2me | Definitions.Def_HeckeEis_Gamma0NebenRep
-- name    : HeckeEis_Gamma0NebenRep
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/b75b2bcb-e814-5cc7-9809-8803bda3b7a2
-- title:
--   Mod-p nebentypus characters of Γ0​(M) and their representations
-- statement:
--   Fix a natural number $p$, a natural number $M$ with $p \mid M$, a commutative ring $\kappa$ of characteristic $p$, and a natural number $e$. The first definition, `gamma0NebenChar`, is the monoid homomorphism $\Gamma_0(M) \to \kappa$ (into the multiplicative monoid of $\kappa$) obtained by composing four maps: Mathlib's homomorphism `Gamma0Map M`, which sends $\gamma \in \Gamma_0(M) \subseteq \mathrm{SL}_2(\mathbb{Z})$ to the reduction modulo $M$ of its lower right entry $\gamma_{1,1}$; the reduction $\mathbb{Z}/M \to \mathbb{Z}/p$, which is a ring homomorphism because $p \mid M$; the canonical ring homomorphism $\mathbb{Z}/p \to \kappa$ coming from the characteristic hypothesis; and raising to the $e$-th power. Thus, writing $\gamma = \begin{pmatrix} a & b \\ c & d\end{pmatrix}$, one has $\mathrm{gamma0NebenChar}(\gamma) = (d \bmod p)^e$ read in $\kappa$; this is recorded explicitly in `gamma0NebenChar_apply`.
--
--   The second definition, `gamma0NebenRep`, is the associated one-dimensional representation of $\Gamma_0(M)$ over $\kappa$: a term of Mathlib's type `Representation κ (Gamma0 M) κ`, i.e. a monoid homomorphism from $\Gamma_0(M)$ to the $\kappa$-linear endomorphisms of $\kappa$, in which $\gamma$ acts by multiplication by the scalar $\mathrm{gamma0NebenChar}(\gamma)$. Two further lemmas describe it: `gamma0NebenRep_apply` states that $\gamma$ sends $v \in \kappa$ to $\mathrm{gamma0NebenChar}(\gamma)\, v$, and `gamma0NebenRep_zero` states that for $e = 0$ the representation is the trivial one, the identity element of the monoid of representations. The parameters $p$, $M$, the divisibility proof $p \mid M$, the coefficient ring $\kappa$ and the exponent $e$ are all explicit arguments of both definitions.
--
--   **Relation to Mathlib.** Built from Mathlib's `CongruenceSubgroup.Gamma0` together with its lower-right-entry homomorphism `Gamma0Map`, Mathlib's `ZMod.castHom` reductions, and Mathlib's `Representation`; the packaging of the $e$-th power of the mod-$p$ nebentypus character as a one-dimensional representation is the project's own.
--
--   **Where it is used.** These characters and one-dimensional representations serve as coefficient modules for group cohomology of $\Gamma_0(M)$ in the mod-$p$ Hecke/Eisenstein part of the argument, where weight-two forms on $\Gamma_0(M)$ with nebentypus a power of the Teichmüller character at $p$ are compared with forms of other weights and levels.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_HeckeEis_Gamma0NebenRep.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace HeckeEis

open CongruenceSubgroup
open scoped MatrixGroups

noncomputable def gamma0NebenChar (p M : ℕ) (hpM : p ∣ M) (κ : Type*) [CommRing κ] [CharP κ p] (e : ℕ) :
    Gamma0 M →* κ :=
  (powMonoidHom e).comp
    ((ZMod.castHom (dvd_refl p) κ).toMonoidHom.comp
      ((ZMod.castHom hpM (ZMod p)).toMonoidHom.comp (Gamma0Map M)))

theorem gamma0NebenChar_apply (p M : ℕ) (hpM : p ∣ M) (κ : Type*) [CommRing κ] [CharP κ p] (e : ℕ)
    (γ : Gamma0 M) :
    gamma0NebenChar p M hpM κ e γ =
      (ZMod.castHom (dvd_refl p) κ (ZMod.castHom hpM (ZMod p) (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M))) ^ e :=
  rfl

noncomputable def gamma0NebenRep (p M : ℕ) (hpM : p ∣ M) (κ : Type*) [CommRing κ] [CharP κ p] (e : ℕ) :
    Representation κ (Gamma0 M) κ :=
  (DistribMulAction.toModuleEnd κ κ).comp (gamma0NebenChar p M hpM κ e)

@[simp]
theorem gamma0NebenRep_apply (p M : ℕ) (hpM : p ∣ M) (κ : Type*) [CommRing κ] [CharP κ p] (e : ℕ)
    (γ : Gamma0 M) (v : κ) :
    gamma0NebenRep p M hpM κ e γ v = gamma0NebenChar p M hpM κ e γ * v :=
  rfl

theorem gamma0NebenRep_zero (p M : ℕ) (hpM : p ∣ M) (κ : Type*) [CommRing κ] [CharP κ p] :
    gamma0NebenRep p M hpM κ 0 = 1 := by
  refine MonoidHom.ext fun γ => LinearMap.ext fun v => ?_
  simp [gamma0NebenChar]

end HeckeEis


