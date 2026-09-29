-- Prove2me | Definitions.Def_Gamma0AwayUnitsChar
-- name    : Gamma0AwayUnitsChar
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/74141c7f-4fc4-54e6-9547-54bac3e713e0
-- title:
--   Lower-right-entry character of Γ₀(N) over ℤ[1/q]
-- statement:
--   Throughout, $N$ and $q$ are natural numbers, $\mathrm{ZAway}\,q$ denotes the localisation of $\mathbb{Z}$ away from $q$ (written $\mathbb{Z}[1/q]$ below), and $\mathrm{Gamma0Away}\,N\,q$ is the subgroup of $\mathrm{SL}_2(\mathbb{Z}[1/q])$ consisting of those $g$ whose entry $g_{10}$ is divisible by $N$ in $\mathbb{Z}[1/q]$. Given coprimality of $N$ and $q$, the image of $q$ in $\mathbb{Z}/N$ is a unit (`isUnit_intCast_q`), so reduction modulo $N$ extends along the localisation to a ring homomorphism `zAwayToZMod` $\colon \mathbb{Z}[1/q] \to \mathbb{Z}/N$, characterised by its values $a \bmod N$ on $a \in \mathbb{Z}$; it sends $N$ to $0$, hence kills the lower left entry of any element of $\mathrm{Gamma0Away}\,N\,q$. From this, `gamma0AwayMap` is the homomorphism of multiplicative monoids $\mathrm{Gamma0Away}\,N\,q \to \mathbb{Z}/N$ given by $g \mapsto g_{11} \bmod N$, multiplicativity coming from the vanishing of the cross term $g_{10}h_{01}$ modulo $N$; `gamma0AwayUnitsChar` is the induced group homomorphism into $(\mathbb{Z}/N)^{\times}$, whose underlying element of $\mathbb{Z}/N$ is that same reduction of the lower right entry.
--
--   Two embeddings of the classical congruence subgroup are recorded as maps into the subgroup: `vertexZeroAway` is the entrywise inclusion $\Gamma_0(N) \to \mathrm{SL}_2(\mathbb{Z}[1/q])$, and `vertexOneAway` is its conjugate $\gamma \mapsto \mathrm{diag}(1,q)\,\gamma\,\mathrm{diag}(1,q)^{-1}$, both corestricted to $\mathrm{Gamma0Away}\,N\,q$. The final two theorems state the equality of group homomorphisms $\Gamma_0(N) \to (\mathbb{Z}/N)^{\times}$ obtained by composing `gamma0AwayUnitsChar` with either embedding and the character `gamma0UnitsHom` $N$, namely $\gamma \mapsto \gamma_{11} \bmod N$: conjugation by $\mathrm{diag}(1,q)$ leaves the lower right entry unchanged.
--
--   **Relation to Mathlib.** Mathlib supplies $\Gamma_0(N) \le \mathrm{SL}_2(\mathbb{Z})$ together with its lower-right-entry map `CongruenceSubgroup.Gamma0Map` into $\mathbb{Z}/N$, and the localisation machinery `IsLocalization.Away.lift`; the $\mathbb{Z}[1/q]$-analogue $\mathrm{Gamma0Away}$ and its unit-valued character are the project's own.
--
--   **Where it is used.** These definitions belong to the setting of Ihara's lemma, where $\Gamma_0(N)$ acts on the Bruhat–Tits tree of $\mathrm{SL}_2(\mathbb{Q}_q)$ and $\mathrm{SL}_2(\mathbb{Z}[1/q])$-level groups are presented as amalgams of two copies of $\Gamma_0(N)$ over $\Gamma_0(Nq)$ via the two embeddings above. The character recorded here is the homomorphism to $(\mathbb{Z}/N)^{\times}$ through which abelian quotients of $\Gamma_0(N)(\mathbb{Z}[1/q])$ are controlled, the compatibility statements being what makes it descend from the amalgam.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Gamma0AwayUnitsChar.lean

import Definitions.Def_Gamma0Away
import Definitions.Def_Gamma0UnitsChar
import Definitions.Def_IharaAmalgamMap
import Mathlib.Data.ZMod.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace Ihara

open Matrix

open scoped MatrixGroups

variable (N q : ℕ)

theorem isUnit_intCast_q (hNq : Nat.Coprime N q) : IsUnit (((q : ℤ) : ZMod N)) := by
  have h : ((ZMod.unitOfCoprime q hNq.symm : (ZMod N)ˣ) : ZMod N) = (((q : ℤ)) : ZMod N) := by
    rw [ZMod.coe_unitOfCoprime, Int.cast_natCast]
  exact h ▸ (ZMod.unitOfCoprime q hNq.symm).isUnit

noncomputable def zAwayToZMod (hNq : Nat.Coprime N q) : ZAway q →+* ZMod N :=
  IsLocalization.Away.lift (S := ZAway q) (g := Int.castRingHom (ZMod N)) (q : ℤ)
    (by rw [eq_intCast]; exact isUnit_intCast_q N q hNq)

@[simp]
theorem zAwayToZMod_algebraMap (hNq : Nat.Coprime N q) (a : ℤ) :
    zAwayToZMod N q hNq (algebraMap ℤ (ZAway q) a) = (a : ZMod N) := by
  rw [zAwayToZMod, IsLocalization.Away.lift_eq, eq_intCast]

theorem zAwayToZMod_natCast_self (hNq : Nat.Coprime N q) :
    zAwayToZMod N q hNq (N : ZAway q) = 0 := by
  have h : ((N : ℕ) : ZAway q) = algebraMap ℤ (ZAway q) ((N : ℕ) : ℤ) := by simp
  rw [h, zAwayToZMod_algebraMap, Int.cast_natCast, ZMod.natCast_self]

theorem zAwayToZMod_apply_one_zero (hNq : Nat.Coprime N q) (g : Gamma0Away N q) :
    zAwayToZMod N q hNq ((g : SL(2, ZAway q)) 1 0) = 0 := by
  obtain ⟨r, hr⟩ := g.2
  rw [hr, map_mul, zAwayToZMod_natCast_self, zero_mul]

noncomputable def gamma0AwayMap (hNq : Nat.Coprime N q) : Gamma0Away N q →* ZMod N where
  toFun g := zAwayToZMod N q hNq ((g : SL(2, ZAway q)) 1 1)
  map_one' := by
    have h : ((1 : Gamma0Away N q) : SL(2, ZAway q)) 1 1 = 1 := rfl
    rw [h, map_one]
  map_mul' a b := by
    have h : ((a * b : Gamma0Away N q) : SL(2, ZAway q)) 1 1
        = (a : SL(2, ZAway q)) 1 0 * (b : SL(2, ZAway q)) 0 1
          + (a : SL(2, ZAway q)) 1 1 * (b : SL(2, ZAway q)) 1 1 :=
      (Matrix.two_mul_expl (a : SL(2, ZAway q)).1 (b : SL(2, ZAway q)).1).2.2.2
    rw [h, map_add, map_mul, map_mul, zAwayToZMod_apply_one_zero N q hNq a, zero_mul,
      zero_add]

noncomputable def gamma0AwayUnitsChar (hNq : Nat.Coprime N q) :
    Gamma0Away N q →* (ZMod N)ˣ :=
  (gamma0AwayMap N q hNq).toHomUnits

@[simp]
theorem gamma0AwayUnitsChar_coe (hNq : Nat.Coprime N q) (g : Gamma0Away N q) :
    (gamma0AwayUnitsChar N q hNq g : ZMod N) = gamma0AwayMap N q hNq g :=
  rfl

noncomputable def vertexZeroAway : CongruenceSubgroup.Gamma0 N →* Gamma0Away N q :=
  (vertexZero N q).codRestrict (Gamma0Away N q) (vertexZero_mem N q)

noncomputable def vertexOneAway : CongruenceSubgroup.Gamma0 N →* Gamma0Away N q :=
  (vertexOne N q).codRestrict (Gamma0Away N q) (vertexOne_mem N q)

theorem gamma0AwayUnitsChar_comp_vertexZeroAway (hNq : Nat.Coprime N q) :
    (gamma0AwayUnitsChar N q hNq).comp (vertexZeroAway N q) = gamma0UnitsHom N := by
  ext g
  show zAwayToZMod N q hNq ((vertexZero N q g : SL(2, ZAway q)) 1 1)
      = CongruenceSubgroup.Gamma0Map N g
  have h : (vertexZero N q g : SL(2, ZAway q)) 1 1
      = algebraMap ℤ (ZAway q) ((g : SL(2, ℤ)) 1 1) := rfl
  rw [h, zAwayToZMod_algebraMap]
  rfl

theorem gamma0AwayUnitsChar_comp_vertexOneAway (hNq : Nat.Coprime N q) :
    (gamma0AwayUnitsChar N q hNq).comp (vertexOneAway N q) = gamma0UnitsHom N := by
  ext g
  show zAwayToZMod N q hNq ((vertexOne N q g : SL(2, ZAway q)) 1 1)
      = CongruenceSubgroup.Gamma0Map N g
  have h : (vertexOne N q g : SL(2, ZAway q)) 1 1
      = algebraMap ℤ (ZAway q) ((g : SL(2, ℤ)) 1 1) := by
    rw [coe_vertexOne_eq]
    rfl
  rw [h, zAwayToZMod_algebraMap]
  rfl

end Ihara


