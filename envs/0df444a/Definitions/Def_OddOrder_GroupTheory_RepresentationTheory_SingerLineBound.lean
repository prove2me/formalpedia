-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SingerLineBound
-- name    : OddOrder_GroupTheory_RepresentationTheory_SingerLineBound
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:44:32.765771+00:00
-- url     : https://prove2.me/theorems/7d9ca2ae-29e6-42f1-9137-bb72e227f448
-- title:
--   The Singer line bound: $|C|\mid(p^q-1)/(p-1)$
-- statement:
--   The $\sigma$-theory foundation of Peterfalvi (9.7)(b), the Galois branch of `typeP_Galois`: a faithful irreducible action of a finite commutative group $C$ on an $\mathbb{F}_p$-space $M$ of order $p^q$ realizes the field $\mathbb{F}_{p^q}$ with $C\hookrightarrow\mathbb{F}_{p^q}^\times$ (the Singer embedding), giving $|C|\mid(p^q-1)/(p-1)$. It consists of lemmas only.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 1 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/SingerLineBound.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/SingerLineBound.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SingerField

namespace OddOrder.RepresentationTheory

universe u

/-- **Arithmetic core of the Singer line bound**: if `a ∣ p^q − 1` and `a` is coprime to `p − 1`,
then `a ∣ (p^q − 1)/(p − 1)`.

`p − 1` divides `p^q − 1` (`nat_sub_dvd_pow_sub_pow p 1 q`), so `p^q − 1 = (p − 1)·m` with
`m = (p^q − 1)/(p − 1)`; from `a ∣ (p − 1)·m` and `gcd(a, p − 1) = 1` the coprime cancellation
`Nat.Coprime.dvd_of_dvd_mul_left` gives `a ∣ m`.  Pure `ℕ` arithmetic, `sorry`-free. -/
theorem dvd_div_of_coprime_of_dvd_sub_one {p q a : ℕ} (hp : 1 ≤ p)
    (hadvd : a ∣ p ^ q - 1) (hcop : Nat.Coprime a (p - 1)) :
    a ∣ (p ^ q - 1) / (p - 1) := by
  -- `(p − 1) ∣ p^q − 1` via `1 ≡ p [MOD p−1]` raised to the `q`-th power.
  have hsub : (p - 1) ∣ p ^ q - 1 := by
    have hpmod : (1 : ℕ) ≡ p [MOD (p - 1)] := (Nat.modEq_iff_dvd' hp).mpr (dvd_refl (p - 1))
    have h := hpmod.pow q
    rw [one_pow] at h
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).mp h
  -- `p^q − 1 = (p − 1) · m` with `m = (p^q − 1)/(p − 1)`.
  have hfac : p ^ q - 1 = (p - 1) * ((p ^ q - 1) / (p - 1)) :=
    (Nat.mul_div_cancel' hsub).symm
  -- `a ∣ (p − 1) · m`, and `a` coprime to `p − 1`, so `a ∣ m`.
  rw [hfac] at hadvd
  exact hcop.dvd_of_dvd_mul_left hadvd

end OddOrder.RepresentationTheory


