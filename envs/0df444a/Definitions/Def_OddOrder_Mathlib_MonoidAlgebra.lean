-- Prove2me | Definitions.Def_OddOrder_Mathlib_MonoidAlgebra
-- name    : OddOrder_Mathlib_MonoidAlgebra
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:40:12.225425+00:00
-- url     : https://prove2.me/theorems/f55d3011-b1aa-4bdb-938c-6807397d63b4
-- title:
--   Gap-filling lemma for `MonoidAlgebra`
-- statement:
--   In recent Mathlib, `MonoidAlgebra R M` is a structure with a `coeff` field rather than a transparent alias of `M →₀ R`, so reading one coefficient of a finite sum takes two steps (`MonoidAlgebra.coeff_sum`, then `Finsupp.finsetSum_apply`). This file bundles the combination as `MonoidAlgebra.coeff_finsetSum`: the coefficient of a finite sum is the finite sum of coefficients. It is used frequently in the block-theory files.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 1 supporting lemma used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Mathlib/MonoidAlgebra.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Mathlib/MonoidAlgebra.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain

namespace MonoidAlgebra

variable {R M ι : Type*} [Semiring R]

/-- **有限和の係数は係数の有限和.**

`MonoidAlgebra.coeff_sum` は `M →₀ R` の等式として同じことを述べるが、こちらは既に 1 点で
評価した形 — 単一の係数を計算するときに必要になるのは常にこの形。 -/
theorem coeff_finsetSum (s : Finset ι) (f : ι → MonoidAlgebra R M) (m : M) :
    (∑ i ∈ s, f i).coeff m = ∑ i ∈ s, (f i).coeff m := by
  rw [coeff_sum]
  exact Finsupp.finsetSum_apply _ _ _

end MonoidAlgebra


