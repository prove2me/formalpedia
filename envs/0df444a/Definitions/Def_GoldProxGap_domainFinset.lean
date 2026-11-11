-- Prove2me | Definitions.Def_GoldProxGap_domainFinset
-- name    : GoldProxGap_domainFinset
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:21:50.020407+00:00
-- url     : https://prove2.me/theorems/420f3511-5034-4d10-9c96-85dd5e9fab57
-- title:
--   Binary additive domains as finite sets, affine translates, and images in an extension field
-- statement:
--   In characteristic two, a **binary additive domain** of dimension $d$ in a field $\mathbb B$ is an $\mathbb F_2$-subspace $D\subseteq\mathbb B$ with $|D|=2^d$; an **affine translate** is $a+D$. When the challenge field is an extension $\mathbb F\supseteq\mathbb B$, the same domain is viewed inside $\mathbb F$.
--
--   This module records three small constructions used throughout: the set of elements of an additive subgroup $D$ as a finite set, the translate $a+S$ of a finite set, and the image of $S\subseteq\mathbb B$ in an extension $\mathbb F$.
--
--   **Formalization Note** A binary additive domain is an additive subgroup `D : AddSubgroup B` with `Nat.card D = 2^d`: in characteristic two every additive subgroup is an $\mathbb F_2$-subspace and its dimension is $\log_2|D|$. The image in $\mathbb F$ is taken along `algebraMap B F`.
-- source:
--   Dao, Kominers, Thaler, Zheng, Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields, STOC 2027 submission manuscript (2 November 2026, sha256 6c2d9cedf047e9f98d174f41e6742e827f7c6f0e1dd00939b3975e7fe66f4e4d), Definition 3.7, p.20; §3.1, p.19

import Mathlib

open scoped Classical

namespace GoldProxGap

/-!
# Additive domains as finite sets, their translates, and their images in an extension

Dao, Kominers, Thaler, Zheng, *Counterexamples to Beyond-Johnson Proximity Gaps over Binary
Fields*, STOC 2027 submission manuscript (2 November 2026, sha256 6c2d9ced…), Definition 3.7,
p.20, and §3.1 ("We write B for a field containing the domain before extending the challenge
field to F", p.19).

**Formalization Note.**
* A binary additive domain of dimension `d` in a field `B` of characteristic two is encoded as an
  additive subgroup `D : AddSubgroup B` with `Nat.card D = 2 ^ d`: in characteristic two every
  additive subgroup is an `F₂`-subspace, and its `F₂`-dimension is `log₂` of its size.
* `domainFinset D` is the set of its elements as a `Finset B`; `translateDomain a S` is the affine
  translate `a + S`; `pushDomain F S` is the image of `S ⊆ B` in a field `F` with `Algebra B F`
  (the same domain, viewed inside the challenge field).
-/

/-- The elements of an additive subgroup of a finite type, as a `Finset`. -/
noncomputable def domainFinset {B : Type*} [AddGroup B] [Fintype B] (D : AddSubgroup B) :
    Finset B :=
  Finset.univ.filter (fun x => x ∈ D)

/-- The translate `a + S` of a finite set. -/
noncomputable def translateDomain {B : Type*} [Add B] (a : B) (S : Finset B) : Finset B :=
  S.image (fun x => a + x)

/-- The image of a finite set `S ⊆ B` in an extension field `F ⊇ B`. -/
noncomputable def pushDomain {B : Type*} (F : Type*) [Field B] [Field F] [Algebra B F]
    (S : Finset B) : Finset F :=
  S.image (algebraMap B F)

end GoldProxGap


