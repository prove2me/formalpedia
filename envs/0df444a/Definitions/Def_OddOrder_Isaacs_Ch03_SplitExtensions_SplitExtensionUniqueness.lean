-- Prove2me | Definitions.Def_OddOrder_Isaacs_Ch03_SplitExtensions_SplitExtensionUniqueness
-- name    : OddOrder_Isaacs_Ch03_SplitExtensions_SplitExtensionUniqueness
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:40:19.331133+00:00
-- url     : https://prove2.me/theorems/8bd20da9-2d92-421a-b6a2-a88743b5b1de
-- title:
--   Isaacs Lemma 3.1: uniqueness of split extensions up to isomorphism
-- statement:
--   Formalizes Isaacs, *Finite Group Theory*, §3A, Lemma 3.1 (pp. 69–70) in its two-abstract-groups form: if $N\trianglelefteq G$ is complemented by $H$ and $N_0\trianglelefteq G_0$ is complemented by $H_0$, and isomorphisms $N\cong N_0$, $H\cong H_0$ are compatible with the conjugation actions, then there is exactly one isomorphism $G\cong G_0$ extending them. So a split extension is determined up to isomorphism by $N$, $H$ and the action of $H$ on $N$. Existence goes through Mathlib's semidirect product.
--
--   The main definition is `conjAutHom`, the homomorphism $H\to\mathrm{Aut}(N)$ given by conjugation of a subgroup $H$ on a normal subgroup $N$.
--
--   The bundle also proves 1 supporting lemma used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch03_SplitExtensions/SplitExtensionUniqueness.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch03_SplitExtensions/SplitExtensionUniqueness.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.SemidirectProduct

namespace OddOrder.Isaacs.Ch03

variable {G G₀ : Type*} [Group G] [Group G₀]

section

/-- 正規部分群 `N ◁ G` への部分群 `H ≤ G` の共役作用を束ねた準同型 `H →* MulAut N`
(`n ↦ h * n * h⁻¹`).

mathlib の `Subgroup.normalizerMonoidHom : N.normalizer →* MulAut N` を
`N.normalizer = ⊤` で `H` 全体に引き戻した形 (仮定特殊化)。Isaacs が Lemma 3.1 /
Thm 3.2 で「`H` が `N` に共役で作用する」と書くときの作用がこれ。 -/
def conjAutHom (N H : Subgroup G) [N.Normal] : H →* MulAut N :=
  N.normalizerMonoidHom.comp (Subgroup.inclusion (N.normalizer_eq_top ▸ le_top))

@[simp]
theorem conjAutHom_apply_coe (N H : Subgroup G) [N.Normal] (h : H) (n : N) :
    ((conjAutHom N H h n : N) : G) = (h : G) * (n : G) * (h : G)⁻¹ :=
  rfl

end

end OddOrder.Isaacs.Ch03


