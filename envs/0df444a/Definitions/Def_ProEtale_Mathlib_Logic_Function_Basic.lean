-- Prove2me | Definitions.Def_ProEtale_Mathlib_Logic_Function_Basic
-- name    : ProEtale_Mathlib_Logic_Function_Basic
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T16:59:49.508187+00:00
-- url     : https://prove2.me/theorems/91c5fdf3-545c-41a9-a521-6d461a629096
-- title:
--   If $g \circ f = \mathrm{id}$ and $g$ is bijective, then $f$ is bijective
-- statement:
--   Let $f : \alpha \to \beta$ and $g : \beta \to \alpha$ be maps with $g(f(x)) = x$ for all $x \in \alpha$, i.e. $g$ is a left inverse of $f$. If $g$ is bijective, then $f$ is bijective, and in fact $f = g^{-1}$.
--
--   This basic fact is used to show that sections of bijective maps (e.g. of rings or spaces) are bijective.
--
--   **Formalization Note** The theorem is `Function.bijective_of_leftInverse_of_bijective`, with hypotheses `h : Function.LeftInverse g f` (meaning `g (f x) = x`) and `hg : Function.Bijective g`, and conclusion `Function.Bijective f`. The docstring calls $f$ "a left inverse of" $g$. Literally, the hypothesis says $g$ is a left inverse of $f$ (equivalently, $f$ is a right inverse of $g$).
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/Logic/Function/Basic.lean (declarations needed by the transplanted proofs, unused ones removed).

/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Logic.Function.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# A left inverse of a bijection is bijective
-/

/-- A left inverse `f` of a bijection `g` is itself bijective. -/
theorem Function.bijective_of_leftInverse_of_bijective {α β : Type*} {f : α → β} {g : β → α}
    (h : Function.LeftInverse g f) (hg : Function.Bijective g) : Function.Bijective f :=
  ⟨h.injective, fun x ↦ ⟨g x, hg.injective (h (g x))⟩⟩


