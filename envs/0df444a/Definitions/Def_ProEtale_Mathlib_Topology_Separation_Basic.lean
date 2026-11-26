-- Prove2me | Definitions.Def_ProEtale_Mathlib_Topology_Separation_Basic
-- name    : ProEtale_Mathlib_Topology_Separation_Basic
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:01:08.826051+00:00
-- url     : https://prove2.me/theorems/8b8dbfc2-2318-57f8-81d5-8a10ead2f4a6
-- title:
--   Points specialize to closed points in compact $T_0$ spaces; all sets are stable under specialization in $T_1$ spaces
-- statement:
--   Recall that $x$ specializes to $y$, written $x \rightsquigarrow y$, if $y \in \overline{\{x\}}$.
--
--   Results:
--   1. In a compact $T_0$ space $X$, every point $x$ specializes to some closed point: there is $c \in X$ with $\{c\}$ closed and $x \rightsquigarrow c$ (not necessarily unique).
--   2. In a $T_1$ space every subset $s$ is stable under specialization: if $x \rightsquigarrow y$ and $x \in s$ then $y \in s$ (since specialization is equality in a $T_1$ space).
--
--   These facts are used for spectral spaces such as prime spectra, e.g. to reduce statements to closed points.
--
--   **Formalization Note** The declarations are `exists_isClosed_specializes` (assumptions `[CompactSpace X] [T0Space X]`, conclusion `∃ c, IsClosed {c} ∧ x ⤳ c`) and `StableUnderSpecialization.of_t1Space`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/Topology/Separation/Basic.lean (declarations needed by the transplanted proofs, unused ones removed).

import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Separation.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-- In a compact, T0 space every point specializes to a (not necessarily unique) closed point. -/
lemma exists_isClosed_specializes {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T0Space X] (x : X) :
    ∃ (c : X), IsClosed {c} ∧ x ⤳ c := by
  obtain ⟨c, hx, hc⟩ := IsClosed.exists_closed_singleton (isClosed_closure (s := {x}))
    (Set.singleton_nonempty x |>.closure)
  use c, hc
  rwa [specializes_iff_mem_closure]

/-- In a `T1Space`, every set is stable under specialization. -/
lemma StableUnderSpecialization.of_t1Space {X : Type*} [TopologicalSpace X] [T1Space X]
    (s : Set X) : StableUnderSpecialization s :=
  fun _ _ hxy hx ↦ hxy.eq ▸ hx


