-- Prove2me | Definitions.Def_UltimateL_VHierarchy
-- name    : UltimateL_VHierarchy
-- status  : Definition
-- author  : @LG
-- created : 2026-11-22T20:46:06.604803+00:00
-- url     : https://prove2.me/theorems/ba89ec40-1766-4cbc-8462-41e97aa93b7d
-- title:
--   The cumulative hierarchy $V_\alpha$ as a set
-- statement:
--   For each ordinal $\alpha$, $V_\alpha$ is the **rank initial segment** consisting of all sets whose rank is below $\alpha$. It is presented here as a single set (an element of the ambient universe of ZFC sets), namely the range of the inclusion of the subtype of sets of rank $<\alpha$. The membership criterion $x\in V_\alpha\iff \mathrm{rank}(x)<\alpha$ is recorded as `mem_vLevel`. These rank segments are the domains and codomains of the elementary embeddings used to define extendible cardinals, and the structures $V_\eta$ over which $\Sigma_2$-definability is evaluated.
-- source:
--   W. Hugh Woodin, In Search of Ultimate-L: The 19th Midrasha Mathematicae Lectures, Bulletin of Symbolic Logic 23(1) (2017) 1-109, doi:10.1017/bsl.2016.34; the cumulative hierarchy V_alpha is standard (Kanamori, The Higher Infinite, 2nd ed., Springer 2003, §1).

import Mathlib

namespace UltimateL

universe u

open ZFSet

/-- The rank initial segment `V_α`, as a set: the sets of rank `< α`. We take this to be
Mathlib's von Neumann hierarchy `ZFSet.vonNeumann`, the cumulative hierarchy
(`V_0 = ∅`, `V_{α+1} = powerset (V_α)`, `V_λ = ⋃_{β<λ} V_β`), which is universe-polymorphic. -/
noncomputable def vLevel (α : Ordinal.{u}) : ZFSet.{u} := ZFSet.vonNeumann α

/-- Membership in `V_α` is exactly having rank below `α` (Mathlib's `ZFSet.mem_vonNeumann`). -/
theorem mem_vLevel {α : Ordinal.{u}} {x : ZFSet.{u}} : x ∈ vLevel α ↔ x.rank < α := by
  change x ∈ ZFSet.vonNeumann α ↔ x.rank < α
  exact ZFSet.mem_vonNeumann

end UltimateL


