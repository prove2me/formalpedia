-- Prove2me | Definitions.Def_AnytimeAdaVR_SMKind
-- name    : AnytimeAdaVR_SMKind
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:26:46.159904+00:00
-- url     : https://prove2.me/theorems/d3e513bd-c645-4bd4-ada6-d2ded92ce42e
-- title:
--   Block-path type S or M
-- statement:
--   The type of an adaptive block path: **S** or **M**. In Appendix C the paper encodes it by $p=2$ for S and $p=1$ for M.
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41…74006), Algorithm 2, p.8; App. C, p.19

import Mathlib

namespace AnytimeAdaVR

/-- **The block-path type S or M.** Jiang–Wang–Yang–Zhang–Li, *Adaptive Variance Reduction across
Smoothness and Noise Conditions* (preprint, 2026), Algorithm 2, p.8: "Require: Initial point xinit and
path type S or M". In Appendix C (p.19) the paper writes `p = 2` for S and `p = 1` for M. -/
inductive SMKind
  | S
  | M
  deriving DecidableEq, Inhabited

instance : Fintype SMKind :=
  ⟨{.S, .M}, by intro x; cases x <;> simp⟩

end AnytimeAdaVR


