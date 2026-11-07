-- Prove2me | Definitions.Def_StochAutoreg_IsPlacement
-- name    : StochAutoreg_IsPlacement
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:12:34.171216+00:00
-- url     : https://prove2.me/theorems/dc21fcd7-a904-408d-9b2c-c9790e92a4ec
-- title:
--   Distinct equal-length strings $b_1,\dots,b_K$
-- statement:
--   A family of strings $(b_j)_j$ is a **placement** when the strings are pairwise distinct and all of the same length. These are the strings from which the proof of Lemma 6.1 builds the roots, and their equal length makes the descendant sets $r_j\Sigma^\star$ disjoint.
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, Lemma 6.1 (proof), p.12; §3, p.7

import Mathlib

namespace StochAutoreg

/-- "Distinct equal-length strings `b₁, …, b_K`": the data from which the roots are built.
Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, Lemma 6.1 (proof), p.12, and §3, p.7. -/
def IsPlacement {ι : Type} (b : ι → List Bool) : Prop :=
  Function.Injective b ∧ ∀ i j, (b i).length = (b j).length

end StochAutoreg


