-- Prove2me | Definitions.Def_SATotalCoeffLB_Supplement_DependsOnAtMostFromW
-- name    : SATotalCoeffLB_Supplement_DependsOnAtMostFromW
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:31:20.579505+00:00
-- url     : https://prove2.me/theorems/360c6411-c6e5-47b2-8c94-a0522052b3f8
-- title:
--   $h$ depends on at most $k$ variables from $W$ (unrestricted in $Q$)
-- statement:
--   An element $h$ of $\mathbb R[W, Q]/\langle y^2 - 1 : y \in W\cup Q\rangle$ **depends on at most $k$ variables from $W$**, with unrestricted dependence on $Q$, if there is a set $S \subseteq W$ with $|S| \le k$ such that the value of $h$ at a point of $\{\pm1\}^{W \cup Q}$ is determined by its coordinates in $S$ together with all its coordinates in $Q$.
--
--   **Formalization Note** The $Q$-variables are not counted. This differs from the published `SATotalCoeffLB.DependsOnAtMost`, which counts every variable.
-- source:
--   Chen–Jin, Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for Sherali–Adams, STOC 2027 submission (manuscript sha256 da19ece6…9d9178), p.6 (Locality); p.8 (Theorem 2); Theorem 9, item 1, p.74

import Mathlib
import Definitions.Def_SATotalCoeffLB_CubeFn

namespace SATotalCoeffLB.Supplement

open SATotalCoeffLB

/-- **`h` depends on at most `k` variables from `W`, with unrestricted dependence on `Q`**
(p.6, "Locality"; p.8, Theorem 2; Theorem 9, item 1, p.74, of Chen–Jin, *Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for
Sherali–Adams*, STOC 2027 submission manuscript
(sha256 da19ece6898e20b159d01408327de710d69219772cc1f088c80301a6679d9178)): there is a set `S` of at
most `k` variables of `W` such that the value of `h` is determined by the bits of `S` together
with all bits of `Q`.

**Formalization Note** The variables of `Q` are not counted (contrast `DependsOnAtMost`, which
counts every variable). -/
def DependsOnAtMostFromW {W Q : Type*} (k : ℕ) (h : CubeFn (W ⊕ Q)) : Prop :=
  ∃ S : Finset W, S.card ≤ k ∧ ∀ z z' : W ⊕ Q → ZMod 2,
    (∀ w ∈ S, z (Sum.inl w) = z' (Sum.inl w)) → (∀ j, z (Sum.inr j) = z' (Sum.inr j)) → h z = h z'

end SATotalCoeffLB.Supplement


