-- Prove2me | Definitions.Def_TwoMasterRoommates_Capped_Compression
-- name    : TwoMasterRoommates_Capped_Compression
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:32:14.277334+00:00
-- url     : https://prove2.me/theorems/5c12a396-186a-4100-9d73-0e115ccf3529
-- title:
--   Whole-rank dense compression and observer-specific cap conversion
-- statement:
--   For a whole rank map $f:V\to R$, its attained values include the self entries. The dense rank of $x$ is the number of distinct attained values strictly smaller than $f(x)$. In a two-master instance each map is compressed separately, and observer classes are retained. An infinite cap stays infinite. The new finite cap is
--
--   $$\bigl|\{\rho\in r_v(V):\rho\le\kappa_v\}\bigr|-1,$$
--
--   where subtraction is in the integers and the attained-value set uses observer $v$'s own master. In particular a cap below every tier becomes $-1$.
--
--   A dense integer map has attained range exactly $\{0,\ldots,s-1\}$, where $s$ is its number of distinct attained values; for an empty population both sets are empty. The definitions provide the exact compression used before the batch algorithm and avoid altering cap acceptance when ranks are renumbered.
-- source:
--   Bin Yu, STOC 2027 submission #225 (October 2026), p. 4 (PDF p. 5), §3; p. 12 (PDF p. 13), Appendix B opening

import Mathlib
import Definitions.Def_TwoMasterRoommates_Capped_Instance

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TwoMasterRoommates.Capped

noncomputable def attained {R : Type} [LinearOrder R] {n : ℕ} (f : Fin n → R) : Finset R := by
  classical
  exact Finset.univ.image f

noncomputable def denseRank {R : Type} [LinearOrder R] {n : ℕ} (f : Fin n → R) (x : Fin n) : ℤ := by
  classical
  exact Int.ofNat ((attained f).filter fun r => r < f x).card

noncomputable def Instance.compress {R : Type} [LinearOrder R] {n : ℕ}
    (I : Instance R n) : Instance ℤ n := by
  classical
  exact ⟨I.isA, denseRank I.a, denseRank I.b, fun v =>
    if I.κ v = ⊤ then ⊤ else
      (((((attained (I.r v)).filter fun r => (r : WithTop R) ≤ I.κ v).card : ℤ) - 1) : WithTop ℤ)⟩

noncomputable def DenseMap {n : ℕ} (f : Fin n → ℤ) : Prop :=
  attained f = (Finset.range (attained f).card).image (fun t : ℕ => (t : ℤ))

noncomputable def Dense {n : ℕ} (I : Instance ℤ n) : Prop := DenseMap I.a ∧ DenseMap I.b

end TwoMasterRoommates.Capped


