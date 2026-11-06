-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_IsCanonicalPath
-- name    : KawasakiSOS_Threshold_IsCanonicalPath
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:09:27.387203+00:00
-- url     : https://prove2.me/theorems/018d65bc-a6ad-4643-a4cd-56ca37ff6afd
-- title:
--   The canonical path $\gamma_{xy}$
-- statement:
--   Fix $x\ne y$ in $\Omega$, with base column $p_0$. The canonical path $\gamma_{xy}$ is the concatenation of three parts along a site sequence:
--
--   1. the opening, a walk given by Lemma 4.10 with $h=x$, $B=B_0=\{p_0-1,\dots,p_0+3\}$ and $t=\xi_0=p_0+1$ the center of $B_0$, ending at $z_{S_0,\xi_0}$;
--   2. the realizations of all slides $S_0\to\dots\to S_f$ between the stages of the site sequence;
--   3. the closing, the reversal of a walk given by Lemma 4.10 with $h=y$, $B=B_f$ and $t=\xi_f$, starting from $z_{S_f,\xi_f}$.
--
--   **Formalization Note** The source makes its choices "canonically (for instance, smallest index first)" without fixing them, so this is a predicate satisfied by every admissible choice, and statements quantify over all of them. The block $B_f$ has first site $c_A(S_f)-1$.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 14 (PDF p. 15)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Config
import Definitions.Def_KawasakiSOS_Threshold_Segment
import Definitions.Def_KawasakiSOS_Threshold_cycleBase
import Definitions.Def_KawasakiSOS_Threshold_IsSiteSequence
import Definitions.Def_KawasakiSOS_Threshold_stageOf
import Definitions.Def_KawasakiSOS_Threshold_IsZState
import Definitions.Def_KawasakiSOS_Threshold_IsOpening
import Definitions.Def_KawasakiSOS_Threshold_IsSlideChain

namespace KawasakiSOS.Threshold

/-- `segs` is a canonical path from `x` to `y` along the site sequence `σ`: the opening with `h = x`, `B = B_0`, `t` the centre of `B_0`; one realization per change of stage along `σ`; and the reversed closing with `h = y`, `B = B_f`, `t = ξ_f`. Formalization Note: all tie-breaks are left open ("All choices below are made canonically", p. 10), so a statement quantified over every such path covers the paper's choice (reading R7).

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 14 (PDF p. 15). -/
def IsCanonicalPath {n k : ℕ} [NeZero k] (x y : Config n k) (σ : List (ℕ × ℕ))
    (segs : List (Segment k × List (Config n k))) : Prop :=
  IsSiteSequence x y (cycleBase x y) σ ∧
  ∃ (S₀ Sf : Stage k) (rest : List (Stage k)) (ξf o₁ o₂ : ZMod k) (g₁ g₂ : Config n k)
    (ops₁ ops₂ : List (ZMod k × ZMod k)) (l₁ l₂ : List (Config n k))
    (mid : List (Segment k × List (Config n k))),
    σ.map (fun q => stageOf k (cycleBase x y) q.1 q.2) = S₀ :: rest ∧
    (S₀ :: rest).getLast? = some Sf ∧
    IsZState x y S₀ (cycleBase x y + 1) g₁ ∧
    IsOpening x (cycleBase x y - 1) (cycleBase x y + 1) o₁ g₁ ops₁ l₁ ∧
    IsSlideChain x y S₀ (cycleBase x y + 1) rest ξf mid ∧
    IsZState x y Sf ξf g₂ ∧
    IsOpening y (Sf.cA - 1) ξf o₂ g₂ ops₂ l₂ ∧
    segs = (Segment.opening, l₁) :: mid ++ [(Segment.closing, l₂.reverse)]

end KawasakiSOS.Threshold


