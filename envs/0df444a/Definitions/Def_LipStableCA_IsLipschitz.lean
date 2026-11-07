-- Prove2me | Definitions.Def_LipStableCA_IsLipschitz
-- name    : LipStableCA_IsLipschitz
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:48:11.457573+00:00
-- url     : https://prove2.me/theorems/3a25ec29-58ce-4274-b6a7-136405fbdc0c
-- title:
--   $K$-Lipschitz rules, $\alpha$-approximate rules, and the parameter $r$
-- statement:
--   A rule with allocation laws $P_v$ is $K$-Lipschitz if $\mathrm{EMD}(P_v,P_w)\le K\,d(v,w)$ whenever $d(v,w)<\infty$. It is $\alpha$-approximate if $\mathbb E_{S\sim P_v}[W_v(S)]\ge\alpha\,\mathrm{OPT}(v)$ at every valid profile. The parameter of §5 is $r=\min\{n,\,m/\log(m+1)\}$, with the natural logarithm.
--
--   **Formalization Note.** The paper's $\mathrm{Lip}(S)\le K$ is the predicate $K$-Lipschitz, since the valid constants form a closed set, and $\mathrm{Lip}(S)<\infty$ is the existence of a valid $K$.
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Def. 2.6, p.8; Def. 2.2, p.7; Thm 5.1, p.21

import Definitions.Def_LipStableCA_emd
import Definitions.Def_LipStableCA_profileDist

namespace LipStableCA

variable {n m : ℕ}

/-- `K`-Lipschitz, Definition 2.6, p.8: `EMD(P_v, P_w) ≤ K d(v, w)` whenever `d(v, w) < ∞`, for a rule
given by its allocation laws. **Formalization Note.** `Lip(S) ≤ K` is stated as `IsLipschitz P K`
(the inequalities are closed in `K`, so the infimum is attained when the set is nonempty) and
`Lip(S) < ∞` as `∃ K, IsLipschitz P K`. No real-valued `Lip` is defined: `sInf ∅ = 0` would hide the
infinite case. -/
def IsLipschitz (P : Profile n m → Alloc n m → ℝ) (K : ℝ) : Prop :=
  ∀ v w : Profile n m, IsProfile v → IsProfile w → profileDist v w ≠ ⊤ →
    emd (P v) (P w) ≤ K * (profileDist v w).toReal

/-- `α`-approximate, Definition 2.2, p.7: `SW(v) ≥ α OPT(v)` at every profile. -/
def IsApprox (P : Profile n m → Alloc n m → ℝ) (α : ℝ) : Prop :=
  ∀ v : Profile n m, IsProfile v → α * opt v ≤ expectedWelfare v (P v)

/-- The parameter `r = min{n, m / log(m + 1)}` of Theorems 5.1 and 5.2, p.21 (natural logarithm). For
`m ≥ 1` the logarithm is positive, so `r > 0` when also `n ≥ 1`. -/
noncomputable def ratioParam (n m : ℕ) : ℝ :=
  min (n : ℝ) ((m : ℝ) / Real.log ((m : ℝ) + 1))

end LipStableCA


