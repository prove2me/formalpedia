-- Prove2me | Definitions.Def_PolyContract_Supplement_gfun
-- name    : PolyContract_Supplement_gfun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:59:55.453973+00:00
-- url     : https://prove2.me/theorems/4f6bf585-8390-4ebb-b2fa-0577845fb46d
-- title:
--   Comb gadget levels: $g_j$, $f_{k+1}$, $h_{k+1}$, full-plane marginals, gap, contacts $\Gamma_j$
-- statement:
--   The levels of the comb gadget (Definition C.11): $g_0:=f_0$ on $E_0$, and at step $j\ge1$
--   $$f_j(S):=g_{j-1}(S\cap E_{j-1})+F^{(j)}_{\tau_1}[\tau_{1,j}\in S]+F^{(j)}_{\tau_2}[\tau_{2,j}\in S],\qquad h_j:=f_j-d_j,$$
--   and $g_j$ is the extension of $f_j$ by $b_j$: $g_j(S):=f_j(S)$ and $g_j(S\cup\{b_j\}):=f_j(S)+K_j-d_j(S)$ for $S\subseteq E_{j-1}\cup\{\tau_{1,j},\tau_{2,j}\}$, all numbers from the parameter rule.
--
--   The module defines the instance of a set function on a finite subset of elements with the gadget's rewards and curvatures, the full-plane marginals $\rho^{(j)}:=\rho^{g_j}$ of level $j$ and $\rho^f,\rho^h$ of $f=f_{k+1}$, $h=h_{k+1}$ at the step $k\to k+1$, the reward $r(\xi^{(j)}(\alpha))$ of the full-plane best response of $g_j$, the line $L_j(\alpha)=p_j+q_j\alpha$, the **gap** $L_j(\alpha)-r(\xi^{(j)}(\alpha))$, and the contact set
--   $$\Gamma_j:=\Big\{\tfrac13+\sum_{i\in Q}\mu_i: Q\subseteq\{0,\dots,j\}\Big\}.$$
--
--   **Formalization Note** The set functions are written on all finite subsets of the ambient type and used only on subsets of the level's ground set. The marginals are taken at a chosen full-plane best response; since the full-plane best response exists and is unique (published milestone), it is that point. The reward uses the published full-plane reward.
-- source:
--   Klimm, Lippke, Warode, The Complexity of Continuous Contract Design over Polymatroids, arXiv:2611.04934 (version of November 3, 2026, sha256 18cfc0a5…), Definition C.11, p.57 (PDF p.58); App. B.6.1, p.28; §C.6.1, p.60

import Mathlib
import Definitions.Def_PolyContract_FullPlane
import Definitions.Def_PolyContract_BaseInstance
import Definitions.Def_PolyContract_Supplement_LevelParams

set_option autoImplicit false

namespace PolyContract.Supplement

/-- The set function `g_j` of level `j` of the comb gadget (Klimm, Lippke, Warode,
arXiv:2611.04934, version of November 3, 2026, sha256 18cfc0a5…, Definition C.11, p.57):
`g₀ := f₀` on `E₀`, and for `S ⊆ E_j ∪ {τ₁, τ₂}` at the step `j → j+1`,
`g_{j+1}(S) := f_{j+1}(S)` and `g_{j+1}(S ∪ {b_{j+1}}) := f_{j+1}(S) + K_{j+1} − d_{j+1}(S)`, where
`f_{j+1}(S) := g_j(S ∩ E_j) + F^{(j+1)}_{τ1}[τ_{1,j+1} ∈ S] + F^{(j+1)}_{τ2}[τ_{2,j+1} ∈ S]`.

**Formalization Note** `g_j` is written on all finite subsets of the ambient type `CombU` and is
used only on subsets of `E_j` (through `combInst`). `f₀` reads `S ∩ E₀` through `Finset.toLeft`. -/
noncomputable def gfun (μin : List ℕ) : ℕ → Finset CombU → ℝ
  | 0 => fun S => f0 S.toLeft
  | k + 1 => fun S =>
      (gfun μin k (S ∩ Elev k) + (if tau1 (k + 1) ∈ S then (params μin (k + 1)).Fτ1 else 0) +
          (if tau2 (k + 1) ∈ S then (params μin (k + 1)).Fτ2 else 0)) +
        if bnew (k + 1) ∈ S then (params μin (k + 1)).K - ∑ e ∈ S ∩ Eext k, dvec μin k e else 0

/-- `f_{k+1}(S) := g_k(S ∩ E_k) + F^{(k+1)}_{τ1}[τ_{1,k+1} ∈ S] + F^{(k+1)}_{τ2}[τ_{2,k+1} ∈ S]`
on `E_k ∪ {τ₁, τ₂}` (arXiv:2611.04934, Definition C.11, p.57). -/
noncomputable def ffun (μin : List ℕ) (k : ℕ) (S : Finset CombU) : ℝ :=
  gfun μin k (S ∩ Elev k) + (if tau1 (k + 1) ∈ S then (params μin (k + 1)).Fτ1 else 0) +
    (if tau2 (k + 1) ∈ S then (params μin (k + 1)).Fτ2 else 0)

/-- `h_{k+1} := f_{k+1} − d_{k+1}` on `E_k ∪ {τ₁, τ₂}` (arXiv:2611.04934, Definition C.11, p.57). -/
noncomputable def hfun (μin : List ℕ) (k : ℕ) (S : Finset CombU) : ℝ :=
  ffun μin k S - ∑ e ∈ S ∩ Eext k, dvec μin k e

/-- The instance `(G, m, β)` on the finite ground set `T ⊆ CombU`, with the rewards and curvatures
of the comb gadget (arXiv:2611.04934, Definition C.11, p.57). -/
noncomputable def combInst (T : Finset CombU) (G : Finset CombU → ℝ) : QuadInstance T where
  f S := G (S.map (Function.Embedding.subtype _))
  m e := mU e
  β e := βU e

/-- A chosen full-plane best response `ξ^g(α)` of an instance (arXiv:2611.04934, App. B.6.1, p.28).

**Formalization Note** For `g` submodular with `g(∅) = 0` and `m, β > 0`, the full-plane best
response exists and is unique (published milestone `PolyContract.fullPlane_existsUnique`), so the
choice is that point. -/
noncomputable def fpXi {ι : Type} [Fintype ι] [DecidableEq ι] (I : QuadInstance ι) (α : ℝ) : ι → ℝ :=
  Classical.epsilon fun y => I.IsFullPlaneBR α y

/-- The full-plane marginal `ρ^G_e(α) = α m_e − β_e ξ^G_e(α)` of an element `e ∈ T` for the instance
`combInst T G` (arXiv:2611.04934, App. B.6.1, p.28); `0` for `e ∉ T`, a value never used. -/
noncomputable def fpRho (T : Finset CombU) (G : Finset CombU → ℝ) (α : ℝ) (e : CombU) : ℝ :=
  if h : e ∈ T then (combInst T G).marginal α (fpXi (combInst T G) α) ⟨e, h⟩ else 0

/-- The full-plane marginals `ρ^{(j)} := ρ^{g_j}` of level `j` (arXiv:2611.04934, Definition C.11,
p.57). -/
noncomputable def rhoLev (μin : List ℕ) (j : ℕ) (α : ℝ) (e : CombU) : ℝ :=
  fpRho (Elev j) (gfun μin j) α e

/-- The full-plane marginals `ρ^f` of `f = f_{k+1}` at the step `k → k+1` (arXiv:2611.04934,
§C.6.1, p.60). -/
noncomputable def rhoF (μin : List ℕ) (k : ℕ) (α : ℝ) (e : CombU) : ℝ :=
  fpRho (Eext k) (ffun μin k) α e

/-- The full-plane marginals `ρ^h` of `h = f_{k+1} − d_{k+1}` at the step `k → k+1`
(arXiv:2611.04934, §C.6.1, p.60). -/
noncomputable def rhoH (μin : List ℕ) (k : ℕ) (α : ℝ) (e : CombU) : ℝ :=
  fpRho (Eext k) (hfun μin k) α e

/-- The reward `r(ξ^{(j)}(α))` of the full-plane best response of level `j` (arXiv:2611.04934,
Definition C.11, p.57). -/
noncomputable def rewardLev (μin : List ℕ) (j : ℕ) (α : ℝ) : ℝ :=
  (combInst (Elev j) (gfun μin j)).fpReward α

/-- The line `L_j(α) := p_j + q_j α` of level `j` (arXiv:2611.04934, Definition C.11, p.57). -/
noncomputable def lineLev (μin : List ℕ) (j : ℕ) (α : ℝ) : ℝ :=
  (params μin j).p + (params μin j).q * α

/-- The **gap** `L_j(α) − r(ξ^{(j)}(α))` of level `j` at `α` (arXiv:2611.04934, Definition C.11,
p.57). -/
noncomputable def gap (μin : List ℕ) (j : ℕ) (α : ℝ) : ℝ := lineLev μin j α - rewardLev μin j α

/-- `Γ_j := {ζ₁ + Σ_{i ∈ Q} µ_i : Q ⊆ {0, …, j}}` with `ζ₁ = 1/3` (arXiv:2611.04934,
Definition C.11, p.57). -/
def Γlev (μin : List ℕ) (j : ℕ) : Set ℝ :=
  {γ | ∃ Q ⊆ Finset.range (j + 1), γ = 1 / 3 + ∑ i ∈ Q, μs μin i}

end PolyContract.Supplement


