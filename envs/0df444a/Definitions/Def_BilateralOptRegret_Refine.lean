-- Prove2me | Definitions.Def_BilateralOptRegret_Refine
-- name    : BilateralOptRegret_Refine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:43:04.070189+00:00
-- url     : https://prove2.me/theorems/d55666e1-08a6-4f57-816e-b6b7407a985b
-- title:
--   Algorithm 3 — Refine, and the parameter $A(K,\delta)=c_0\ell_K^6\log(24K^3/\delta)$
-- statement:
--   **Algorithm 3**, Refine$(G,\hat F,\varepsilon_i,\delta)$: let $\varepsilon_{i+1}=\varepsilon_i/8$; construct $G_{\mathrm{tar}},G_{\mathrm{qry}}$ by (17) and the maps by Algorithm 2; with $\beta=\varepsilon_{i+1}/(8\ell_K)$ and $\delta_B=\delta/(6K^2)$, run BinS on every fixed-endpoint block with distinct endpoints and an eligible row. For each row $j$ containing a target point, choose a reference point $a_j=x_{\iota_j,j}\in G_{\mathrm{tar}}$ and estimate $F(a_j)$ by $n_A=\lceil 2\varepsilon_{i+1}^{-2}\log(4K/\delta)\rceil$ fresh observations. For each $x_{a,j}\in G_{\mathrm{tar}}$ set
--   $$\hat F_{\mathrm{new}}(x_{a,j})=\mathrm{clip}_{[0,1]}\big(\hat F(a_j)+\hat D_j(a,\iota_j)\big),$$
--   where $\hat F(a_j)$ here is the fresh estimate, and return $(G_{\mathrm{tar}},\hat F_{\mathrm{new}})$.
--
--   Section 9 uses this procedure with $A(K,\delta)=c_0\ell_K^6\log(24K^3/\delta)$ in Algorithm 1.
--
--   **Formalization Note** `relLearn` is lines 2–14 of the algorithm, the relative-learning procedure of p.37. $\log$ is natural. $\hat F_{\mathrm{new}}$ takes the value $0$ off $G_{\mathrm{tar}}$. The reference point is a selection from the targets of the row.
-- source:
--   Castiglioni, Lunghi, Marchesi, Optimal Regret for Profit Maximization in Bilateral Trade (manuscript, sha256 aafed174…), Algorithm 3, p.40; §8.1, p.39, (28); §9, p.42

import Mathlib
import Definitions.Def_BilateralProfit_QueryRoutine
import Definitions.Def_BilateralOptRegret_Model
import Definitions.Def_BilateralOptRegret_Program
import Definitions.Def_BilateralOptRegret_Oracle
import Definitions.Def_BilateralOptRegret_Phased
import Definitions.Def_BilateralOptRegret_Dyadic
import Definitions.Def_BilateralOptRegret_Maps
import Definitions.Def_BilateralOptRegret_BinS
import Definitions.Def_BilateralOptRegret_Blocks

namespace BilateralOptRegret

open BilateralProfit

/-! # Algorithm 3, Refine, and the paper's oracle parameter `A`

Castiglioni, Lunghi, Marchesi (manuscript, sha256 aafed174…), Algorithm 3, p.40; (28), p.39; §9, p.42.

**Formalization Note.** Here `ε` is the phase precision `ε_i`, so `ε_{i+1} = ε/8`. `log` is natural (forced by p.39
and p.45). "Choose a reference point" uses the selection rule `sel`, on the set of targets of the row. `relLearn` is
lines 2–14 of Algorithm 3, the procedure of Proposition 7.10, p.37; `refineAlg` is the whole algorithm.
`F̂_new` takes the value `0` off `G_tar`. `paperA c₀` is `A(K, δ) = c₀ ℓ_K⁶ log(24K³/δ)` of §9, with
`ℓ_K = log₂(K − 1) + 1` computed by `Nat.log`, which equals `n + 1` at `K = 2^n + 1`. -/

/-- The mappings of Algorithm 3, line 3: `v_j = BuildTargetMaps(G_tar, G_qry)`. -/
noncomputable def mapsOf {n : ℕ} (sel : Finset (Idx n) → Idx n) (G : Finset (Act n))
    (Fhat : Act n → ℝ) (ε : ℝ) : ℕ → Idx n → Idx n :=
  fun j => repAfter sel (gTar G Fhat ε) (gQry G Fhat ε) (j + 1)

/-- **Algorithm 3, lines 2–14** (the relative-learning procedure of p.37): the table of elementary estimates,
with `β = ε_{i+1}/(8ℓ_K)` and `δ_B = δ/(6K²)`. -/
noncomputable def relLearn {n : ℕ} (sel : Finset (Idx n) → Idx n) (G : Finset (Act n))
    (Fhat : Act n → ℝ) (ε δ : ℝ) : QTree (Act n) (Table n) :=
  runBlocks (mapsOf sel G Fhat ε) (gQry G Fhat ε) ((ε / 8) / (8 * (ell n : ℝ)))
    (δ / (6 * (Kof n : ℝ) ^ 2))

/-- The targets of row `j`. -/
def rowTargets {n : ℕ} (Gtar : Finset (Act n)) (j : Idx n) : Finset (Idx n) :=
  Finset.univ.filter fun a => (a, j) ∈ Gtar

/-- The rows `J_tar` with at least one target point (p.39). -/
def jTar {n : ℕ} (Gtar : Finset (Act n)) : Finset (Idx n) :=
  Finset.univ.filter fun j => (rowTargets Gtar j).Nonempty

/-- `n_A = ⌈2 ε_{i+1}⁻² log(4K/δ)⌉` (p.39). -/
noncomputable def nAOf (n : ℕ) (ε δ : ℝ) : ℕ :=
  ⌈2 * (ε / 8) ^ (-2 : ℤ) * Real.log (4 * (Kof n : ℝ) / δ)⌉₊

/-- Algorithm 3, lines 15–18: for each row of `J_tar`, the estimate of `F(a_j)` by `n_A` fresh observations at the
reference point `a_j = x_{ι_j,j}`, `ι_j = sel (rowTargets G_tar j)`. -/
noncomputable def refEstimates {n : ℕ} (sel : Finset (Idx n) → Idx n) (Gtar : Finset (Act n))
    (nA : ℕ) : QTree (Act n) (Idx n → ℝ) :=
  (jTar Gtar).toList.foldlM
    (fun est j =>
      qBind (sampleMean (sel (rowTargets Gtar j), j) nA) fun m => .done (Function.update est j m))
    (fun _ => 0)

/-- `clip_{[0,1]}` of (28), p.39. -/
noncomputable def clip01 (x : ℝ) : ℝ := max 0 (min 1 x)

/-- **Algorithm 3, p.40**, `Refine(G, F̂, ε_i, δ)`. It returns `G_tar` and `F̂_new` of (28), p.39:
`F̂_new(x_{a,j}) = clip_{[0,1]}(F̂(a_j) + D̂_j(a, ι_j))`. -/
noncomputable def refineAlg {n : ℕ} (sel : Finset (Idx n) → Idx n) : RefineProc n :=
  fun G Fhat ε δ =>
    qBind (relLearn sel G Fhat ε δ) fun tbl =>
      qBind (refEstimates sel (gTar G Fhat ε) (nAOf n ε δ)) fun refs =>
        .done (gTar G Fhat ε, fun q => by
          classical
          exact if q ∈ gTar G Fhat ε then
            clip01 (refs q.2 + Dhat tbl q.2 q.1 (sel (rowTargets (gTar G Fhat ε) q.2)))
          else 0)

/-- The parameter `A(K, δ) = c₀ ℓ_K⁶ log(24K³/δ)` of §9, p.42. -/
noncomputable def paperA (c₀ : ℝ) (K : ℕ) (δ : ℝ) : ℝ :=
  c₀ * ((Nat.log 2 (K - 1) + 1 : ℕ) : ℝ) ^ 6 * Real.log (24 * (K : ℝ) ^ 3 / δ)

end BilateralOptRegret


