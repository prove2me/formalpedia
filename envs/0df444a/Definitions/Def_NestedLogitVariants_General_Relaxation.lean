-- Prove2me | Definitions.Def_NestedLogitVariants_General_Relaxation
-- name    : NestedLogitVariants_General_Relaxation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T21:26:52.878988+00:00
-- url     : https://prove2.me/theorems/a913508b-8b7e-4b87-902e-ff7d6d549277
-- title:
--   A.4, pp. 47–48 — the box [0,1]^n, the relaxed objective of Case 1, the objective of (31), the fractional-prefix shape, R_ik' and q_ik'
-- statement:
--   The proof of Theorem 11 (Appendix A.4) relaxes an assortment $S_i$ to a vector $z_i\in[0,1]^n$. For a nest $i$ and a number $x$ it uses the objective of Case 1 (p. 47),
--   $$
--   F_i(z_i\mid x)=\Big(v_{i0}+\sum_{j\in N}v_{ij}z_{ij}\Big)^{\gamma_i}\left[\frac{\sum_{j\in N}r_{ij}v_{ij}z_{ij}}{v_{i0}+\sum_{j\in N}v_{ij}z_{ij}}-x\right],
--   $$
--   taken at $x=\beta\hat x$ on the page, and the objective of problem (31) of Case 2 (p. 48),
--   $$
--   \sum_{j\in N}r_{ij}v_{ij}z_{ij}-a\Big(v_{i0}+\sum_{j\in N}v_{ij}z_{ij}\Big)-b\Big(v_{i0}+\sum_{j\in N}v_{ij}z_{ij}\Big)^{1-\gamma_i},
--   $$
--   with $a=\beta\hat x$ and $b=\beta\hat y_i$ on the page. At the indicator vector of an assortment $S_i$, $F_i$ equals $V_i(S_i)^{\gamma_i}(R_i(S_i)-x)$.
--
--   A vector $z$ has the **fractional-prefix** form at product $k$ if $z_1=\dots=z_{k-1}=1$, $z_k\in[0,1]$ and $z_{k+1}=\dots=z_n=0$. Finally $R_{ik'}=\sum_{j=1}^{k'}r_{ij}v_{ij}$ and $q_{ik'}=\sum_{j=1}^{k'}v_{ij}$ are the revenue-weighted sum and the total weight of the first $k'$ products (p. 47).
--
--   **Formalization Note** Powers are `Real.rpow`. For $v_{i0}=0$ and $z=0$, Lean evaluates $F_i$ to $0^{\gamma_i}(0/0-x)=0$ and the term $0^{1-\gamma_i}$ of (31) to $0$ (for $\gamma_i\ne1$), where the page would read the latter as $+\infty$ when $\gamma_i>1$; the statement about (31) is therefore restricted to nests with $v_{i0}>0$, the only nests in which Case 2 arises. Products are indexed from $0$, so the fractional-prefix shape at the Lean index $k$ is the page's shape at $k+1$; $R_{ik'}$ and $q_{ik'}$ are sums over `nbr n k'`.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), pp. 47–48, Appendix A.4, Case 1 (the maximization problem, R_ik', q_ik') and Case 2 (problem (31))

import Mathlib
import Definitions.Def_NestedLogitVariants_General_Model

namespace NestedLogitVariants.General

variable {ι : Type*} {n : ℕ}

/-- The unit box `[0, 1]^n` of the decision vectors `z_i = (z_{i1}, …, z_{in})`. -/
def box (n : ℕ) : Set (Fin n → ℝ) := Set.pi Set.univ (fun _ => Set.Icc 0 1)

/-- The objective of the maximization problem of Appendix A.4, Case 1 (p. 47) for nest `i` at the
point `x` (the page takes `x = β x̂`):
`(v_{i0} + ∑_j v_{ij} z_{ij})^{γ_i} [∑_j r_{ij} v_{ij} z_{ij} / (v_{i0} + ∑_j v_{ij} z_{ij}) − x]`.
At `v_{i0} = 0`, `z = 0` its value is `0 ^ γ_i * (0 / 0 − x) = 0` (`Real.rpow`, `0 / 0 = 0`). -/
noncomputable def F (I : Instance ι n) (i : ι) (z : Fin n → ℝ) (x : ℝ) : ℝ :=
  (I.vnp i + ∑ j, I.v i j * z j) ^ I.γ i *
    ((∑ j, I.r i j * I.v i j * z j) / (I.vnp i + ∑ j, I.v i j * z j) - x)

/-- The objective of problem (31) (Appendix A.4, Case 2, p. 48) for nest `i`, with `a = β x̂` and
`b = β ŷ_i`:
`∑_j r_{ij} v_{ij} z_{ij} − a (v_{i0} + ∑_j v_{ij} z_{ij}) − b (v_{i0} + ∑_j v_{ij} z_{ij})^{1−γ_i}`
(`Real.rpow`; for `γ_i > 1` the exponent is negative, and Lean gives `0 ^ (1 − γ_i) = 0` at a zero
base, which only occurs for `v_{i0} = 0`, `z = 0`). -/
noncomputable def F31 (I : Instance ι n) (i : ι) (z : Fin n → ℝ) (a b : ℝ) : ℝ :=
  ∑ j, I.r i j * I.v i j * z j - a * (I.vnp i + ∑ j, I.v i j * z j) -
    b * (I.vnp i + ∑ j, I.v i j * z j) ^ (1 - I.γ i)

/-- The shape of Lemma 6 (p. 21), used again in Appendix A.4: `z_1 = ⋯ = z_{k−1} = 1`,
`z_k ∈ [0, 1]`, `z_{k+1} = ⋯ = z_n = 0`, for the product `k` (here a `Fin n`, products indexed
from `0`). -/
def IsFracPrefix (z : Fin n → ℝ) (k : Fin n) : Prop :=
  (∀ j, j < k → z j = 1) ∧ z k ∈ Set.Icc 0 1 ∧ ∀ j, k < j → z j = 0

/-- `R_{ik'} = ∑_{j=1}^{k'} r_{ij} v_{ij}` (Appendix A.4, p. 47): the revenue-weighted sum over the
first `k'` products of nest `i`, i.e. over `N_{ik'}`. -/
def Rsum (I : Instance ι n) (i : ι) (k' : ℕ) : ℝ := ∑ j ∈ nbr n k', I.r i j * I.v i j

/-- `q_{ik'} = ∑_{j=1}^{k'} v_{ij}` (Appendix A.4, p. 47): the total weight of the first `k'`
products of nest `i`, i.e. of `N_{ik'}`. -/
def qsum (I : Instance ι n) (i : ι) (k' : ℕ) : ℝ := ∑ j ∈ nbr n k', I.v i j

end NestedLogitVariants.General


