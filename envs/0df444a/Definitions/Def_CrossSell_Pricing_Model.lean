-- Prove2me | Definitions.Def_CrossSell_Pricing_Model
-- name    : CrossSell_Pricing_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:28:33.744264+00:00
-- url     : https://prove2.me/theorems/c82ebdcf-58bf-4763-b50c-15f1588950ea
-- title:
--   §2–§3, pp. 8–12 — sequential MNL: choice probabilities (1), (3), profit (5), t_i and the aggregate markup (Definition 1), H(r; z) and H(z) (Theorem 1)
-- statement:
--   This file sets up the **sequential (two-stage) multinomial logit model** of cross-category retailing of Ke and Wang.
--
--   A firm sells **main products**, indexed by a type $\mathcal M$, and **secondary products**, indexed by a finite type $\mathcal N$. It offers a finite set $S \subseteq \mathcal M$ of main products and writes $S^+ := S \cup \{0\}$, where $0$ is the no-purchase option of the first stage. To every $i \in S^+$ is attached a set $T_i \subseteq \mathcal N$ of secondary products (the sets may be disjoint, overlap, coincide or be empty); $T_0$ is the set offered to a consumer who bought no main product. The data are the intrinsic utilities $u_i$ and marginal costs $c_i$ of the main products, the marginal costs $s_l$ of the secondary products, and the intrinsic utility $v_{il}$ of secondary product $l$ after the first-stage outcome $i \in S^+$. The decision variables are the main prices $\mathbf p = (p_i)$ and the secondary prices $\mathbf r = (r_l)$; a secondary product has one price whatever main product it follows.
--
--   1. **Stage-1 choice probabilities**, eq. (1): for $i \in S$,
--   $$d_i(S,\mathbf p) = \frac{\exp(u_i - p_i)}{1 + \sum_{j\in S}\exp(u_j - p_j)}, \qquad d_0(S,\mathbf p) = 1 - \sum_{i\in S} d_i(S,\mathbf p) = \frac{1}{1 + \sum_{j\in S}\exp(u_j - p_j)}.$$
--   2. **Stage-2 choice probabilities**, eq. (3): for $i \in S^+$ and $l \in T_i$,
--   $$q_{l|i}(T_i,\mathbf r) = \frac{\exp(v_{il} - r_l)}{1 + \sum_{k\in T_i}\exp(v_{ik} - r_k)}.$$
--   3. **Secondary profit**, Definition 1: $t_i(\mathbf r) = \sum_{l\in T_i}(r_l - s_l)\,q_{l|i}(T_i,\mathbf r)$ for $i \in S^+$.
--   4. **Total expected profit**, eq. (5):
--   $$\Pi(S,\mathbf T,\mathbf p,\mathbf r) = \sum_{i\in S}(p_i - c_i)\,d_i(S,\mathbf p) + \sum_{i\in S^+}\sum_{l\in T_i}(r_l - s_l)\,d_i(S,\mathbf p)\,q_{l|i}(T_i,\mathbf r).$$
--   5. **Aggregate markup**, Definition 1: $p_i - c_i + t_i(\mathbf r)$ for $i \in S$.
--   6. **The functions of Theorem 1**:
--   $$H(\mathbf r; z) = \sum_{i\in S}\exp\big((u_i - c_i - 1 - z) + t_i(\mathbf r)\big) + t_0(\mathbf r), \qquad H(z) = \sup_{\mathbf r} H(\mathbf r; z).$$
--
--   These objects are shared by every statement of the mission: the pricing problem maximizes $\Pi$ over $(\mathbf p, \mathbf r)$, and Theorem 1 reduces it to the scalar fixed-point equation $z = H(z)$.
--
--   **Formalization Note.** $S^+$ is `Finset.insertNone S` in `Option ι`, with `none` the no-purchase option $0$; `mainMargin` encodes $p_i - c_i$ on $S^+$ with $p_0 - c_0 = 0$ (eq. (6)). The Gumbel derivation of (1) and (3) is not formalized: the closed forms are the model, with scale $\mu = 1$ as in the paper and no-purchase utilities normalized to $0$. The paper's factorization $v_{il} = \beta_{il} v_l$ is not imposed: $v_{il}$ is a free real, which is the same generality (take $v_l = 1$); the paper's device $\beta_{0l} v_l = -\infty$ (p. 10) corresponds to $T_0 = \emptyset$. Prices are unconstrained reals, as on the page. Every denominator is $1$ plus a sum of exponentials, hence positive. The paper writes $H(z) := \max_{\mathbf r} H(\mathbf r; z)$; here it is the real supremum `⨆ r`, and every statement using it also asserts that the range is bounded above, so the supremum is never the junk value of an unbounded set.
-- source:
--   Ke & Wang, Cross-Category Retailing Management: Substitution and Complementarity, accepted manuscript (SSRN 3383023), pp. 8–12, eqs. (1), (3), (5), (6), Definition 1, Theorem 1

import Mathlib

namespace CrossSell.Pricing
open Finset

variable {ι κ : Type*}

/-- Stage-1 denominator `1 + Σ_{j∈S} exp(u_j − p_j)` of eq. (1). -/
noncomputable def mainDenom (S : Finset ι) (u p : ι → ℝ) : ℝ :=
  1 + ∑ j ∈ S, Real.exp (u j - p j)

/-- `d_i(S, p)` of eq. (1) on `S+ = S ∪ {0}`, encoded in `Option ι`: `none` is the no-purchase
option `0`, with `d_0 = 1 − Σ_{i∈S} d_i = 1 / (1 + Σ_{j∈S} exp(u_j − p_j))`. -/
noncomputable def mainProb (S : Finset ι) (u p : ι → ℝ) : Option ι → ℝ
  | none => 1 / mainDenom S u p
  | some i => Real.exp (u i - p i) / mainDenom S u p

/-- The stage-1 margin `p_i − c_i` on `S+`, with `p_0 − c_0 = 0` (eq. (6)). -/
def mainMargin (c p : ι → ℝ) : Option ι → ℝ
  | none => 0
  | some i => p i - c i

/-- `q_{l|i}(T_i, r)` of eq. (3). -/
noncomputable def secProb (T : Option ι → Finset κ) (v : Option ι → κ → ℝ) (r : κ → ℝ)
    (i : Option ι) (l : κ) : ℝ :=
  Real.exp (v i l - r l) / (1 + ∑ k ∈ T i, Real.exp (v i k - r k))

/-- `t_i` of Definition 1: the profit collected from the secondary set `T_i`, for `i ∈ S+`. -/
noncomputable def secProfit (T : Option ι → Finset κ) (s : κ → ℝ) (v : Option ι → κ → ℝ)
    (r : κ → ℝ) (i : Option ι) : ℝ :=
  ∑ l ∈ T i, (r l - s l) * secProb T v r i l

/-- The total expected profit `Π(S, T, p, r)` of eq. (5). -/
noncomputable def profit (S : Finset ι) (T : Option ι → Finset κ) (u c : ι → ℝ) (s : κ → ℝ)
    (v : Option ι → κ → ℝ) (p : ι → ℝ) (r : κ → ℝ) : ℝ :=
  (∑ i ∈ S, (p i - c i) * mainProb S u p (some i)) +
    ∑ i ∈ S.insertNone, ∑ l ∈ T i, (r l - s l) * mainProb S u p i * secProb T v r i l

/-- The aggregate markup `p_i − c_i + t_i` of Definition 1. -/
noncomputable def aggMarkup (T : Option ι → Finset κ) (c : ι → ℝ) (s : κ → ℝ)
    (v : Option ι → κ → ℝ) (p : ι → ℝ) (r : κ → ℝ) (i : ι) : ℝ :=
  p i - c i + secProfit T s v r (some i)

/-- `H(r; z)` of Theorem 1. -/
noncomputable def Hr (S : Finset ι) (T : Option ι → Finset κ) (u c : ι → ℝ) (s : κ → ℝ)
    (v : Option ι → κ → ℝ) (r : κ → ℝ) (z : ℝ) : ℝ :=
  (∑ i ∈ S, Real.exp ((u i - c i - 1 - z) + secProfit T s v r (some i))) +
    secProfit T s v r none

/-- `H(z) := max_r H(r; z)` of Theorem 1, as a real supremum over all secondary price vectors.
Every statement that uses it also asserts that the range is bounded above. -/
noncomputable def Hmax (S : Finset ι) (T : Option ι → Finset κ) (u c : ι → ℝ) (s : κ → ℝ)
    (v : Option ι → κ → ℝ) (z : ℝ) : ℝ :=
  ⨆ r : κ → ℝ, Hr S T u c s v r z

end CrossSell.Pricing


