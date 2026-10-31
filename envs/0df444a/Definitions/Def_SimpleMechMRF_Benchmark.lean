-- Prove2me | Definitions.Def_SimpleMechMRF_Benchmark
-- name    : SimpleMechMRF_Benchmark
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:13:25.656747+00:00
-- url     : https://prove2.me/theorems/fa48df39-2b27-4e54-a080-2951f435f70c
-- title:
--   Favourite regions $R_i$, ironed conditional virtual values $\varphi_i(t_i\mid t_{-i})$, Single, Non-Favorite, Tail, Core, $C_i$
-- statement:
--   Fix a finite type distribution $D$.
--
--   1. **Favourite regions** (Definition 6). $R_i$ is the set of types for which $i$ is the smallest index in $\arg\max_{i'}t_{i'}$: $t_j\le t_i$ for all $j$ and $t_j<t_i$ for $j<i$.
--   2. **Ironed conditional virtual value** (Definition 7). Fix $i$ and $t_{-i}$, let $S=\{s:(s,t_{-i})\in T\cap R_i\}$ and $q(s)=\Pr[t_i\ge s\wedge t\in R_i\mid t_{-i}]$. The ironed revenue curve $\bar R$ is the least concave majorant of the points $(0,0)$ and $(q(s),\,s\,q(s))$, $s\in S$. For $t\in R_i$,
--   $$
--   \varphi_i(t_i\mid t_{-i})=\frac{\bar R\big(q(t_i)\big)-\bar R\big(q(t_i)-f_i(t_i\mid t_{-i})\big)}{f_i(t_i\mid t_{-i})},
--   $$
--   the slope of the ironed curve on the quantile interval of $t_i$. Without ironing it is the paper's $t_i-(t_i'-t_i)\,\Pr[t_i>t_i\mid t_{-i}]/f_i(t_i\mid t_{-i})$ ($t_i'$ the next support point).
--   3. For a mechanism $M$ and a cutoff $r$:
--   $$
--   \textsc{Single}=\sum_{t\in T}\sum_i f(t)\pi_i(t)\varphi_i(t_i\mid t_{-i})\mathbb 1[t\in R_i],\qquad \textsc{Non-Favorite}=\sum_{t\in T}\sum_i f(t)\pi_i(t)\,t_i\,\mathbb 1[t\notin R_i],
--   $$
--   $$
--   \textsc{Tail}(r)=\sum_i\sum_{t_i>r}f_i(t_i)\,t_i\Pr_{t'\sim D}[t'\notin R_i\mid t_i'=t_i],\qquad \textsc{Core}(r)=\sum_i\sum_{t_i\le r}f_i(t_i)\,t_i .
--   $$
--   4. $C_i=t_i\cdot\mathbb 1[t_i\le r]$ and $C=\sum_i C_i$ (§4.3).
--
--   These are the terms of the Cai–Devanur–Weinberg duality benchmark $\mathrm{Rev}\le\textsc{Single}+\textsc{Tail}+\textsc{Core}$ used for the additive buyer.
--
--   **Formalization Note** $\varphi_i$ is evaluated only for $t\in T\cap R_i$; every statement multiplies it by $\mathbb 1[t\in R_i]$. The concave majorant is the supremum of convex combinations of the curve's points with the given abscissa. Ironing is over the values of the conditional support lying in $R_i$ (the paper's interval $[\max_{j\ne i}t_j,\max\mathrm{Supp}(D_{i\mid t_{-i}})]$ restricted to $R_i$).
-- source:
--   Cai & Oikonomou, On Simple Mechanisms for Dependent Items, arXiv:2106.10814v2, Definition 6 and Definition 7, p.10 (PDF 11); Lemma 4, p.11 (PDF 12); C_i, §4.3, p.12 (PDF 13)

import Mathlib
import Definitions.Def_SimpleMechMRF_TypeDist
import Definitions.Def_SimpleMechMRF_Mechanism

open scoped NNReal

namespace SimpleMechMRF

variable {n : ℕ}

/-- **Favourite region** `Rᵢ`: item `i` is the smallest index in `argmax_{i'} t_{i'}`, i.e.
`t j ≤ t i` for all `j` and `t j < t i` for all `j < i` (Definition 6, p. 10, PDF 11). The
paper's `Rᵢ = {t ∈ T : …}`; membership in `T` is imposed separately wherever it matters. -/
def Favorite (i : Fin n) (t : Fin n → ℝ≥0) : Prop :=
  (∀ j, t j ≤ t i) ∧ ∀ j, j < i → t j < t i

/-- `max_{j≠i} t_j`, in `ℝ≥0` (it is `0` when there is no `j ≠ i`). -/
noncomputable def othersMax (i : Fin n) (t : Fin n → ℝ≥0) : ℝ≥0 :=
  (Finset.univ.filter (fun j => j ≠ i)).sup t

namespace TypeDist

variable (D : TypeDist n)

/-- The values `s` with `(s, t₋ᵢ) ∈ Rᵢ` (and `(s, t₋ᵢ) ∈ T`): the part of the support of
`D_{i|t₋ᵢ}` on which item `i` is the favourite. -/
noncomputable def regionVals (i : Fin n) (t : Fin n → ℝ≥0) : Finset ℝ≥0 := by
  classical
  exact (D.supp.filter (fun u => SameOthers i t u ∧ Favorite i u)).image (fun u => u i)

/-- `q(s) = Pr[tᵢ ≥ s ∧ (tᵢ, t₋ᵢ) ∈ Rᵢ | t₋ᵢ]`, the conditional sale probability at price `s`
within the favourite region. -/
noncomputable def regionTail (i : Fin n) (t : Fin n → ℝ≥0) (s : ℝ≥0) : ℝ :=
  D.condProb i t {u | s ≤ u i ∧ Favorite i u}

/-- **Ironed conditional revenue curve.** The least concave majorant, on the quantile axis, of
the points `(0, 0)` and `(q(s), s · q(s))` for `s` in `regionVals D i t`: the best convex
combination of these points with first coordinate `x`. -/
noncomputable def ironedRevenue (i : Fin n) (t : Fin n → ℝ≥0) (x : ℝ) : ℝ :=
  sSup {y : ℝ | ∃ a : Option ℝ≥0 → ℝ,
    (∀ o, 0 ≤ a o) ∧
    a none + ∑ s ∈ D.regionVals i t, a (some s) = 1 ∧
    ∑ s ∈ D.regionVals i t, a (some s) * D.regionTail i t s = x ∧
    y = ∑ s ∈ D.regionVals i t, a (some s) * ((s : ℝ) * D.regionTail i t s)}

/-- **Ironed conditional virtual value** `φᵢ(tᵢ | t₋ᵢ)` (Definition 7, p. 10, PDF 11): Myerson's
ironed virtual value of `D_{i|t₋ᵢ}`, ironed over the favourite region
`{s : (s, t₋ᵢ) ∈ Rᵢ}` (the paper's interval `[max_{j≠i} t_j, max Supp(D_{i|t₋ᵢ})]`). It is the
slope of the ironed revenue curve on the quantile interval `[q(tᵢ) − fᵢ(tᵢ | t₋ᵢ), q(tᵢ)]` of
mass `fᵢ(tᵢ | t₋ᵢ)`.

**Formalization Note.** Used only for `t ∈ T ∩ Rᵢ` (the paper: "For any t ∈ Ri"); every
statement multiplies it by `1[t ∈ Rᵢ]`. When no ironing occurs it equals the paper's regular
formula `tᵢ − (t'ᵢ − tᵢ)(1 − Fᵢ(tᵢ | t₋ᵢ)) / fᵢ(tᵢ | t₋ᵢ)` (`t'ᵢ` the next support point), and
`tᵢ` at the top of the support. -/
noncomputable def phi (i : Fin n) (t : Fin n → ℝ≥0) : ℝ :=
  (D.ironedRevenue i t (D.regionTail i t (t i)) -
      D.ironedRevenue i t (D.regionTail i t (t i) - D.cond i t)) / D.cond i t

/-- **Single** `= Σ_{t∈T} Σ_{i∈[n]} f(t) · πᵢ(t) · φᵢ(tᵢ | t₋ᵢ) · 1[t ∈ Rᵢ]` (Lemma 4, p. 11). -/
noncomputable def single (I : Finset (Finset (Fin n))) (M : Mechanism n) : ℝ := by
  classical
  exact ∑ t ∈ D.supp, ∑ i, D.pmf t * M.alloc I i t * D.phi i t * (if Favorite i t then 1 else 0)

/-- **Non-Favorite** `= Σ_{t∈T} Σ_{i∈[n]} f(t) · πᵢ(t) · tᵢ · 1[t ∉ Rᵢ]` (Lemma 4, p. 11). -/
noncomputable def nonFavorite (I : Finset (Finset (Fin n))) (M : Mechanism n) : ℝ := by
  classical
  exact ∑ t ∈ D.supp, ∑ i, D.pmf t * M.alloc I i t * (t i : ℝ) * (if Favorite i t then 0 else 1)

/-- **Tail** `= Σ_{i∈[n]} Σ_{tᵢ ∈ Tᵢ, tᵢ > r} fᵢ(tᵢ) · tᵢ · Pr_{t'∼D}[t' ∉ Rᵢ | t'ᵢ = tᵢ]`
(Lemma 4, p. 11). -/
noncomputable def tail (r : ℝ) : ℝ := by
  classical
  exact ∑ i, ∑ s ∈ (D.suppMarg i).filter (fun s : ℝ≥0 => r < (s : ℝ)),
    D.marg i s * (s : ℝ) * D.condOnItem i s {u | ¬ Favorite i u}

/-- **Core** `= Σ_{i∈[n]} Σ_{tᵢ ∈ Tᵢ, tᵢ ≤ r} fᵢ(tᵢ) · tᵢ` (Lemma 4, p. 11). -/
noncomputable def core (r : ℝ) : ℝ := by
  classical
  exact ∑ i, ∑ s ∈ (D.suppMarg i).filter (fun s : ℝ≥0 => (s : ℝ) ≤ r), D.marg i s * (s : ℝ)

end TypeDist

/-- `Cᵢ = tᵢ · 1[tᵢ ≤ r]` (p. 12, PDF 13). -/
noncomputable def truncVal (r : ℝ) (i : Fin n) (t : Fin n → ℝ≥0) : ℝ := by
  classical
  exact if (t i : ℝ) ≤ r then (t i : ℝ) else 0

/-- `C = Σ_{i=1}^n Cᵢ` (p. 12, PDF 13). -/
noncomputable def truncSum (r : ℝ) (t : Fin n → ℝ≥0) : ℝ :=
  ∑ i, truncVal r i t

end SimpleMechMRF


