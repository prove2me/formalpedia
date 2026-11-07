-- Prove2me | Definitions.Def_KTCenter_KeyDomains
-- name    : KTCenter_KeyDomains
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:28:18.434946+00:00
-- url     : https://prove2.me/theorems/af039416-8308-425e-a2b9-8b523ad2afac
-- title:
--   Allowed-key sets $P_v$, order indicator $\chi$, pair costs $c_i$, sorted ranking $\sigma_p$ and variable pairs $E_0$
-- statement:
--   Fix nonnegative integer allowances $(w_v)$ and $0<\beta<1$; let $m=\lceil 1/(2\beta)\rceil$ and $K=2m+1$. With $\mathrm{clip}_{[a,b]}(t)=\min\{b,\max\{a,t\}\}$, the **allowed-key set** of candidate $v$ is
--
--   $$P_v=\Bigl\{\mathrm{clip}_{[1,d]}\Bigl(v+\frac{k\,w_v}{m}\Bigr):k=-m,\dots,m\Bigr\},$$
--
--   and $I_v=[\max\{1,v-w_v\},\min\{d,v+w_v\}]$. The **order indicator** $\chi(u,a,v,b)$ is $1$ when $a<b$, or $a=b$ and $u<v$, and $0$ otherwise. For an input $\pi_i$ the **pair cost** is $c_i(u,a,v,b)=\mathbf 1[\chi(u,a,v,b)\ne\mathbf 1[u\prec_{\pi_i}v]]$ for $u\neq v$ and $c_i(v,a,v,b)=0$. A key assignment $p$ gives the ranking $\sigma_p=\mathrm{sort}_\rho(p)$: increasing keys, ties broken by label. A pair $\{u,v\}$ is a **variable pair**, $\{u,v\}\in E_0$, when one allowed choice of keys puts $u$ first and another puts $v$ first. $\mathcal P(V)=\prod_v P_v$ is the set of allowed assignments.
--
--   These finite domains replace positions by sorting keys (Algorithm 2, BuildKeyDomains).
--
--   **Formalization Note** Keys are rationals, and $v$ in the formula is the 1-based label. An assignment is a full vector of keys; since $P_v=\{v\}$ when $w_v=0$, this is the paper's assignment on $U=\{v:w_v>0\}$ extended by $p_v=v$. Sorting is Mathlib's `Tuple.sort`, which breaks ties by index.
-- source:
--   Chakraborty, Das, Mukherjee, Kendall–tau Center Admits a PTAS, STOC 2027 submission (manuscript sha256 4739ffba…), §3 pp.13–14 (PDF pp.15–16), eq. (4), (16), p.22 (PDF p.24), Algorithm 2 p.24 (PDF p.26)

import Mathlib
import Definitions.Def_KTCenter_InversionUnion

namespace KTCenter

/-- `clip_[a,b](t) = min{b, max{a, t}}`, p.14 (PDF p.16). -/
def clip (a b t : ℚ) : ℚ := min b (max a t)

/-- `m = ⌈1/(2β)⌉`, p.22 (PDF p.24). -/
def gridM (β : ℚ) : ℕ := ⌈1 / (2 * β)⌉₊

/-- `K = 2m + 1`, p.22 (PDF p.24). -/
def keyBound (β : ℚ) : ℕ := 2 * gridM β + 1

/-- **Allowed-key set**, eq. (16), p.22 (PDF p.24; Algorithm 2 on p.24):
`P_v = {clip_[1,d](v + k w_v/m) : k = −m, …, m}`.

Chakraborty, Das, Mukherjee, *Kendall–tau Center Admits a PTAS*, STOC 2027 submission (manuscript
sha256 4739ffba…).

**Formalization Note.** `v` in the formula is the 1-based label `lab v`, and `k = t − m` as `t` runs
over `0, …, 2m`. Repeated values occur once, as a `Finset`. -/
def keySet {d : ℕ} (w : Fin d → ℕ) (β : ℚ) (v : Fin d) : Finset ℚ :=
  (Finset.range (2 * gridM β + 1)).image fun t : ℕ =>
    clip 1 d ((lab v : ℚ) + ((t : ℚ) - gridM β) * (w v : ℚ) / (gridM β : ℚ))

lemma keySet_nonempty {d : ℕ} (w : Fin d → ℕ) (β : ℚ) (v : Fin d) : (keySet w β v).Nonempty :=
  Finset.Nonempty.image ⟨0, by simp⟩ _

/-- `I_v = [max{1, v − w_v}, min{d, v + w_v}]`, p.16 and p.22. -/
def keyInterval {d : ℕ} (w : Fin d → ℕ) (v : Fin d) : Set ℚ :=
  Set.Icc (max 1 ((lab v : ℚ) - w v)) (min (d : ℚ) ((lab v : ℚ) + w v))

/-- **Order indicator** `χ(u, a, v, b)`, p.14 (PDF p.16): `1` exactly when `a < b`, or `a = b` and
`u < v`. Lean takes the Boolean value, `true` for `1`. -/
def chi {d : ℕ} (u : Fin d) (a : ℚ) (v : Fin d) (b : ℚ) : Bool :=
  decide (a < b ∨ (a = b ∧ u < v))

/-- **Pair cost**, eq. (4), p.14 (PDF p.16), with `cᵢ(v, a, v, b) = 0`, p.15:
`c(u, a, v, b) = 1[χ(u, a, v, b) ≠ 1[u ≺_π v]]`. -/
def pairCost {d : ℕ} (π : Equiv.Perm (Fin d)) (u : Fin d) (a : ℚ) (v : Fin d) (b : ℚ) : ℕ :=
  if u = v then 0 else if chi u a v b = decide (π⁻¹ u < π⁻¹ v) then 0 else 1

/-- **Sorted ranking** `σ_p = sort_ρ(p)`, p.14 (PDF p.16): increasing key, ties by label.

**Formalization Note.** Mathlib's `Tuple.sort` orders by the pair `(p v, v)` lexicographically, and
`Tuple.sort p j` is the candidate at position `j`, so `u` precedes `v` exactly when `p u < p v`, or
`p u = p v` and `u < v`: ties are broken by the label, that is, by `ρ = (1, …, d)` (p.25). -/
def sortRanking {d : ℕ} (p : Fin d → ℚ) : Equiv.Perm (Fin d) := Tuple.sort p

/-- **Variable pairs** `E₀`, p.15 (PDF p.17) and Algorithm 2, line 28: pairs `(u, v)`, `u < v`, for
which one allowed choice puts `u` before `v` and another puts `v` before `u`. -/
def variablePairs {d : ℕ} (w : Fin d → ℕ) (β : ℚ) : Finset (Fin d × Fin d) :=
  Finset.univ.filter fun p => p.1 < p.2 ∧
    (∃ a ∈ keySet w β p.1, ∃ b ∈ keySet w β p.2, chi p.1 a p.2 b = true) ∧
    (∃ a ∈ keySet w β p.1, ∃ b ∈ keySet w β p.2, chi p.1 a p.2 b = false)

/-- **Allowed assignments** `𝒫(V) = ∏_{v∈V} P_v`, as a finite set of full key vectors.

**Formalization Note.** On p.27 an assignment `p ∈ 𝒫(U)`, `U = {v : w_v > 0}`, is extended by
`p_v = v` outside `U`. Since `P_v = {v}` when `w_v = 0`, those extended assignments are exactly the
full vectors of this set. -/
def assignments {d : ℕ} (w : Fin d → ℕ) (β : ℚ) : Finset (Fin d → ℚ) :=
  Fintype.piFinset (keySet w β)

lemma assignments_nonempty {d : ℕ} (w : Fin d → ℕ) (β : ℚ) : (assignments w β).Nonempty :=
  Fintype.piFinset_nonempty.mpr fun v => keySet_nonempty w β v

end KTCenter


