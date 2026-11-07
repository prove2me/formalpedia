-- Prove2me | Definitions.Def_KTCenter_PartitionCosts
-- name    : KTCenter_PartitionCosts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:29:18.982248+00:00
-- url     : https://prove2.me/theorems/bf5800f9-31fa-45d2-804c-016d32fde28c
-- title:
--   Algorithm 3 (PartitionCosts): bands, blocks $\mathcal B$, constants $A_i$, single-key costs $u_{iv}$, pair costs $q_i$ and surrogate cost $\tilde C_i$
-- statement:
--   Given allowances $(w_v)$, $0<\beta<1$, $0<\zeta<1$ and an input ranking $\pi_i$, Algorithm 3 sets $\alpha=\zeta/9$, $\nu=\lceil\log_2(1/\alpha)\rceil+1$, $L=\lceil 12\nu/\zeta\rceil$, $M=2^L$, $U=\{v:w_v>0\}$, and:
--
--   1. $A_i$ sums $c_i(u,u,v,v)$ over pairs outside $E_0$.
--   2. Each pair of $E_0$ is named $(u,v)$ with $w_u\le w_v$ (smaller label on ties); if $w_u\le\alpha w_v$, then $\min_{a\in P_u}c_i(u,a,v,b)$ is added to $u_{iv}(b)$ and the pair is removed. The remaining pairs form $E^{(1)}$.
--   3. With levels $a_v=\lfloor\log_2 w_v\rfloor$ and band indices $b_o(v)=\lfloor (a_v-o)/L\rfloor$, the smallest $o\in\{0,\dots,L-1\}$ minimizing the number of pairs of $E^{(1)}$ with different indices is selected, and those pairs are removed ($E^{(2)}$).
--   4. In each band $S_j$, with $h_j=2^{o+(j+1)L}$ and $H_j=\lceil 24h_j/\zeta\rceil$, the smallest $e_j\in\{0,\dots,H_j-1\}$ minimizing the number of pairs of $E^{(2)}$ in $S_j$ whose indices $\lfloor (v-e_j)/H_j\rfloor$ differ is selected, those pairs are removed ($E^{(3)}$), and the nonempty sets $B_{j,k}=\{v\in S_j:\lfloor (v-e_j)/H_j\rfloor=k\}$ form $\mathcal B$.
--   5. $q_i(u,a,v,b)=c_i(u,a,v,b)$ if $\{u,v\}\in E^{(3)}$ and $0$ otherwise; $C_0=24M/\zeta+1$, $C_1=3/\alpha$, $\lambda_v=C_1w_v$.
--
--   The **surrogate cost** is
--
--   $$\tilde C_i(p)=A_i+\sum_{v\in U}u_{iv}(p_v)+\sum_{B\in\mathcal B}\sum_{\substack{u,v\in B\\u<v}}q_i(u,p_u,v,p_v).$$
--
--   It approximates $\mathcal K(\sigma_p,\pi_i)$ from below within $\zeta W$ and couples only keys inside one block.
--
--   **Formalization Note** Band and interval indices are integers (floor division with positive divisor), since $j=-1$ and negative numerators occur. Ties in steps 3–4 take the smallest minimizer, as printed. All costs are natural numbers.
-- source:
--   Chakraborty, Das, Mukherjee, Kendall–tau Center Admits a PTAS, STOC 2027 submission (manuscript sha256 4739ffba…), §5.2, eqs. (18)–(25), Algorithm 3, pp.27–31 (PDF pp.29–33)

import Mathlib
import Definitions.Def_KTCenter_Instance
import Definitions.Def_KTCenter_KeyDomains

namespace KTCenter

/-- The smallest minimizer of `f` on `{0, …, N − 1}`: the tie rule "the smallest one minimizing" of
Algorithm 3, lines 14 and 20 (p.31). For `N = 0` the value is `0`; Algorithm 3 has `N ≥ 1` always. -/
def smallestMin (N : ℕ) (f : ℕ → ℕ) : ℕ :=
  ((List.range N).find? fun x => (List.range N).all fun y => decide (f x ≤ f y)).getD 0

namespace PartitionCosts

variable {d : ℕ} (w : Fin d → ℕ) (β ζ : ℚ)

/-- `α = ζ/9`, eq. (18), p.28 (PDF p.30). -/
def alpha (ζ : ℚ) : ℚ := ζ / 9

/-- `ν = ⌈log₂(1/α)⌉ + 1`, eq. (18).

**Formalization Note.** For rational `1/α ≥ 1`, `⌈log₂(1/α)⌉ = Nat.clog 2 ⌈1/α⌉`. -/
def nu (ζ : ℚ) : ℕ := Nat.clog 2 ⌈1 / alpha ζ⌉₊ + 1

/-- `L = ⌈12ν/ζ⌉`, eq. (18). -/
def bandL (ζ : ℚ) : ℕ := ⌈12 * (nu ζ : ℚ) / ζ⌉₊

/-- `M = 2^L`, eq. (18). -/
def bandM (ζ : ℚ) : ℕ := 2 ^ bandL ζ

/-- `C₀ = 24M/ζ + 1`, eq. (25), p.30 (PDF p.32). -/
def constC0 (ζ : ℚ) : ℚ := 24 * (bandM ζ : ℚ) / ζ + 1

/-- `C₁ = 3/α`, eq. (25). -/
def constC1 (ζ : ℚ) : ℚ := 3 / alpha ζ

/-- `λ_v = C₁ w_v`, eq. (25). -/
def lam (v : Fin d) : ℚ := constC1 ζ * (w v : ℚ)

/-- `U = {v ∈ V : w_v > 0}`, p.27 (PDF p.29). -/
def varSet : Finset (Fin d) := Finset.univ.filter fun v => 0 < w v

/-- Algorithm 3, line 8: the pair `(u, v)`, `u < v`, named so that the first component has the
smaller allowance, and the smaller label when the allowances are equal. -/
def named (p : Fin d × Fin d) : Fin d × Fin d :=
  if w p.1 ≤ w p.2 then p else (p.2, p.1)

/-- The replacement test of Algorithm 3, line 9: `w_u ≤ α w_v` for the named pair. -/
def replaced (ζ : ℚ) (p : Fin d × Fin d) : Prop :=
  ((w (named w p).1 : ℕ) : ℚ) ≤ alpha ζ * ((w (named w p).2 : ℕ) : ℚ)

instance (p : Fin d × Fin d) : Decidable (replaced w ζ p) := by
  unfold replaced; infer_instance

/-- `E⁽¹⁾`, p.31–32: the pairs of `E₀` not replaced by single-key costs. -/
def E1 : Finset (Fin d × Fin d) :=
  (variablePairs w β).filter fun p => ¬ replaced w ζ p

/-- The level `a_v = ⌊log₂ w_v⌋`, p.28 (PDF p.30), for `v ∈ U`. -/
def level (v : Fin d) : ℤ := (Nat.log 2 (w v) : ℤ)

/-- The band index `b_o(v) = ⌊(a_v − o)/L⌋`, eq. (20), p.28.

**Formalization Note.** `/` on `ℤ` with positive divisor is the floor; the value may be negative
("The index j = −1 is permitted when a_v < o", p.29). -/
def bandIndex (ζ : ℚ) (o : ℕ) (v : Fin d) : ℤ := (level w v - (o : ℤ)) / (bandL ζ : ℤ)

/-- The selected offset `o`, Algorithm 3, line 14: the smallest minimizer of
`|{{u, v} ∈ E⁽¹⁾ : b_o(u) ≠ b_o(v)}|` on `{0, …, L − 1}`. -/
def offset : ℕ :=
  smallestMin (bandL ζ) fun o =>
    ((E1 w β ζ).filter fun p => bandIndex w ζ o p.1 ≠ bandIndex w ζ o p.2).card

/-- `b(v) = b_o(v)` for the selected `o`, Algorithm 3, line 16. -/
def band (v : Fin d) : ℤ := bandIndex w ζ (offset w β ζ) v

/-- `E⁽²⁾`, p.32: pairs of `E⁽¹⁾` with equal selected band index. -/
def E2 : Finset (Fin d × Fin d) :=
  (E1 w β ζ).filter fun p => band w β ζ p.1 = band w β ζ p.2

/-- `h_j = 2^{o+(j+1)L}`, eq. (21), p.29 (PDF p.31).

**Formalization Note.** For a nonempty band `j ≥ −1`, so the exponent is a nonnegative integer and
`toNat` does not truncate. -/
def bandH (j : ℤ) : ℕ := 2 ^ (((offset w β ζ : ℤ) + (j + 1) * (bandL ζ : ℤ)).toNat)

/-- `H_j = ⌈24 h_j/ζ⌉`, eq. (21). -/
def widthH (j : ℤ) : ℕ := ⌈24 * (bandH w β ζ j : ℚ) / ζ⌉₊

/-- The interval index `⌊(v − e)/H⌋` of the label `v`, p.29. -/
def intervalIndex (H e : ℕ) (v : Fin d) : ℤ := (lab v - (e : ℤ)) / (H : ℤ)

/-- The selected shift `e_j`, Algorithm 3, line 20: the smallest minimizer on `{0, …, H_j − 1}` of
the number of pairs of `E⁽²⁾` inside `S_j` whose interval indices differ. -/
def shift (j : ℤ) : ℕ :=
  smallestMin (widthH w β ζ j) fun e =>
    ((E2 w β ζ).filter fun p => band w β ζ p.1 = j ∧
      intervalIndex (widthH w β ζ j) e p.1 ≠ intervalIndex (widthH w β ζ j) e p.2).card

/-- The selected interval index of `v`, `⌊(v − e_j)/H_j⌋` with `j = b(v)`, eq. (22). -/
def cell (v : Fin d) : ℤ :=
  intervalIndex (widthH w β ζ (band w β ζ v)) (shift w β ζ (band w β ζ v)) v

/-- `E⁽³⁾`, p.32: pairs of `E⁽²⁾` with equal selected interval index. -/
def E3 : Finset (Fin d × Fin d) :=
  (E2 w β ζ).filter fun p => cell w β ζ p.1 = cell w β ζ p.2

/-- The family `ℬ` of the nonempty sets `B_{j,k}`, eq. (22), p.29. -/
def blocks : Finset (Finset (Fin d)) :=
  (varSet w).image fun v =>
    (varSet w).filter fun u => band w β ζ u = band w β ζ v ∧ cell w β ζ u = cell w β ζ v

/-- The constant `Aᵢ`, Algorithm 3, lines 4–5: the sum over pairs outside `E₀` of
`cᵢ(u, u, v, v)`, with keys the labels. -/
def constA (ρ : Equiv.Perm (Fin d)) : ℕ :=
  ∑ p ∈ (Finset.univ.filter fun p : Fin d × Fin d => p.1 < p.2) \ variablePairs w β,
    pairCost ρ p.1 (lab p.1 : ℚ) p.2 (lab p.2 : ℚ)

/-- The single-key cost `uᵢᵥ(b)`, Algorithm 3, lines 7–12 and eq. (19): the sum over replaced pairs
named `(u, v)` of `min_{a∈P_u} cᵢ(u, a, v, b)`. -/
def singleKey (ρ : Equiv.Perm (Fin d)) (v : Fin d) (b : ℚ) : ℕ :=
  ∑ p ∈ ((variablePairs w β).filter fun p => replaced w ζ p ∧ (named w p).2 = v),
    (keySet w β (named w p).1).inf' (keySet_nonempty w β _) fun a =>
      pairCost ρ (named w p).1 a v b

/-- The retained pair cost `qᵢ(u, a, v, b)`, eq. (23), p.30 (PDF p.32): `cᵢ(u, a, v, b)` when
`{u, v} ∈ E⁽³⁾`, else `0`.

**Formalization Note.** `E⁽³⁾` holds `(u, v)` with `u < v`, so `{u, v}` is looked up as
`(min u v, max u v)`; this makes `q` symmetric and zero on a repeated candidate. -/
def pairQ (ρ : Equiv.Perm (Fin d)) (u : Fin d) (a : ℚ) (v : Fin d) (b : ℚ) : ℕ :=
  if (min u v, max u v) ∈ E3 w β ζ then pairCost ρ u a v b else 0

/-- **Surrogate cost**, eq. (24), p.30 (PDF p.32):
`C̃ᵢ(p) = Aᵢ + Σ_{v∈U} uᵢᵥ(p_v) + Σ_{B∈ℬ} Σ_{u<v in B} qᵢ(u, p_u, v, p_v)`.

Chakraborty, Das, Mukherjee, *Kendall–tau Center Admits a PTAS*, STOC 2027 submission (manuscript
sha256 4739ffba…), Algorithm 3, p.31.

**Formalization Note.** `p` is a full key vector, and only its values on `U` are used. All values
are natural numbers, since the costs are `0` or `1`. The parameters `β` and `ζ` are arguments,
and the input is the single ranking `ρ = πᵢ`. -/
def surrogate (ρ : Equiv.Perm (Fin d)) (p : Fin d → ℚ) : ℕ :=
  constA w β ρ + ∑ v ∈ varSet w, singleKey w β ζ ρ v (p v) +
    ∑ B ∈ blocks w β ζ, ∑ x ∈ (B ×ˢ B).filter (fun x => x.1 < x.2),
      pairQ w β ζ ρ x.1 (p x.1) x.2 (p x.2)

/-- `max_{i∈[n]} C̃ᵢ(p)`, p.56. -/
def maxSurrogate (I : Instance) (w : Fin I.d → ℕ) (β ζ : ℚ) (p : Fin I.d → ℚ) : ℕ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => surrogate w β ζ (I.π i) p

/-- `min_{p∈𝒫(U)} max_{i∈[n]} C̃ᵢ(p)`, eq. (72), p.56. -/
def minMaxSurrogate (I : Instance) (w : Fin I.d → ℕ) (β ζ : ℚ) : ℕ :=
  (assignments w β).inf' (assignments_nonempty w β) (maxSurrogate I w β ζ)

end PartitionCosts

end KTCenter


